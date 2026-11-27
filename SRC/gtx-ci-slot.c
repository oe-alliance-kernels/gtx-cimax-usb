// SPDX-License-Identifier: GPL-2.0-or-later
/* EN 50221 link/transport for the single wired CIMaX+ slot.
 * Enigma2 owns all session protocols above this interface.
 */
#include <linux/delay.h>
#include <linux/fs.h>
#include <linux/kref.h>
#include <linux/miscdevice.h>
#include <linux/module.h>
#include <linux/poll.h>
#include <linux/proc_fs.h>
#include <linux/skbuff.h>
#include <linux/usb.h>
#include <linux/workqueue.h>
#include <asm/unaligned.h>
#include "cimax+usb-driver.h"

#define CI_SPDU 4096 /* Enigma2's read buffer */
#define CI_LINK 512
#define CI_WIRE (CI_SPDU + 12)
#define CI_QUEUE 16

enum cam_command { CAM_RESET = 1, CAM_CIS, CAM_COR, CAM_NEG, CAM_WRITE, CAM_READ, CAM_STATUS = 14 };
enum transport_tag {
	T_SB = 0x80, T_RCV, T_CREATE, T_CREATED, T_DELETE, T_DELETED,
	T_DATA_LAST = 0xa0, T_DATA_MORE
};
/* Only the transport and router registers used by the board's USB profile. */
static const struct { u16 addr; u8 value; } pvr_regs[] = {
	{ 0x0e13, 0x3f }, { 0x0e12, 0x7f }, /* endpoint DMA and enable */
	{ 0x0221, 0x0f }, { 0x0224, 0x0f }, /* TS FIFOs */
	{ 0x0222, 0x80 }, { 0x0223, 0x80 }, /* USB to TS pacing */
	{ 0x0234, 0x0c }, { 0x0235, 0x0c }, /* gap removers */
};

enum slot_state { EMPTY, RESET, CIS, CONFIGURE, NEGOTIATE, CONNECT, RUNNING };

struct gtx_ci {
	struct kref ref;
	struct device_s *usb;
	struct miscdevice node, pvr_node;
	bool pvr_open, pvr_started;
	u8 pvr_saved[ARRAY_SIZE(pvr_regs)];
	u8 pvr_input, pvr_output;
	struct proc_dir_entry *mux;
	struct delayed_work work;
	struct mutex lock;
	wait_queue_head_t wait;
	struct sk_buff_head rx, tx;
	enum slot_state state;
	bool opened, present, contact_b, power_pending, waiting, receive;
	atomic_t remove_event;
	enum { DIRECT, TUNER_A, TUNER_B, FILE_INPUT } route, pending_route, ci_source;
	unsigned long check_contact, deadline;
	u16 base, link_size;
	u8 option;
	char version[256];
	u8 *wire, *reply, *tpdu, *spdu;
	unsigned int tpdu_len, spdu_len;
	int last_error;
};

static const u8 cmd_reply[] = {
	[CAM_RESET] = 0x40, [CAM_CIS] = 0x41, [CAM_COR] = 0x42,
	[CAM_NEG] = 0x43, [CAM_WRITE] = 0x44, [CAM_READ] = 0x46, [CAM_STATUS] = 0x57,
};

/* Caller owns the transport driver's mutex. The device sends a response
 * header only in the first interrupt packet; subsequent packets are payload.
 */
static int exchange(struct gtx_ci *ci, const u8 *cmd, size_t count, u8 tag)
{
	struct usb_device *dev = ci->usb->usbdev;
	const bool reg = tag == 0x4c || tag == 0x4d;
	int actual, ret, total = 0, expected = 0, attempts;
	bool matched = false;
	size_t sent = 0;
	int pipe = usb_rcvintpipe(dev, 5);
	unsigned int packet = usb_maxpacket(dev, pipe, 0);
	unsigned int timeout = !reg && (cmd[0] == CAM_RESET || cmd[0] == CAM_CIS ||
					cmd[0] == CAM_NEG) ? 8000 : 1000;
	unsigned long deadline = jiffies + msecs_to_jiffies(timeout);
	u8 last_tag = 0;

	if (!packet || packet > 512 || count > CI_WIRE)
		return -EINVAL;
	/* The firmware consumes 256-byte CI command blocks, even when EP6
	 * advertises a 512-byte USB maximum packet size. */
	while (sent < count) {
		size_t chunk = min_t(size_t, count - sent, DEVICE_BULK_OUT_MAXPACKET);
		ret = usb_bulk_msg(dev, usb_sndbulkpipe(dev, 6), (void *)(cmd + sent),
				   chunk, &actual, 500);
		if (ret || actual != chunk)
			return ret ?: -EIO;
		sent += actual;
	}
	/* Hot removal can leave one previous reply or an event in EP5. The
	 * firmware also packs several messages into one interrupt transaction.
	 * Drain whole messages and match the reply to this command. */
	for (attempts = 0; attempts < 64; attempts++) {
		u8 *p = ci->reply + CI_WIRE;
		int left;

		if (time_after_eq(jiffies, deadline))
			return -ETIMEDOUT;
		ret = usb_interrupt_msg(dev, pipe, p, packet, &actual,
					max_t(unsigned int, 1, jiffies_to_msecs(deadline - jiffies)));
		if (ret) {
			dev_warn_ratelimited(&dev->dev, "CI command %02x reply %02x, %d/%d bytes, error %d\n",
					     cmd[0], last_tag, total, expected, ret);
			return ret;
		}
		left = actual;
		while (left) {
			int take;

			if (!expected) {
				u8 response;
				bool register_reply;

				if (left < 4)
					break;
				last_tag = p[0];
				response = p[0] & 0x7f;
				if (!p[0] && !p[1] && !p[2] && !p[3])
					break;
				if (!reg && p[0] == response && p[1] == 1) {
					if (response == 0x54 || response == 0x56)
						return -EAGAIN;
					if (response == 0x49)
						return -ENODEV;
					if (response == 0x4a)
						return -EIO;
				}
				register_reply = response == 0x4c || response == 0x4d;
				expected = 4 + (register_reply ? p[3] : get_unaligned_be16(p + 2));
				if (expected > CI_WIRE)
					return -EMSGSIZE;
				matched = p[0] == tag && (reg ?
					!memcmp(p + 1, cmd + 1, 2) : p[1] == 1);
				total = 0;
			}
			take = min(left, expected - total);
			if (matched)
				memcpy(ci->reply + total, p, take);
			total += take;
			left -= take;
			p += take;
			if (total == expected) {
				if (matched)
					return total - 4;
				expected = 0;
			}
		}
	}
	return -ETIMEDOUT;
}

static int command(struct gtx_ci *ci, enum cam_command cmd, const u8 *payload, size_t len)
{
	u8 *w = ci->wire;
	if (len > CI_WIRE - 4)
		return -EMSGSIZE;
	w[0] = cmd;
	w[1] = 1;
	put_unaligned_be16(len, w + 2);
	if (len)
		memcpy(w + 4, payload, len);
	return exchange(ci, w, len + 4, cmd_reply[cmd]);
}

static int reg_io(struct gtx_ci *ci, unsigned int reg, int value)
{
	u8 *w = ci->wire;
	int ret;
	w[0] = value < 0 ? 0xff : 0x7f;
	put_unaligned_be16(reg, w + 1);
	w[3] = 1;
	w[4] = value;
	ret = exchange(ci, w, value < 0 ? 4 : 5, value < 0 ? 0x4c : 0x4d);
	if (ret < 0)
		return ret;
	if (value < 0)
		return ret == 1 ? ci->reply[4] : -EPROTO;
	return ret == 0 ? 0 : -EPROTO;
}

/* Called with both CI locks held. TS returns on the physical parallel
 * connection to SM1 TS1. EP5/6 remain owned by the active CI session. */
static int stop_pvr(struct gtx_ci *ci)
{
	int i, err, first = 0;

	if (!ci->pvr_started)
		return 0;
	err = reg_io(ci, 0x022d, ci->pvr_input);
	if (err)
		first = err;
	err = reg_io(ci, 0x022e, ci->pvr_output);
	if (err && !first)
		first = err;
	for (i = ARRAY_SIZE(pvr_regs) - 1; i >= 0; i--) {
		err = reg_io(ci, pvr_regs[i].addr, ci->pvr_saved[i]);
		if (err && !first)
			first = err;
	}
	err = usb_set_interface(ci->usb->usbdev, 0, 1);
	if (!first)
		first = err;
	if (!first)
		ci->pvr_started = false;
	return first;
}

static int start_pvr(struct gtx_ci *ci)
{
	struct usb_device *dev = ci->usb->usbdev;
	int i, value, err;

	value = reg_io(ci, 0x022d, -1);
	if (value < 0)
		return value;
	ci->pvr_input = value;
	value = reg_io(ci, 0x022e, -1);
	if (value < 0)
		return value;
	ci->pvr_output = value;
	for (i = 0; i < ARRAY_SIZE(pvr_regs); i++) {
		value = reg_io(ci, pvr_regs[i].addr, -1);
		if (value < 0)
			return value;
		ci->pvr_saved[i] = value;
	}
	err = usb_set_interface(dev, 0, 2);
	if (err)
		return err;
	ci->pvr_started = true;
	if (!dev->ep_out[3] || !usb_endpoint_is_bulk_out(&dev->ep_out[3]->desc))
		return -ENODEV;
	/* Start with empty TS FIFOs as in the firmware USB transport profile. */
	err = reg_io(ci, 0x022d, 0);
	if (!err)
		err = reg_io(ci, 0x022e, 0);
	if (!err)
		err = reg_io(ci, 0x0231, 0x0f);
	if (!err)
		err = reg_io(ci, 0x0236, 0x0f);
	for (i = 0; !err && i < ARRAY_SIZE(pvr_regs); i++)
		err = reg_io(ci, pvr_regs[i].addr, pvr_regs[i].value);
	if (!err)
		err = reg_io(ci, 0x022e, ci->pvr_output);
	if (!err)
		err = reg_io(ci, 0x022d, (ci->pvr_input & 0xf0) | 2);
	return err;
}

static int set_route(struct gtx_ci *ci, int route)
{
	/* CH1 is the Sony (E2 A); CH0 is the Montage (E2 B).
	 * The unused input stays direct while the other passes through CAM A. */
	static const u8 routes[][2] = {
		[DIRECT] = { 0x21, 0x00 },
		[TUNER_A] = { 0x51, 0x02 },
		[TUNER_B] = { 0x20, 0x01 },
		[FILE_INPUT] = { 0x20, 0x01 },
	};
	u8 *cmd = ci->wire;
	int ret;

	if (route != FILE_INPUT && ci->pvr_started) {
		ret = stop_pvr(ci);
		if (ret)
			return ret;
	}
	cmd[0] = 0x7f;
	put_unaligned_be16(0x022f, cmd + 1);
	cmd[3] = 2;
	memcpy(cmd + 4, routes[route], 2);
	ret = exchange(ci, cmd, 6, 0x4d);
	if (ret)
		return ret < 0 ? ret : -EPROTO;
	cmd[0] = 0xff;
	ret = exchange(ci, cmd, 4, 0x4c);
	if (ret != 2 || memcmp(ci->reply + 4, routes[route], 2))
		return ret < 0 ? ret : -EIO;
	ci->route = route;
	return 0;
}

static bool contains(const u8 *p, size_t n, const char *s)
{
	size_t len = strlen(s), i;
	for (i = 0; i + len <= n; i++)
		if (!memcmp(p + i, s, len))
			return true;
	return false;
}

static int parse_cis(struct gtx_ci *ci, const u8 *p, size_t n)
{
	bool config = false, entry = false;
	size_t pos = 0;
	ci->version[0] = 0;
	while (pos < n) {
		u8 type = p[pos++], len;
		const u8 *v;
		unsigned int i;
		if (type == 0xff)
			break;
		if (!type)
			continue;
		if (pos == n || (len = p[pos++]) > n - pos)
			return -EPROTO;
		v = p + pos;
		pos += len;
		if (type == 0x15 && len >= 2) {
			for (i = 2; i < len && v[i] != 0xff; i++)
				ci->version[i - 2] = v[i] ?: ' ';
			ci->version[i - 2] = 0;
		} else if (type == 0x1a && len >= 3 && contains(v, len, "DVB_CI_V")) {
			unsigned int bytes = (v[0] & 3) + 1;
			u32 base = 0;
			if (len < 2 + bytes)
				return -EINVAL;
			for (i = 0; i < bytes; i++)
				base |= (u32)v[2 + i] << (8 * i);
			if (base > U16_MAX)
				return -ERANGE;
			ci->base = base;
			config = true;
		} else if (type == 0x1b && !entry && contains(v, len, "DVB_HOST") &&
			   contains(v, len, "DVB_CI_MODULE")) {
			ci->option = v[0] & 0x3f;
			entry = true;
		}
	}
	return config && entry ? 0 : -EINVAL;
}

static int send_tpdu(struct gtx_ci *ci, u8 tag, const u8 *p, size_t len)
{
	u8 *t, *link;
	size_t i = 0, end, pos, part;
	int ret = 0;
	t = kmalloc(len + 6, GFP_KERNEL);
	link = kmalloc(ci->link_size, GFP_KERNEL);
	if (!t || !link) {
		ret = -ENOMEM;
		goto out;
	}
	t[i++] = tag;
	if (len + 1 < 128) {
		t[i++] = len + 1;
	} else {
		t[i++] = 0x82;
		put_unaligned_be16(len + 1, t + i);
		i += 2;
	}
	t[i++] = 1; /* transport connection ID */
	if (len)
		memcpy(t + i, p, len);
	end = i + len;
	for (pos = 0; pos < end; pos += part) {
		part = min_t(size_t, end - pos, ci->link_size - 2);
		link[0] = 1;
		link[1] = pos + part < end ? 0x80 : 0;
		memcpy(link + 2, t + pos, part);
		{
			unsigned long deadline = jiffies + msecs_to_jiffies(300);
			do {
				ret = command(ci, CAM_WRITE, link, part + 2);
				if (ret != -EAGAIN || !pos)
					break;
				usleep_range(2000, 4000);
			} while (time_before(jiffies, deadline));
		}
		if (ret) {
			if (pos || ret > 0)
				ret = -EIO;
			goto out;
		}
	}
	ci->waiting = true;
	ci->deadline = jiffies + 5 * HZ;
out:
	kfree(link);
	kfree(t);
	return ret;
}

static int unpack_tpdu(struct gtx_ci *ci)
{
	const u8 *p = ci->tpdu;
	unsigned int left = ci->tpdu_len;
	while (left) {
		struct sk_buff *skb;
		unsigned int len, bytes;
		u8 tag;
		if (left < 3)
			return -EPROTO;
		tag = *p++;
		len = *p++;
		left -= 2;
		if (len & 0x80) {
			bytes = len & 0x7f;
			if (!bytes || bytes > 2 || bytes >= left)
				return -EPROTO;
			len = 0;
			while (bytes--) {
				len = (len << 8) | *p++;
				left--;
			}
		}
		if (!len || len > left || *p++ != 1)
			return -EPROTO;
		left -= len;
		len--;
		switch (tag) {
		case T_CREATED:
			if (ci->state == CONNECT) {
				ci->state = RUNNING;
				dev_info(&ci->usb->usbdev->dev, "CI slot A transport ready\n");
			}
			break;
		case T_SB:
			if (len != 1)
				return -EPROTO;
			ci->receive = !!(p[0] & 0x80);
			break;
		case T_DATA_MORE:
		case T_DATA_LAST:
			if (len > CI_SPDU - ci->spdu_len)
				return -EMSGSIZE;
			memcpy(ci->spdu + ci->spdu_len, p, len);
			ci->spdu_len += len;
			if (tag == T_DATA_LAST && ci->spdu_len) {
				if (skb_queue_len(&ci->rx) >= CI_QUEUE)
					return -ENOBUFS;
				skb = alloc_skb(ci->spdu_len, GFP_KERNEL);
				if (!skb)
					return -ENOMEM;
				skb_put_data(skb, ci->spdu, ci->spdu_len);
				skb_queue_tail(&ci->rx, skb);
				ci->spdu_len = 0;
			}
			break;
		default:
			return -EPROTO;
		}
		p += len;
	}
	ci->waiting = false;
	return 0;
}

static int transport(struct gtx_ci *ci)
{
	struct sk_buff *skb;
	int ret;
	if (ci->waiting) {
		int n;
		ret = command(ci, CAM_STATUS, NULL, 0);
		if (ret < 0)
			return ret;
		if (ret != 1)
			return -EPROTO;
		if (!(ci->reply[4] & 0x80))
			return time_after(jiffies, ci->deadline) ? -ETIMEDOUT : 0;
		n = command(ci, CAM_READ, NULL, 0);
		if (n < 0)
			return n;
		if (n < 2 || n > ci->link_size || ci->reply[4] != 1 ||
		    n - 2 > CI_WIRE - ci->tpdu_len)
			return -EPROTO;
		memcpy(ci->tpdu + ci->tpdu_len, ci->reply + 6, n - 2);
		ci->tpdu_len += n - 2;
		if (ci->reply[5] & 0x80)
			return 0;
		ret = unpack_tpdu(ci);
		ci->tpdu_len = 0;
		return ret;
	}
	if (ci->state == CONNECT)
		return send_tpdu(ci, T_CREATE, NULL, 0);
	if (ci->receive) {
		ret = send_tpdu(ci, T_RCV, NULL, 0);
		if (!ret)
			ci->receive = false;
		return ret;
	}
	skb = skb_peek(&ci->tx);
	ret = send_tpdu(ci, T_DATA_LAST, skb ? skb->data : NULL, skb ? skb->len : 0);
	if (skb && !ret)
		kfree_skb(skb_dequeue(&ci->tx));
	return ret;
}

static void clear_session(struct gtx_ci *ci)
{
	skb_queue_purge(&ci->rx);
	skb_queue_purge(&ci->tx);
	ci->tpdu_len = 0;
	ci->spdu_len = 0;
	ci->waiting = false;
	ci->receive = false;
	ci->version[0] = 0;
}

static int slot_step(struct gtx_ci *ci, unsigned int *delay)
{
	u8 cor[6] = { 0 }, neg[2];
	int ret;
	switch (ci->state) {
	case EMPTY:
		*delay = 200;
		return 0;
	case RESET:
		ret = command(ci, CAM_RESET, NULL, 0);
		if (!ret) {
			ci->state = CIS;
			*delay = 500;
		}
		return ret;
	case CIS:
		ret = command(ci, CAM_CIS, NULL, 0);
		if (ret < 0)
			return ret;
		ret = parse_cis(ci, ci->reply + 4, ret);
		if (!ret)
			ci->state = CONFIGURE;
		return ret;
	case CONFIGURE:
		put_unaligned_be16(ci->base, cor);
		cor[2] = ci->option;
		cor[5] = 0x40; /* CIMaX module polling */
		ret = command(ci, CAM_COR, cor, sizeof(cor));
		if (!ret)
			ci->state = NEGOTIATE;
		return ret;
	case NEGOTIATE:
		put_unaligned_be16(CI_LINK, neg);
		ret = command(ci, CAM_NEG, neg, sizeof(neg));
		if (ret < 0)
			return ret;
		if (ret != 2)
			return -EPROTO;
		ci->link_size = get_unaligned_be16(ci->reply + 4);
		if (ci->link_size < 16 || ci->link_size > CI_LINK)
			return -EPROTO;
		ci->state = CONNECT;
		return 0;
	case CONNECT:
	case RUNNING:
		ret = transport(ci);
		if (!ret && ci->state == RUNNING && ci->pending_route != ci->route)
			ret = set_route(ci, ci->pending_route);
		return ret;
	}
	return -EINVAL;
}

static void slot_work(struct work_struct *work)
{
	struct gtx_ci *ci = container_of(to_delayed_work(work), struct gtx_ci, work);
	unsigned int delay = 15;
	int ret = 0;

	mutex_lock(&ci->lock);
	if (!ci->usb)
		goto done;
	mutex_lock(&ci->usb->lock);
	if (time_after_eq(jiffies, ci->check_contact)) {
		int contact, power;
		ret = reg_io(ci, 0x0208, -1);
		if (ret < 0)
			goto retry;
		WRITE_ONCE(ci->contact_b, !!(ret & 1));
		ret = reg_io(ci, 0x0207, -1);
		if (ret < 0)
			goto retry;
		ci->check_contact = jiffies + msecs_to_jiffies(250);
		contact = ret & 1;
		if (!contact)
			ci->power_pending = false;
		if (contact && !ci->present && !ci->power_pending) {
			ci->power_pending = true;
			delay = 200;
			ci->check_contact = jiffies + msecs_to_jiffies(delay);
			ret = 0;
			goto retry;
		}
		if (contact != ci->present) {
			power = reg_io(ci, 0x020d, -1);
			if (power < 0) {
				ret = power;
				goto retry;
			}
			/* GPIO0 bit 1 supplies the populated PC Card slot. */
			ret = reg_io(ci, 0x020d, contact ? power | 2 : power & ~2);
			if (ret)
				goto retry;
			if (contact) {
				power = reg_io(ci, 0x0202, -1);
				if (power < 0 || !(power & 0x20)) {
					ret = power < 0 ? power : -EAGAIN;
					goto retry;
				}
				if (!(power & 0x08)) {
					ret = reg_io(ci, 0x0202, power | 0x08);
					if (ret)
						goto retry;
					power = reg_io(ci, 0x0202, -1);
					if (power < 0 || !(power & 0x08)) {
						ret = power < 0 ? power : -EIO;
						goto retry;
					}
				}
			}
			ci->power_pending = false;
			WRITE_ONCE(ci->present, !!contact);
			clear_session(ci);
			ci->state = ci->present ? RESET : EMPTY;
			if (!ci->present) {
				atomic_set(&ci->remove_event, 1);
				ci->pending_route = DIRECT;
			}
			ci->last_error = 0;
			if (contact) {
				/* Let the slot supply settle before issuing CAM_RESET. */
				delay = 200;
				goto retry;
			}
		}
	}
	if ((!ci->opened || ci->state != RUNNING) && (ci->route != DIRECT || ci->pvr_started)) {
		if (ci->pending_route == FILE_INPUT)
			ci->pending_route = DIRECT;
		ret = set_route(ci, DIRECT);
		if (ret)
			goto retry;
	}
	if (ci->opened)
		ret = slot_step(ci, &delay);
	else {
		delay = 250;
		ret = 0;
	}
retry:
	if (ret == -EAGAIN) {
		delay = 30;
	} else if (ret) {
		if (ci->last_error != ret) {
			dev_warn(&ci->usb->usbdev->dev, "CI slot A state %u error %d\n",
				 ci->state, ret);
			ci->last_error = ret;
		}
		if (ci->state == RUNNING)
			atomic_set(&ci->remove_event, 1);
		clear_session(ci);
		ci->state = ci->present ? RESET : EMPTY;
		delay = 1000;
	}
	mutex_unlock(&ci->usb->lock);
	queue_delayed_work(system_long_wq, &ci->work, msecs_to_jiffies(delay));
	wake_up_interruptible(&ci->wait);
done:
	mutex_unlock(&ci->lock);
}

static void free_slot(struct kref *ref)
{
	struct gtx_ci *ci = container_of(ref, struct gtx_ci, ref);
	clear_session(ci);
	kfree(ci->spdu);
	kfree(ci->tpdu);
	kfree(ci->reply);
	kfree(ci->wire);
	kfree(ci);
}

static int slot_open(struct inode *inode, struct file *file)
{
	struct gtx_ci *ci = container_of(file->private_data, struct gtx_ci, node);
	int ret = 0;
	mutex_lock(&ci->lock);
	if (!ci->usb)
		ret = -ENODEV;
	else if (ci->opened)
		ret = -EBUSY;
	else {
		kref_get(&ci->ref);
		ci->opened = true;
		atomic_set(&ci->remove_event, 0);
		file->private_data = ci;
		mod_delayed_work(system_long_wq, &ci->work, 0);
	}
	mutex_unlock(&ci->lock);
	return ret;
}

static int slot_close(struct inode *inode, struct file *file)
{
	struct gtx_ci *ci = file->private_data;
	mutex_lock(&ci->lock);
	ci->opened = false;
	ci->pending_route = DIRECT;
	clear_session(ci);
	ci->state = ci->present ? RESET : EMPTY;
	if (ci->usb)
		mod_delayed_work(system_long_wq, &ci->work, 0);
	mutex_unlock(&ci->lock);
	kref_put(&ci->ref, free_slot);
	return 0;
}

static ssize_t slot_read(struct file *file, char __user *out, size_t count, loff_t *offset)
{
	struct gtx_ci *ci = file->private_data;
	struct sk_buff *skb;
	int ret;

	if (!count)
		return 0;
	if (!(file->f_flags & O_NONBLOCK)) {
		ret = wait_event_interruptible(ci->wait, !skb_queue_empty(&ci->rx) ||
					       !READ_ONCE(ci->usb) || !READ_ONCE(ci->present));
		if (ret)
			return ret;
	}
	mutex_lock(&ci->lock);
	skb = skb_peek(&ci->rx);
	if (!ci->usb || !ci->present)
		ret = -ENODEV;
	else if (!skb)
		ret = -EAGAIN;
	else if (count < skb->len)
		ret = -EMSGSIZE;
	else if (copy_to_user(out, skb->data, skb->len))
		ret = -EFAULT;
	else {
		ret = skb->len;
		kfree_skb(skb_dequeue(&ci->rx));
	}
	mutex_unlock(&ci->lock);
	return ret;
}

static ssize_t slot_write(struct file *file, const char __user *in, size_t count, loff_t *offset)
{
	struct gtx_ci *ci = file->private_data;
	struct sk_buff *skb;
	ssize_t ret = count;
	if (!count || count > CI_SPDU)
		return -EMSGSIZE;
	mutex_lock(&ci->lock);
	if (!ci->usb || !ci->present)
		ret = -ENODEV;
	else if (ci->state != RUNNING || skb_queue_len(&ci->tx) >= CI_QUEUE)
		ret = -EAGAIN;
	else {
		skb = alloc_skb(count, GFP_KERNEL);
		if (!skb)
			ret = -ENOMEM;
		else if (copy_from_user(skb_put(skb, count), in, count)) {
			kfree_skb(skb);
			ret = -EFAULT;
		} else {
			skb_queue_tail(&ci->tx, skb);
			mod_delayed_work(system_long_wq, &ci->work, 0);
		}
	}
	mutex_unlock(&ci->lock);
	return ret;
}

static __poll_t slot_poll(struct file *file, poll_table *wait)
{
	struct gtx_ci *ci = file->private_data;
	__poll_t mask = 0;
	poll_wait(file, &ci->wait, wait);
	/* A slow PC Card reset must never stall the Enigma2 event loop. */
	if (!READ_ONCE(ci->usb))
		mask = EPOLLHUP | EPOLLERR;
	else if (atomic_xchg(&ci->remove_event, 0))
		mask = EPOLLPRI;
	else {
		if (!skb_queue_empty_lockless(&ci->rx))
			mask |= EPOLLIN | EPOLLRDNORM;
		if (READ_ONCE(ci->present) && skb_queue_len_lockless(&ci->tx) < CI_QUEUE &&
		    READ_ONCE(ci->state) == RUNNING)
			mask |= EPOLLOUT | EPOLLWRNORM;
	}
	return mask;
}

static long slot_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
	struct gtx_ci *ci = file->private_data;
	long ret = 0;
	mutex_lock(&ci->lock);
	if (!ci->usb)
		ret = -ENODEV;
	else if (cmd == 0) {
		clear_session(ci);
		ci->state = ci->present ? RESET : EMPTY;
		mod_delayed_work(system_long_wq, &ci->work, 0);
	} else if (cmd == 1) {
		if (copy_to_user((void __user *)arg, ci->version, strlen(ci->version) + 1))
			ret = -EFAULT;
	} else
		ret = -ENOTTY;
	mutex_unlock(&ci->lock);
	return ret;
}

static const struct file_operations slot_ops = {
	.owner = THIS_MODULE, .open = slot_open, .release = slot_close,
	.read = slot_read, .write = slot_write, .unlocked_ioctl = slot_ioctl,
	.poll = slot_poll, .llseek = no_llseek,
};

/* The physical return FIFO fills in blocks. Null packets establish sync at
 * start and flush the last data block without adding a program PID. */
static int pvr_pad(struct gtx_ci *ci)
{
	const unsigned int size = 56 * 188;
	u8 *data = kmalloc(size, GFP_KERNEL);
	unsigned int i;
	int err = 0, sent;

	if (!data)
		return -ENOMEM;
	memset(data, 0xff, size);
	for (i = 0; i < size; i += 188) {
		data[i] = 0x47;
		data[i + 1] = 0x1f;
		data[i + 3] = 0x10;
	}
	for (i = 0; i < 8; i++) {
		err = usb_bulk_msg(ci->usb->usbdev, usb_sndbulkpipe(ci->usb->usbdev, 3),
				   data, size, &sent, 500);
		if (err || sent != size) {
			if (!err)
				err = -EIO;
			break;
		}
	}
	kfree(data);
	return err;
}

static int pvr_open(struct inode *inode, struct file *file)
{
	struct gtx_ci *ci = container_of(file->private_data, struct gtx_ci, pvr_node);
	int err = 0;

	if ((file->f_flags & O_ACCMODE) != O_WRONLY)
		return -EACCES;
	mutex_lock(&ci->lock);
	if (!ci->usb)
		err = -ENODEV;
	else if (!ci->opened || ci->state != RUNNING)
		err = -EAGAIN;
	else if (ci->pvr_open || ci->route != DIRECT || ci->pending_route != DIRECT)
		err = -EBUSY;
	else {
		mutex_lock(&ci->usb->lock);
		err = start_pvr(ci);
		if (!err)
			err = set_route(ci, FILE_INPUT);
		if (!err)
			err = pvr_pad(ci);
		if (err) {
			set_route(ci, DIRECT);
		} else {
			ci->pvr_open = true;
			ci->ci_source = ci->pending_route = FILE_INPUT;
			kref_get(&ci->ref);
			file->private_data = ci;
		}
		mutex_unlock(&ci->usb->lock);
	}
	mutex_unlock(&ci->lock);
	return err;
}

static ssize_t pvr_write(struct file *file, const char __user *data, size_t count, loff_t *offset)
{
	struct gtx_ci *ci = file->private_data;
	int sent = 0, err;
	u8 *packets;

	if (!count)
		return 0;
	count = min_t(size_t, count, 64 * 188);
	packets = memdup_user(data, count);
	if (IS_ERR(packets))
		return PTR_ERR(packets);
	if (mutex_lock_interruptible(&ci->lock)) {
		kfree(packets);
		return -ERESTARTSYS;
	}
	if (!ci->usb || ci->state != RUNNING || ci->route != FILE_INPUT ||
	    !ci->pvr_started)
		err = -EPIPE;
	else
		err = usb_bulk_msg(ci->usb->usbdev, usb_sndbulkpipe(ci->usb->usbdev, 3),
				   packets, count, &sent, 500);
	mutex_unlock(&ci->lock);
	kfree(packets);
	if (sent > 0)
		return sent;
	return err ? err : -EIO;
}

static int pvr_fsync(struct file *file, loff_t start, loff_t end, int datasync)
{
	struct gtx_ci *ci = file->private_data;
	int err = -EPIPE;

	mutex_lock(&ci->lock);
	if (ci->usb && ci->state == RUNNING && ci->route == FILE_INPUT)
		err = pvr_pad(ci);
	mutex_unlock(&ci->lock);
	return err;
}

static int pvr_close(struct inode *inode, struct file *file)
{
	struct gtx_ci *ci = file->private_data;
	int err = 0;

	mutex_lock(&ci->lock);
	if (ci->usb && (ci->route == FILE_INPUT || ci->pvr_started)) {
		mutex_lock(&ci->usb->lock);
		ci->pending_route = DIRECT;
		err = set_route(ci, DIRECT);
		mutex_unlock(&ci->usb->lock);
	}
	ci->pvr_open = false;
	if (ci->ci_source == FILE_INPUT)
		ci->ci_source = TUNER_B;
	mutex_unlock(&ci->lock);
	kref_put(&ci->ref, free_slot);
	return err;
}

static const struct file_operations pvr_ops = {
	.owner = THIS_MODULE, .open = pvr_open, .release = pvr_close,
	.write = pvr_write, .fsync = pvr_fsync, .llseek = no_llseek,
};

static ssize_t mux_read(struct file *file, char __user *buf, size_t len, loff_t *pos)
{
	struct gtx_ci *ci = PDE_DATA(file_inode(file));
	const char *name = file_dentry(file)->d_name.name;
	const char *value;

	if (!strcmp(name, "input0_choices"))
		value = "A CI0\n";
	else if (!strcmp(name, "input1_choices"))
		value = "B CI0\n";
	else if (!strcmp(name, "ci0_input_choices"))
		value = "A B PVR NONE\n";
	else if (!strcmp(name, "input0"))
		value = READ_ONCE(ci->route) == TUNER_A ? "CI0\n" : "A\n";
	else if (!strcmp(name, "input1"))
		value = READ_ONCE(ci->route) == TUNER_B ? "CI0\n" : "B\n";
	else
		value = READ_ONCE(ci->ci_source) == FILE_INPUT ? "PVR\n" :
			(READ_ONCE(ci->ci_source) == TUNER_A ? "A\n" : "B\n");
	return simple_read_from_buffer(buf, len, pos, value, strlen(value));
}

static ssize_t mux_write(struct file *file, const char __user *buf, size_t len, loff_t *pos)
{
	struct gtx_ci *ci = PDE_DATA(file_inode(file));
	const char *name = file_dentry(file)->d_name.name;
	char input[16], *value;
	bool source = !strcmp(name, "ci0_input");
	int tuner, route, ret = 0;
	if (!len || len >= sizeof(input))
		return -EINVAL;
	if (copy_from_user(input, buf, len))
		return -EFAULT;
	input[len] = 0;
	value = strim(input);
	if (source) {
		if (!strcmp(value, "PVR") || !strcmp(value, "NONE")) {
			bool select = !strcmp(value, "PVR");

			mutex_lock(&ci->lock);
			if (!ci->usb)
				ret = -ENODEV;
			else if (select && ci->route != DIRECT && ci->route != FILE_INPUT)
				ret = -EBUSY;
			else if (select)
				ci->ci_source = FILE_INPUT;
			else if (ci->route == FILE_INPUT) {
				mutex_lock(&ci->usb->lock);
				ci->pending_route = DIRECT;
				ret = set_route(ci, DIRECT);
				mutex_unlock(&ci->usb->lock);
				if (!ret)
					ci->ci_source = TUNER_B;
			} else if (ci->ci_source == FILE_INPUT)
				ci->ci_source = TUNER_B;
			mutex_unlock(&ci->lock);
			return ret ? ret : len;
		}
		if (strcmp(value, "A") && strcmp(value, "B"))
			return -EINVAL;
		tuner = !strcmp(value, "A") ? TUNER_A : TUNER_B;
	} else {
		if (strcmp(name, "input0") && strcmp(name, "input1"))
			return -EINVAL;
		tuner = !strcmp(name, "input0") ? TUNER_A : TUNER_B;
		if (strcmp(value, "CI0") && strcmp(value, tuner == TUNER_A ? "A" : "B"))
			return -EINVAL;
	}
	mutex_lock(&ci->lock);
	route = ci->route;
	if (source) {
		if (route != DIRECT)
			route = tuner;
	} else if (!strcmp(value, "CI0")) {
		route = tuner;
	} else if (route == tuner) {
		route = DIRECT;
	}
	if (!ci->usb)
		ret = -ENODEV;
	else if (route != DIRECT && ci->state != RUNNING)
		ret = -EAGAIN;
	else {
		if (route != ci->route) {
			mutex_lock(&ci->usb->lock);
			ret = set_route(ci, route);
			mutex_unlock(&ci->usb->lock);
		}
		if (!ret) {
			ci->pending_route = route;
			if (source || route == tuner)
				ci->ci_source = tuner;
		}
	}
	mutex_unlock(&ci->lock);
	return ret ? ret : len;
}

static const struct proc_ops mux_ops = {
	.proc_read = mux_read, .proc_write = mux_write, .proc_lseek = default_llseek,
};

/* Fixed board and packet-clock diagnostics. No session data is exposed. */
static ssize_t ts_route_status_show(struct device *dev, struct device_attribute *attr,
				    char *buf)
{
	struct miscdevice *node = dev_get_drvdata(dev);
	struct gtx_ci *ci = container_of(node, struct gtx_ci, node);
	static const struct { const char *name; u16 addr; } fields[] = {
		{ "input", 0x022d }, { "output", 0x022e }, { "channel", 0x022f },
		{ "module", 0x0230 }, { "slot_control", 0x0207 }, { "power", 0x0202 },
		{ "slot_supply", 0x020d }, { "parallel", 0x0225 }, { "parallel_clock", 0x0226 },
		{ "clock_enable", 0x0048 }, { "clock_select", 0x0049 },
		{ "serial_input1", 0x0228 }, { "serial_output1", 0x022a },
		{ "packet_length", 0x0220 }, { "rate0_lo", 0x02c5 },
		{ "rate0_hi", 0x02c6 }, { "rate1_lo", 0x02c7 }, { "rate1_hi", 0x02c8 },
	};
	int i, len = 0;

	mutex_lock(&ci->lock);
	if (!ci->usb) {
		mutex_unlock(&ci->lock);
		return -ENODEV;
	}
	mutex_lock(&ci->usb->lock);
	for (i = 0; i < ARRAY_SIZE(fields); i++) {
		int val = reg_io(ci, fields[i].addr, -1);
		if (val < 0) {
			len = val;
			break;
		}
		len += sysfs_emit_at(buf, len, "%s=%02x\n", fields[i].name, val);
	}
	mutex_unlock(&ci->usb->lock);
	mutex_unlock(&ci->lock);
	return len;
}
static DEVICE_ATTR_RO(ts_route_status);

static struct attribute *gtx_ci_attrs[] = {
	&dev_attr_ts_route_status.attr,
	NULL,
};
ATTRIBUTE_GROUPS(gtx_ci);

int gtx_ci_attach(struct device_s *usb)
{
	static const char * const names[] = { "input0", "input0_choices", "input1",
		"input1_choices", "ci0_input", "ci0_input_choices" };
	struct gtx_ci *ci;
	int i, ret = -ENOMEM;
	ci = kzalloc(sizeof(*ci), GFP_KERNEL);
	if (!ci)
		return -ENOMEM;
	kref_init(&ci->ref);
	mutex_init(&ci->lock);
	skb_queue_head_init(&ci->rx);
	skb_queue_head_init(&ci->tx);
	init_waitqueue_head(&ci->wait);
	INIT_DELAYED_WORK(&ci->work, slot_work);
	ci->wire = kmalloc(CI_WIRE, GFP_KERNEL);
	ci->reply = kmalloc(CI_WIRE + 512, GFP_KERNEL);
	ci->tpdu = kmalloc(CI_WIRE, GFP_KERNEL);
	ci->spdu = kmalloc(CI_SPDU, GFP_KERNEL);
	if (!ci->wire || !ci->reply || !ci->tpdu || !ci->spdu)
		goto fail;
	ci->usb = usb;
	ci->ci_source = TUNER_B;
	ci->check_contact = jiffies;
	ci->node.minor = MISC_DYNAMIC_MINOR;
	ci->node.name = "ci0";
	ci->node.mode = 0600;
	ci->node.fops = &slot_ops;
	ci->node.groups = gtx_ci_groups;
	ci->node.parent = &usb->usbdev->dev;
	ci->mux = proc_mkdir("stb/tsmux", NULL);
	if (!ci->mux)
		goto fail;
	for (i = 0; i < ARRAY_SIZE(names); i++)
		if (!proc_create_data(names[i], strstr(names[i], "_choices") ? 0444 : 0644,
				      ci->mux, &mux_ops, ci))
			goto fail_mux;
	ci->pvr_node.minor = MISC_DYNAMIC_MINOR;
	ci->pvr_node.name = "gtx-ci-pvr0";
	ci->pvr_node.mode = 0600;
	ci->pvr_node.fops = &pvr_ops;
	ci->pvr_node.parent = ci->node.parent;
	ret = misc_register(&ci->pvr_node);
	if (ret)
		goto fail_mux;
	ret = misc_register(&ci->node);
	if (ret) {
		misc_deregister(&ci->pvr_node);
		goto fail_mux;
	}
	mutex_lock(&usb->lock);
	usb->ci_slot = ci;
	mutex_unlock(&usb->lock);
	queue_delayed_work(system_long_wq, &ci->work, 0);
	return 0;
fail_mux:
	proc_remove(ci->mux);
fail:
	kref_put(&ci->ref, free_slot);
	return ret;
}

ssize_t gtx_ci_contacts(struct device_s *usb, char *buf)
{
	/* Called with usb->lock held. The slot worker owns the EP5 stream. */
	return sysfs_emit(buf, "A=%u B=%u\n", READ_ONCE(usb->ci_slot->present),
			  READ_ONCE(usb->ci_slot->contact_b));
}

void gtx_ci_detach(struct device_s *usb)
{
	struct gtx_ci *ci = usb->ci_slot;
	if (!ci)
		return;
	misc_deregister(&ci->pvr_node);
	misc_deregister(&ci->node);
	proc_remove(ci->mux);
	mutex_lock(&ci->lock);
	mutex_lock(&usb->lock);
	ci->usb = NULL;
	usb->ci_slot = NULL;
	mutex_unlock(&usb->lock);
	mutex_unlock(&ci->lock);
	cancel_delayed_work_sync(&ci->work);
	wake_up_interruptible(&ci->wait);
	kref_put(&ci->ref, free_slot);
}
