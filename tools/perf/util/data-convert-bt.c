// SPDX-License-Identifier: GPL-2.0-only
/*
 * CTF writing support via babeltrace.
 *
 * Copyright (C) 2014, Jiri Olsa <jolsa@redhat.com>
 * Copyright (C) 2014, Sebastian Andrzej Siewior <bigeasy@linutronix.de>
 */

#include <errno.h>
#include <inttypes.h>
#include <linux/compiler.h>
#include <linux/kernel.h>
#include <linux/zalloc.h>
#include <babeltrace2-ctf-writer/writer.h>
#include <babeltrace2-ctf-writer/clock.h>
#include <babeltrace2-ctf-writer/stream.h>
#include <babeltrace2-ctf-writer/event.h>
#include <babeltrace2-ctf-writer/event-types.h>
#include <babeltrace2-ctf-writer/event-fields.h>
#include <babeltrace2-ctf-writer/utils.h>
#include "asm/bug.h"
#include "data-convert.h"
#include "session.h"
#include "debug.h"
#include "tool.h"
#include "evlist.h"
#include "evsel.h"
#include "machine.h"
#include "config.h"
#include <linux/ctype.h>
#include <linux/err.h>
#include <linux/time64.h>
#include "util.h"
#include "clockid.h"
#include "util/sample.h"
#include "util/time-utils.h"
#include "header.h"
#include "addr_location.h"
#include "annotate.h"
#include "annotate-data.h"
#include "build-id.h"
#include "dso.h"
#include "map.h"
#include "map_symbol.h"
#include "symbol.h"
#include "thread.h"

#ifdef HAVE_LIBTRACEEVENT
#include <event-parse.h>
#endif

#define pr_N(n, fmt, ...) \
	eprintf(n, debug_data_convert, fmt, ##__VA_ARGS__)

#define pr(fmt, ...)  pr_N(1, pr_fmt(fmt), ##__VA_ARGS__)
#define pr2(fmt, ...) pr_N(2, pr_fmt(fmt), ##__VA_ARGS__)

#define pr_time2(t, fmt, ...) pr_time_N(2, debug_data_convert, t, pr_fmt(fmt), ##__VA_ARGS__)

struct evsel_priv {
	struct bt_ctf_event_class *event_class;
	/* The samples of this event carry the resolved data type fields */
	bool data_type;
};

#define MAX_CPUS	4096

struct ctf_stream {
	struct bt_ctf_stream *stream;
	int cpu;
	u32 count;
};

struct ctf_writer {
	/* writer primitives */
	struct bt_ctf_writer		 *writer;
	struct ctf_stream		**stream;
	int				  stream_cnt;
	struct bt_ctf_stream_class	 *stream_class;
	struct bt_ctf_clock		 *clock;

	/* data types */
	union {
		struct {
			struct bt_ctf_field_type	*s64;
			struct bt_ctf_field_type	*u64;
			struct bt_ctf_field_type	*s32;
			struct bt_ctf_field_type	*u32;
			struct bt_ctf_field_type	*string;
			struct bt_ctf_field_type	*u32_hex;
			struct bt_ctf_field_type	*u64_hex;
		};
		struct bt_ctf_field_type *array[6];
	} data;
	struct bt_ctf_event_class	*comm_class;
	struct bt_ctf_event_class	*exit_class;
	struct bt_ctf_event_class	*fork_class;
	struct bt_ctf_event_class	*mmap_class;
	struct bt_ctf_event_class	*mmap2_class;

	/* data type profiling of the memory samples */
	bool				 data_type;
	struct bt_ctf_event_class	*dso_info_class;
};

struct convert {
	struct perf_tool	tool;
	struct ctf_writer	writer;

	struct perf_time_interval *ptime_range;
	int range_size;
	int range_num;

	u64			events_size;
	u64			events_count;
	u64			non_sample_count;
	u64			skipped;

	/* Ordered events configured queue size. */
	u64			queue_size;

	/*
	 * DSOs the data types were resolved in, in id order: the id a
	 * perf_sample record carries is its index in here plus one, so that
	 * zero stays free for the samples no type was resolved for.  The
	 * pointers are borrowed from the session's machines, which outlive
	 * the conversion.
	 */
	struct dso		**dt_dsos;
	size_t			dt_nr_dsos;
	u64			dt_resolved;
	u64			dt_bad_addr;
};

static int value_set(struct bt_ctf_field_type *type,
		     struct bt_ctf_event *event,
		     const char *name, u64 val)
{
	struct bt_ctf_field *field;
	bool sign = bt_ctf_field_type_integer_get_signed(type);
	int ret;

	field = bt_ctf_field_create(type);
	if (!field) {
		pr_err("failed to create a field %s\n", name);
		return -1;
	}

	if (sign) {
		ret = bt_ctf_field_integer_signed_set_value(field, val);
		if (ret) {
			pr_err("failed to set field value %s\n", name);
			goto err;
		}
	} else {
		ret = bt_ctf_field_integer_unsigned_set_value(field, val);
		if (ret) {
			pr_err("failed to set field value %s\n", name);
			goto err;
		}
	}

	ret = bt_ctf_event_set_payload(event, name, field);
	if (ret) {
		pr_err("failed to set payload %s\n", name);
		goto err;
	}

	pr2("  SET [%s = %" PRIu64 "]\n", name, val);

err:
	bt_ctf_field_put(field);
	return ret;
}

#define __FUNC_VALUE_SET(_name, _val_type)				\
static __maybe_unused int value_set_##_name(struct ctf_writer *cw,	\
			     struct bt_ctf_event *event,		\
			     const char *name,				\
			     _val_type val)				\
{									\
	struct bt_ctf_field_type *type = cw->data._name;		\
	return value_set(type, event, name, (u64) val);			\
}

#define FUNC_VALUE_SET(_name) __FUNC_VALUE_SET(_name, _name)

FUNC_VALUE_SET(s32)
FUNC_VALUE_SET(u32)
FUNC_VALUE_SET(s64)
FUNC_VALUE_SET(u64)
__FUNC_VALUE_SET(u64_hex, u64)

static int string_set_value(struct bt_ctf_field *field, const char *string);
static __maybe_unused int
value_set_string(struct ctf_writer *cw, struct bt_ctf_event *event,
		 const char *name, const char *string)
{
	struct bt_ctf_field_type *type = cw->data.string;
	struct bt_ctf_field *field;
	int ret = 0;

	field = bt_ctf_field_create(type);
	if (!field) {
		pr_err("failed to create a field %s\n", name);
		return -1;
	}

	ret = string_set_value(field, string);
	if (ret) {
		pr_err("failed to set value %s\n", name);
		goto err_put_field;
	}

	ret = bt_ctf_event_set_payload(event, name, field);
	if (ret)
		pr_err("failed to set payload %s\n", name);

err_put_field:
	bt_ctf_field_put(field);
	return ret;
}

static struct bt_ctf_field_type*
get_tracepoint_field_type(struct ctf_writer *cw, struct tep_format_field *field)
{
	unsigned long flags = field->flags;

	if (flags & TEP_FIELD_IS_STRING)
		return cw->data.string;

	if (!(flags & TEP_FIELD_IS_SIGNED)) {
		/* unsigned long are mostly pointers */
		if (flags & TEP_FIELD_IS_LONG || flags & TEP_FIELD_IS_POINTER)
			return cw->data.u64_hex;
	}

	if (flags & TEP_FIELD_IS_SIGNED) {
		if (field->size == 8)
			return cw->data.s64;
		else
			return cw->data.s32;
	}

	if (field->size == 8)
		return cw->data.u64;
	else
		return cw->data.u32;
}

static unsigned long long adjust_signedness(unsigned long long value_int, int size)
{
	unsigned long long value_mask;

	/*
	 * value_mask = (1 << (size * 8 - 1)) - 1.
	 * Directly set value_mask for code readers.
	 */
	switch (size) {
	case 1:
		value_mask = 0x7fULL;
		break;
	case 2:
		value_mask = 0x7fffULL;
		break;
	case 4:
		value_mask = 0x7fffffffULL;
		break;
	case 8:
		/*
		 * For 64 bit value, return it self. There is no need
		 * to fill high bit.
		 */
		/* Fall through */
	default:
		/* BUG! */
		return value_int;
	}

	/* If it is a positive value, don't adjust. */
	if ((value_int & (~0ULL - value_mask)) == 0)
		return value_int;

	/* Fill upper part of value_int with 1 to make it a negative long long. */
	return (value_int & value_mask) | ~value_mask;
}

static int string_set_value(struct bt_ctf_field *field, const char *string)
{
	char *buffer = NULL;
	size_t len = strlen(string), i, p;
	int err;

	for (i = p = 0; i < len; i++, p++) {
		if (isprint(string[i])) {
			if (!buffer)
				continue;
			buffer[p] = string[i];
		} else {
			char numstr[5];

			snprintf(numstr, sizeof(numstr), "\\x%02x",
				 (unsigned int)(string[i]) & 0xff);

			if (!buffer) {
				buffer = zalloc(i + (len - i) * 4 + 2);
				if (!buffer) {
					pr_err("failed to set unprintable string '%s'\n", string);
					return bt_ctf_field_string_set_value(field, "UNPRINTABLE-STRING");
				}
				if (i > 0)
					strncpy(buffer, string, i);
			}
			memcpy(buffer + p, numstr, 4);
			p += 3;
		}
	}

	if (!buffer)
		return bt_ctf_field_string_set_value(field, string);
	err = bt_ctf_field_string_set_value(field, buffer);
	free(buffer);
	return err;
}

static int add_tracepoint_field_value(struct ctf_writer *cw,
				      struct bt_ctf_event_class *event_class,
				      struct bt_ctf_event *event,
				      struct perf_sample *sample,
				      struct tep_format_field *fmtf)
{
	struct bt_ctf_field_type *type;
	struct bt_ctf_field *array_field;
	struct bt_ctf_field *field;
	const char *name = fmtf->name;
	void *data = sample->raw_data;
	unsigned long flags = fmtf->flags;
	unsigned int n_items;
	unsigned int i;
	unsigned int offset;
	unsigned int len;
	int ret;

	name = fmtf->alias;
	offset = fmtf->offset;
	len = fmtf->size;
	if (flags & TEP_FIELD_IS_STRING)
		flags &= ~TEP_FIELD_IS_ARRAY;

	if (flags & TEP_FIELD_IS_DYNAMIC) {
		unsigned long long tmp_val;

		tmp_val = tep_read_number(fmtf->event->tep,
					  data + offset, len);
		offset = tmp_val;
		len = offset >> 16;
		offset &= 0xffff;
		if (tep_field_is_relative(flags))
			offset += fmtf->offset + fmtf->size;
	}

	if (flags & TEP_FIELD_IS_ARRAY) {

		type = bt_ctf_event_class_get_field_by_name(
				event_class, name);
		array_field = bt_ctf_field_create(type);
		bt_ctf_field_type_put(type);
		if (!array_field) {
			pr_err("Failed to create array type %s\n", name);
			return -1;
		}

		len = fmtf->size / fmtf->arraylen;
		n_items = fmtf->arraylen;
	} else {
		n_items = 1;
		array_field = NULL;
	}

	type = get_tracepoint_field_type(cw, fmtf);

	for (i = 0; i < n_items; i++) {
		if (flags & TEP_FIELD_IS_ARRAY)
			field = bt_ctf_field_array_get_field(array_field, i);
		else
			field = bt_ctf_field_create(type);

		if (!field) {
			pr_err("failed to create a field %s\n", name);
			return -1;
		}

		if (flags & TEP_FIELD_IS_STRING)
			ret = string_set_value(field, data + offset + i * len);
		else {
			unsigned long long value_int;

			value_int = tep_read_number(
					fmtf->event->tep,
					data + offset + i * len, len);

			if (!(flags & TEP_FIELD_IS_SIGNED))
				ret = bt_ctf_field_integer_unsigned_set_value(
						field, value_int);
			else
				ret = bt_ctf_field_integer_signed_set_value(
						field, adjust_signedness(value_int, len));
		}

		if (ret) {
			pr_err("failed to set file value %s\n", name);
			goto err_put_field;
		}
		if (!(flags & TEP_FIELD_IS_ARRAY)) {
			ret = bt_ctf_event_set_payload(event, name, field);
			if (ret) {
				pr_err("failed to set payload %s\n", name);
				goto err_put_field;
			}
		}
		bt_ctf_field_put(field);
	}
	if (flags & TEP_FIELD_IS_ARRAY) {
		ret = bt_ctf_event_set_payload(event, name, array_field);
		if (ret) {
			pr_err("Failed add payload array %s\n", name);
			return -1;
		}
		bt_ctf_field_put(array_field);
	}
	return 0;

err_put_field:
	bt_ctf_field_put(field);
	return -1;
}

static int add_tracepoint_fields_values(struct ctf_writer *cw,
					struct bt_ctf_event_class *event_class,
					struct bt_ctf_event *event,
					struct tep_format_field *fields,
					struct perf_sample *sample)
{
	struct tep_format_field *field;
	int ret;

	for (field = fields; field; field = field->next) {
		ret = add_tracepoint_field_value(cw, event_class, event, sample,
				field);
		if (ret)
			return -1;
	}
	return 0;
}

static int add_tracepoint_values(struct ctf_writer *cw,
				 struct bt_ctf_event_class *event_class,
				 struct bt_ctf_event *event,
				 struct evsel *evsel,
				 struct perf_sample *sample)
{
	const struct tep_event *tp_format = evsel__tp_format(evsel);
	struct tep_format_field *common_fields = tp_format->format.common_fields;
	struct tep_format_field *fields        = tp_format->format.fields;
	int ret;

	ret = add_tracepoint_fields_values(cw, event_class, event,
					   common_fields, sample);
	if (!ret)
		ret = add_tracepoint_fields_values(cw, event_class, event,
						   fields, sample);

	return ret;
}

static int
add_bpf_output_values(struct bt_ctf_event_class *event_class,
		      struct bt_ctf_event *event,
		      struct perf_sample *sample)
{
	struct bt_ctf_field_type *len_type, *seq_type;
	struct bt_ctf_field *len_field, *seq_field;
	unsigned int raw_size = sample->raw_size;
	unsigned int nr_elements = raw_size / sizeof(u32);
	unsigned int i;
	int ret;

	if (nr_elements * sizeof(u32) != raw_size)
		pr_warning("Incorrect raw_size (%u) in bpf output event, skip %zu bytes\n",
			   raw_size, nr_elements * sizeof(u32) - raw_size);

	len_type = bt_ctf_event_class_get_field_by_name(event_class, "raw_len");
	len_field = bt_ctf_field_create(len_type);
	if (!len_field) {
		pr_err("failed to create 'raw_len' for bpf output event\n");
		ret = -1;
		goto put_len_type;
	}

	ret = bt_ctf_field_integer_unsigned_set_value(len_field, nr_elements);
	if (ret) {
		pr_err("failed to set field value for raw_len\n");
		goto put_len_field;
	}
	ret = bt_ctf_event_set_payload(event, "raw_len", len_field);
	if (ret) {
		pr_err("failed to set payload to raw_len\n");
		goto put_len_field;
	}

	seq_type = bt_ctf_event_class_get_field_by_name(event_class, "raw_data");
	seq_field = bt_ctf_field_create(seq_type);
	if (!seq_field) {
		pr_err("failed to create 'raw_data' for bpf output event\n");
		ret = -1;
		goto put_seq_type;
	}

	ret = bt_ctf_field_sequence_set_length(seq_field, len_field);
	if (ret) {
		pr_err("failed to set length of 'raw_data'\n");
		goto put_seq_field;
	}

	for (i = 0; i < nr_elements; i++) {
		struct bt_ctf_field *elem_field =
			bt_ctf_field_sequence_get_field(seq_field, i);

		ret = bt_ctf_field_integer_unsigned_set_value(elem_field,
				((u32 *)(sample->raw_data))[i]);

		bt_ctf_field_put(elem_field);
		if (ret) {
			pr_err("failed to set raw_data[%d]\n", i);
			goto put_seq_field;
		}
	}

	ret = bt_ctf_event_set_payload(event, "raw_data", seq_field);
	if (ret)
		pr_err("failed to set payload for raw_data\n");

put_seq_field:
	bt_ctf_field_put(seq_field);
put_seq_type:
	bt_ctf_field_type_put(seq_type);
put_len_field:
	bt_ctf_field_put(len_field);
put_len_type:
	bt_ctf_field_type_put(len_type);
	return ret;
}

static int
add_callchain_output_values(struct bt_ctf_event_class *event_class,
		      struct bt_ctf_event *event,
		      struct ip_callchain *callchain)
{
	struct bt_ctf_field_type *len_type, *seq_type;
	struct bt_ctf_field *len_field, *seq_field;
	unsigned int nr_elements = callchain->nr;
	unsigned int i;
	int ret;

	len_type = bt_ctf_event_class_get_field_by_name(
			event_class, "perf_callchain_size");
	len_field = bt_ctf_field_create(len_type);
	if (!len_field) {
		pr_err("failed to create 'perf_callchain_size' for callchain output event\n");
		ret = -1;
		goto put_len_type;
	}

	ret = bt_ctf_field_integer_unsigned_set_value(len_field, nr_elements);
	if (ret) {
		pr_err("failed to set field value for perf_callchain_size\n");
		goto put_len_field;
	}
	ret = bt_ctf_event_set_payload(event, "perf_callchain_size", len_field);
	if (ret) {
		pr_err("failed to set payload to perf_callchain_size\n");
		goto put_len_field;
	}

	seq_type = bt_ctf_event_class_get_field_by_name(
			event_class, "perf_callchain");
	seq_field = bt_ctf_field_create(seq_type);
	if (!seq_field) {
		pr_err("failed to create 'perf_callchain' for callchain output event\n");
		ret = -1;
		goto put_seq_type;
	}

	ret = bt_ctf_field_sequence_set_length(seq_field, len_field);
	if (ret) {
		pr_err("failed to set length of 'perf_callchain'\n");
		goto put_seq_field;
	}

	for (i = 0; i < nr_elements; i++) {
		struct bt_ctf_field *elem_field =
			bt_ctf_field_sequence_get_field(seq_field, i);

		ret = bt_ctf_field_integer_unsigned_set_value(elem_field,
				((u64 *)(callchain->ips))[i]);

		bt_ctf_field_put(elem_field);
		if (ret) {
			pr_err("failed to set callchain[%d]\n", i);
			goto put_seq_field;
		}
	}

	ret = bt_ctf_event_set_payload(event, "perf_callchain", seq_field);
	if (ret)
		pr_err("failed to set payload for raw_data\n");

put_seq_field:
	bt_ctf_field_put(seq_field);
put_seq_type:
	bt_ctf_field_type_put(seq_type);
put_len_field:
	bt_ctf_field_put(len_field);
put_len_type:
	bt_ctf_field_type_put(len_type);
	return ret;
}

static int add_generic_values(struct ctf_writer *cw,
			      struct bt_ctf_event *event,
			      struct evsel *evsel,
			      struct perf_sample *sample)
{
	u64 type = evsel->core.attr.sample_type;
	int ret;

	/*
	 * missing:
	 *   PERF_SAMPLE_TIME         - not needed as we have it in
	 *                              ctf event header
	 *   PERF_SAMPLE_READ         - TODO
	 *   PERF_SAMPLE_RAW          - tracepoint fields are handled separately
	 *   PERF_SAMPLE_BRANCH_STACK - TODO
	 *   PERF_SAMPLE_REGS_USER    - TODO
	 *   PERF_SAMPLE_STACK_USER   - TODO
	 */

	if (type & PERF_SAMPLE_IP) {
		ret = value_set_u64_hex(cw, event, "perf_ip", sample->ip);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_TID) {
		ret = value_set_s32(cw, event, "perf_tid", sample->tid);
		if (ret)
			return -1;

		ret = value_set_s32(cw, event, "perf_pid", sample->pid);
		if (ret)
			return -1;
	}

	if ((type & PERF_SAMPLE_ID) ||
	    (type & PERF_SAMPLE_IDENTIFIER)) {
		ret = value_set_u64(cw, event, "perf_id", sample->id);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_STREAM_ID) {
		ret = value_set_u64(cw, event, "perf_stream_id", sample->stream_id);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_PERIOD) {
		ret = value_set_u64(cw, event, "perf_period", sample->period);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_WEIGHT) {
		ret = value_set_u64(cw, event, "perf_weight", sample->weight);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_DATA_SRC) {
		ret = value_set_u64(cw, event, "perf_data_src",
				sample->data_src);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_TRANSACTION) {
		ret = value_set_u64(cw, event, "perf_transaction",
				sample->transaction);
		if (ret)
			return -1;
	}

	return 0;
}

static int ctf_stream__flush(struct ctf_stream *cs)
{
	int err = 0;

	if (cs) {
		err = bt_ctf_stream_flush(cs->stream);
		if (err)
			pr_err("CTF stream %d flush failed\n", cs->cpu);

		pr("Flush stream for cpu %d (%u samples)\n",
		   cs->cpu, cs->count);

		cs->count = 0;
	}

	return err;
}

static struct ctf_stream *ctf_stream__create(struct ctf_writer *cw, int cpu)
{
	struct ctf_stream *cs;
	struct bt_ctf_field *pkt_ctx   = NULL;
	struct bt_ctf_field *cpu_field = NULL;
	struct bt_ctf_stream *stream   = NULL;
	int ret;

	cs = zalloc(sizeof(*cs));
	if (!cs) {
		pr_err("Failed to allocate ctf stream\n");
		return NULL;
	}

	stream = bt_ctf_writer_create_stream(cw->writer, cw->stream_class);
	if (!stream) {
		pr_err("Failed to create CTF stream\n");
		goto out;
	}

	pkt_ctx = bt_ctf_stream_get_packet_context(stream);
	if (!pkt_ctx) {
		pr_err("Failed to obtain packet context\n");
		goto out;
	}

	cpu_field = bt_ctf_field_structure_get_field(pkt_ctx, "cpu_id");
	bt_ctf_field_put(pkt_ctx);
	if (!cpu_field) {
		pr_err("Failed to obtain cpu field\n");
		goto out;
	}

	ret = bt_ctf_field_integer_unsigned_set_value(cpu_field, (u32) cpu);
	if (ret) {
		pr_err("Failed to update CPU number\n");
		goto out;
	}

	bt_ctf_field_put(cpu_field);

	cs->cpu    = cpu;
	cs->stream = stream;
	return cs;

out:
	if (cpu_field)
		bt_ctf_field_put(cpu_field);
	if (stream)
		bt_ctf_stream_put(stream);

	free(cs);
	return NULL;
}

static void ctf_stream__delete(struct ctf_stream *cs)
{
	if (cs) {
		bt_ctf_stream_put(cs->stream);
		free(cs);
	}
}

static struct ctf_stream *ctf_stream(struct ctf_writer *cw, int cpu)
{
	struct ctf_stream *cs = cw->stream[cpu];

	if (!cs) {
		cs = ctf_stream__create(cw, cpu);
		cw->stream[cpu] = cs;
	}

	return cs;
}

static int get_sample_cpu(struct ctf_writer *cw, struct perf_sample *sample,
			  struct evsel *evsel)
{
	int cpu = 0;

	if (evsel->core.attr.sample_type & PERF_SAMPLE_CPU)
		cpu = sample->cpu;

	if (cpu > cw->stream_cnt) {
		pr_err("Event was recorded for CPU %d, limit is at %d.\n",
			cpu, cw->stream_cnt);
		cpu = 0;
	}

	return cpu;
}

#define STREAM_FLUSH_COUNT 100000

/*
 * Currently we have no other way to determine the
 * time for the stream flush other than keep track
 * of the number of events and check it against
 * threshold.
 */
static bool is_flush_needed(struct ctf_stream *cs)
{
	return cs->count >= STREAM_FLUSH_COUNT;
}

/*
 * Whether the samples of @evsel can carry a resolved data type: the
 * consumer needs the data address of the access (the instance identity,
 * without which every instance of a type collapses into the same one) and
 * the CPU the access happened on (a core does not invalidate itself, so it
 * is the cross CPU accesses that make a pair of them false sharing).
 */
static bool data_type_evsel(struct ctf_writer *cw, struct evsel *evsel)
{
	u64 type = evsel->core.attr.sample_type;

	if (!cw->data_type || !(type & PERF_SAMPLE_ADDR))
		return false;

	if (!(type & PERF_SAMPLE_CPU)) {
		pr_warning("'%s' samples no CPU: the data type records need the CPU the access happened on, re-record with --sample-cpu\n",
			   evsel__name(evsel));
		return false;
	}

	return true;
}

/*
 * The id of @dso in the perf_dso_info table, assigning one the first time
 * the DSO shows up and reporting it in @new_dso, so that the caller can
 * publish it before the sample that references it.  Ids start at one: the
 * samples no type was resolved for carry zero, and a consumer that finds no
 * perf_dso_info event for an id falls back to an unknown, unverified DSO.
 */
static int dso_info_id(struct convert *c, struct dso *dso, struct dso **new_dso)
{
	size_t i;

	*new_dso = NULL;

	for (i = 0; i < c->dt_nr_dsos; i++) {
		if (c->dt_dsos[i] == dso)
			return i + 1;
	}

	if ((c->dt_nr_dsos % 16) == 0) {
		struct dso **dsos = realloc(c->dt_dsos,
					    (c->dt_nr_dsos + 16) * sizeof(*dsos));
		if (dsos == NULL) {
			pr_err("Failed to grow the DSO table.\n");
			return -1;
		}
		c->dt_dsos = dsos;
	}

	c->dt_dsos[c->dt_nr_dsos] = dso;
	*new_dso = dso;

	return ++c->dt_nr_dsos;
}

/*
 * The perf_dso_info side event: one per DSO a data type was resolved in,
 * carrying the identity the consumer needs to find the DWARF the type came
 * from and to check that it is analyzing the binary that was profiled --
 * the same (dso, build_id) pair the JSON export of 'perf report -s type'
 * carries.  A name per sample would bloat the stream, so the perf_sample
 * records carry the id this event publishes instead.
 */
static int add_dso_info_event(struct ctf_writer *cw)
{
	struct bt_ctf_event_class *event_class;
	int ret = -1;

	pr("Adding dso_info event\n");
	event_class = bt_ctf_event_class_create("perf_dso_info");
	if (!event_class)
		return -1;

	if (bt_ctf_event_class_add_field(event_class, cw->data.u64, "id") ||
	    bt_ctf_event_class_add_field(event_class, cw->data.string, "long_name") ||
	    bt_ctf_event_class_add_field(event_class, cw->data.string, "build_id")) {
		pr_err("Failed to add the 'perf_dso_info' fields.\n");
		goto err;
	}

	ret = bt_ctf_stream_class_add_event_class(cw->stream_class, event_class);
	if (ret) {
		pr("Failed to add event class 'dso_info' into stream.\n");
		goto err;
	}

	cw->dso_info_class = event_class;
	bt_ctf_event_class_put(event_class);
	return 0;

err:
	bt_ctf_event_class_put(event_class);
	return ret;
}

/* An empty build_id tells the consumer that the DSO has none. */
static int emit_dso_info(struct ctf_writer *cw, struct ctf_stream *cs,
			 struct dso *dso, u64 id, u64 time)
{
	char sbuild_id[SBUILD_ID_SIZE] = "";
	struct bt_ctf_event *event;
	int ret;

	event = bt_ctf_event_create(cw->dso_info_class);
	if (!event) {
		pr_err("Failed to create a perf_dso_info event\n");
		return -1;
	}

	if (dso__has_build_id(dso))
		build_id__snprintf(dso__bid(dso), sbuild_id, sizeof(sbuild_id));

	bt_ctf_clock_set_time(cw->clock, time);

	ret = value_set_u64(cw, event, "id", id);
	if (ret == 0)
		ret = value_set_string(cw, event, "long_name", dso__long_name(dso));
	if (ret == 0)
		ret = value_set_string(cw, event, "build_id", sbuild_id);
	if (ret == 0) {
		cs->count++;
		bt_ctf_stream_append_event(cs->stream, event);
	}

	bt_ctf_event_put(event);
	return ret;
}

/*
 * Resolve the data type @sample accessed and set the perf_sample_* fields
 * with it.  A sample whose type could not be resolved gets an empty type
 * name and no DSO: the trace stays a faithful conversion of perf.data
 * instead of dropping the sample, and the consumer skips the empty ones.
 * The stack operation and stack canary pseudo types are skipped too, they
 * are not accesses to an instance of a type.
 *
 * Returns 0 on success, -1 on error, and the DSO that got a new id in
 * @new_dso (with that id in @new_dso_id) so the caller can publish it right
 * before the sample that references it.
 */
static int add_data_type_values(struct convert *c, struct bt_ctf_event *event,
				struct evsel *evsel, struct perf_sample *sample,
				struct machine *machine, struct dso **new_dso,
				u64 *new_dso_id)
{
	struct ctf_writer *cw = &c->writer;
	struct annotated_data_type *data_type = NULL;
	struct addr_location al;
	const char *type_name = "";
	int offset = 0, dso_id = 0, ret = 0;
	bool is_write = false;

	*new_dso = NULL;
	*new_dso_id = 0;

	addr_location__init(&al);

	if (machine__resolve(machine, &al, sample) < 0)
		pr_debug("data type: cannot resolve the sample at %#" PRIx64 "\n",
			 sample->ip);
	else if (al.map && al.sym) {
		/*
		 * The map, symbol and thread references belong to @al, which
		 * outlives the resolution: nothing in it takes or drops a
		 * reference of its own.
		 */
		struct map_symbol ms = {
			.thread	= al.thread,
			.map	= al.map,
			.sym	= al.sym,
		};

		data_type = annotate_resolve_data_type(&ms, al.addr, al.thread,
						       al.cpumode, evsel,
						       &offset, &is_write,
						       sample->addr);
	}

	if (data_type == &stackop_type || data_type == &canary_type)
		data_type = NULL;

	if (data_type) {
		/*
		 * The direction of the access: a memory sample carries what
		 * the hardware saw in data_src, which is the only reliable
		 * source on the PMUs with a single load/store event (AMD
		 * IBS); the role the operand parser assigned to the memory
		 * operand is the fallback for the samples that say nothing
		 * about it.
		 */
		if (evsel->core.attr.sample_type & PERF_SAMPLE_DATA_SRC) {
			union perf_mem_data_src data_src = {
				.val = sample->data_src,
			};

			if (data_src.mem_op & PERF_MEM_OP_STORE)
				is_write = true;
			else if (data_src.mem_op & PERF_MEM_OP_LOAD)
				is_write = false;
		}

		type_name = data_type->self.type_name;
		dso_id = dso_info_id(c, map__dso(al.map), new_dso);
		if (dso_id < 0) {
			ret = -1;
			goto out;
		}
		*new_dso_id = dso_id;
		c->dt_resolved++;
	} else {
		offset = 0;
		is_write = false;
	}

	/*
	 * With a fixed sampling period the field is in the event class but
	 * add_generic_values() left it alone, as the sample does not carry
	 * it: the period comes from the attr there.
	 */
	if (!(evsel->core.attr.sample_type & PERF_SAMPLE_PERIOD)) {
		ret = value_set_u64(cw, event, "perf_period", sample->period);
		if (ret)
			goto out;
	}

	ret = value_set_string(cw, event, "perf_sample_type", type_name);
	if (ret == 0)
		ret = value_set_u64(cw, event, "perf_sample_type_offset", offset);
	if (ret == 0)
		ret = value_set_u64(cw, event, "perf_sample_is_write", is_write ? 1 : 0);
	if (ret == 0)
		ret = value_set_u64(cw, event, "perf_sample_cpu", sample->cpu);
	if (ret == 0)
		ret = value_set_u64_hex(cw, event, "perf_sample_addr", sample->addr);
	if (ret == 0)
		ret = value_set_u64(cw, event, "perf_sample_dso_id", dso_id);

out:
	addr_location__exit(&al);
	return ret;
}

static int process_sample_event(const struct perf_tool *tool,
				union perf_event *_event,
				struct perf_sample *sample,
				struct machine *machine)
{
	struct convert *c = container_of(tool, struct convert, tool);
	struct evsel *evsel = sample->evsel;
	struct evsel_priv *priv = evsel->priv;
	struct ctf_writer *cw = &c->writer;
	struct ctf_stream *cs;
	struct bt_ctf_event_class *event_class;
	struct bt_ctf_event *event;
	struct dso *new_dso = NULL;
	u64 new_dso_id = 0;
	int ret;
	unsigned long type = evsel->core.attr.sample_type;

	if (WARN_ONCE(!priv, "Failed to setup all events.\n"))
		return 0;

	if (perf_time__ranges_skip_sample(c->ptime_range, c->range_num, sample->time)) {
		++c->skipped;
		return 0;
	}

	event_class = priv->event_class;

	/* update stats */
	c->events_count++;
	c->events_size += _event->header.size;

	pr_time2(sample->time, "sample %" PRIu64 "\n", c->events_count);

	event = bt_ctf_event_create(event_class);
	if (!event) {
		pr_err("Failed to create an CTF event\n");
		return -1;
	}

	bt_ctf_clock_set_time(cw->clock, sample->time);

	ret = add_generic_values(cw, event, evsel, sample);
	if (ret)
		return -1;

	if (priv->data_type) {
		ret = add_data_type_values(c, event, evsel, sample, machine,
					   &new_dso, &new_dso_id);
		if (ret)
			return -1;
	}

	if (evsel->core.attr.type == PERF_TYPE_TRACEPOINT) {
		ret = add_tracepoint_values(cw, event_class, event,
					    evsel, sample);
		if (ret)
			return -1;
	}

	if (type & PERF_SAMPLE_CALLCHAIN) {
		ret = add_callchain_output_values(event_class,
				event, sample->callchain);
		if (ret)
			return -1;
	}

	if (evsel__is_bpf_output(evsel)) {
		ret = add_bpf_output_values(event_class, event, sample);
		if (ret)
			return -1;
	}

	cs = ctf_stream(cw, get_sample_cpu(cw, sample, evsel));
	if (cs) {
		if (is_flush_needed(cs))
			ctf_stream__flush(cs);

		/*
		 * The identity of the DSO this sample's type was resolved in
		 * goes out right before the sample referencing it, into the
		 * same stream, so that a consumer sees the side event before
		 * the id it carries.
		 */
		if (new_dso && emit_dso_info(cw, cs, new_dso, new_dso_id,
					     sample->time))
			pr_warning("Failed to write the perf_dso_info event for %s\n",
				   dso__long_name(new_dso));

		cs->count++;
		bt_ctf_stream_append_event(cs->stream, event);
	}

	bt_ctf_event_put(event);
	return cs ? 0 : -1;
}

#define __NON_SAMPLE_SET_FIELD(_name, _type, _field) 	\
do {							\
	ret = value_set_##_type(cw, event, #_field, _event->_name._field);\
	if (ret)					\
		return -1;				\
} while(0)

#define __FUNC_PROCESS_NON_SAMPLE(_name, body) 	\
static int process_##_name##_event(const struct perf_tool *tool,	\
				   union perf_event *_event,	\
				   struct perf_sample *sample,	\
				   struct machine *machine)	\
{								\
	struct convert *c = container_of(tool, struct convert, tool);\
	struct ctf_writer *cw = &c->writer;			\
	struct bt_ctf_event_class *event_class = cw->_name##_class;\
	struct bt_ctf_event *event;				\
	struct ctf_stream *cs;					\
	int ret;						\
								\
	c->non_sample_count++;					\
	c->events_size += _event->header.size;			\
	event = bt_ctf_event_create(event_class);		\
	if (!event) {						\
		pr_err("Failed to create an CTF event\n");	\
		return -1;					\
	}							\
								\
	bt_ctf_clock_set_time(cw->clock, sample->time);		\
	body							\
	cs = ctf_stream(cw, 0);					\
	if (cs) {						\
		if (is_flush_needed(cs))			\
			ctf_stream__flush(cs);			\
								\
		cs->count++;					\
		bt_ctf_stream_append_event(cs->stream, event);	\
	}							\
	bt_ctf_event_put(event);				\
								\
	return perf_event__process_##_name(tool, _event, sample, machine);\
}

__FUNC_PROCESS_NON_SAMPLE(comm,
	__NON_SAMPLE_SET_FIELD(comm, u32, pid);
	__NON_SAMPLE_SET_FIELD(comm, u32, tid);
	__NON_SAMPLE_SET_FIELD(comm, string, comm);
)
__FUNC_PROCESS_NON_SAMPLE(fork,
	__NON_SAMPLE_SET_FIELD(fork, u32, pid);
	__NON_SAMPLE_SET_FIELD(fork, u32, ppid);
	__NON_SAMPLE_SET_FIELD(fork, u32, tid);
	__NON_SAMPLE_SET_FIELD(fork, u32, ptid);
	__NON_SAMPLE_SET_FIELD(fork, u64, time);
)

__FUNC_PROCESS_NON_SAMPLE(exit,
	__NON_SAMPLE_SET_FIELD(fork, u32, pid);
	__NON_SAMPLE_SET_FIELD(fork, u32, ppid);
	__NON_SAMPLE_SET_FIELD(fork, u32, tid);
	__NON_SAMPLE_SET_FIELD(fork, u32, ptid);
	__NON_SAMPLE_SET_FIELD(fork, u64, time);
)
__FUNC_PROCESS_NON_SAMPLE(mmap,
	__NON_SAMPLE_SET_FIELD(mmap, u32, pid);
	__NON_SAMPLE_SET_FIELD(mmap, u32, tid);
	__NON_SAMPLE_SET_FIELD(mmap, u64_hex, start);
	__NON_SAMPLE_SET_FIELD(mmap, string, filename);
)
__FUNC_PROCESS_NON_SAMPLE(mmap2,
	__NON_SAMPLE_SET_FIELD(mmap2, u32, pid);
	__NON_SAMPLE_SET_FIELD(mmap2, u32, tid);
	__NON_SAMPLE_SET_FIELD(mmap2, u64_hex, start);
	__NON_SAMPLE_SET_FIELD(mmap2, string, filename);
)
#undef __NON_SAMPLE_SET_FIELD
#undef __FUNC_PROCESS_NON_SAMPLE

/* If dup < 0, add a prefix. Else, add _dupl_X suffix. */
static char *change_name(char *name, char *orig_name, int dup)
{
	char *new_name = NULL;
	size_t len;

	if (!name)
		name = orig_name;

	if (dup >= 10)
		goto out;
	/*
	 * Add '_' prefix to potential keywork.  According to
	 * Mathieu Desnoyers (https://lore.kernel.org/lkml/1074266107.40857.1422045946295.JavaMail.zimbra@efficios.com),
	 * further CTF spec updating may require us to use '$'.
	 */
	if (dup < 0)
		len = strlen(name) + sizeof("_");
	else
		len = strlen(orig_name) + sizeof("_dupl_X");

	new_name = malloc(len);
	if (!new_name)
		goto out;

	if (dup < 0)
		snprintf(new_name, len, "_%s", name);
	else
		snprintf(new_name, len, "%s_dupl_%d", orig_name, dup);

out:
	if (name != orig_name)
		free(name);
	return new_name;
}

static int event_class_add_field(struct bt_ctf_event_class *event_class,
		struct bt_ctf_field_type *type,
		struct tep_format_field *field)
{
	struct bt_ctf_field_type *t = NULL;
	char *name;
	int dup = 1;
	int ret;

	/* alias was already assigned */
	if (field->alias != field->name)
		return bt_ctf_event_class_add_field(event_class, type,
				(char *)field->alias);

	name = field->name;

	/* If 'name' is a keywork, add prefix. */
	if (bt_ctf_validate_identifier(name))
		name = change_name(name, field->name, -1);

	if (!name) {
		pr_err("Failed to fix invalid identifier.");
		return -1;
	}
	while ((t = bt_ctf_event_class_get_field_by_name(event_class, name))) {
		bt_ctf_field_type_put(t);
		name = change_name(name, field->name, dup++);
		if (!name) {
			pr_err("Failed to create dup name for '%s'\n", field->name);
			return -1;
		}
	}

	ret = bt_ctf_event_class_add_field(event_class, type, name);
	if (!ret)
		field->alias = name;

	return ret;
}

static int add_tracepoint_fields_types(struct ctf_writer *cw,
				       struct tep_format_field *fields,
				       struct bt_ctf_event_class *event_class)
{
	struct tep_format_field *field;
	int ret;

	for (field = fields; field; field = field->next) {
		struct bt_ctf_field_type *type;
		unsigned long flags = field->flags;

		pr2("  field '%s'\n", field->name);

		type = get_tracepoint_field_type(cw, field);
		if (!type)
			return -1;

		/*
		 * A string is an array of chars. For this we use the string
		 * type and don't care that it is an array. What we don't
		 * support is an array of strings.
		 */
		if (flags & TEP_FIELD_IS_STRING)
			flags &= ~TEP_FIELD_IS_ARRAY;

		if (flags & TEP_FIELD_IS_ARRAY)
			type = bt_ctf_field_type_array_create(type, field->arraylen);

		ret = event_class_add_field(event_class, type, field);

		if (flags & TEP_FIELD_IS_ARRAY)
			bt_ctf_field_type_put(type);

		if (ret) {
			pr_err("Failed to add field '%s': %d\n",
					field->name, ret);
			return -1;
		}
	}

	return 0;
}

static int add_tracepoint_types(struct ctf_writer *cw,
				struct evsel *evsel,
				struct bt_ctf_event_class *class)
{
	const struct tep_event *tp_format = evsel__tp_format(evsel);
	struct tep_format_field *common_fields = tp_format ? tp_format->format.common_fields : NULL;
	struct tep_format_field *fields        = tp_format ? tp_format->format.fields : NULL;
	int ret;

	ret = add_tracepoint_fields_types(cw, common_fields, class);
	if (!ret)
		ret = add_tracepoint_fields_types(cw, fields, class);

	return ret;
}

static int add_bpf_output_types(struct ctf_writer *cw,
				struct bt_ctf_event_class *class)
{
	struct bt_ctf_field_type *len_type = cw->data.u32;
	struct bt_ctf_field_type *seq_base_type = cw->data.u32_hex;
	struct bt_ctf_field_type *seq_type;
	int ret;

	ret = bt_ctf_event_class_add_field(class, len_type, "raw_len");
	if (ret)
		return ret;

	seq_type = bt_ctf_field_type_sequence_create(seq_base_type, "raw_len");
	if (!seq_type)
		return -1;

	return bt_ctf_event_class_add_field(class, seq_type, "raw_data");
}

static int add_generic_types(struct ctf_writer *cw, struct evsel *evsel,
			     struct bt_ctf_event_class *event_class,
			     bool data_type)
{
	u64 type = evsel->core.attr.sample_type;

	/*
	 * missing:
	 *   PERF_SAMPLE_TIME         - not needed as we have it in
	 *                              ctf event header
	 *   PERF_SAMPLE_READ         - TODO
	 *   PERF_SAMPLE_CALLCHAIN    - TODO
	 *   PERF_SAMPLE_RAW          - tracepoint fields and BPF output
	 *                              are handled separately
	 *   PERF_SAMPLE_BRANCH_STACK - TODO
	 *   PERF_SAMPLE_REGS_USER    - TODO
	 *   PERF_SAMPLE_STACK_USER   - TODO
	 */

#define ADD_FIELD(cl, t, n)						\
	do {								\
		pr2("  field '%s'\n", n);				\
		if (bt_ctf_event_class_add_field(cl, t, n)) {		\
			pr_err("Failed to add field '%s';\n", n);	\
			return -1;					\
		}							\
	} while (0)

	if (type & PERF_SAMPLE_IP)
		ADD_FIELD(event_class, cw->data.u64_hex, "perf_ip");

	if (type & PERF_SAMPLE_TID) {
		ADD_FIELD(event_class, cw->data.s32, "perf_tid");
		ADD_FIELD(event_class, cw->data.s32, "perf_pid");
	}

	if ((type & PERF_SAMPLE_ID) ||
	    (type & PERF_SAMPLE_IDENTIFIER))
		ADD_FIELD(event_class, cw->data.u64, "perf_id");

	if (type & PERF_SAMPLE_STREAM_ID)
		ADD_FIELD(event_class, cw->data.u64, "perf_stream_id");

	/*
	 * A fixed sampling period ('perf record -c') is not carried by each
	 * sample, perf_evsel__parse_sample() takes it from the attr instead.
	 * The data type records want it anyway, so that the consumer summing
	 * the per sample periods gets the totals the aggregate histograms of
	 * 'perf report -s type' carry.
	 */
	if ((type & PERF_SAMPLE_PERIOD) || data_type)
		ADD_FIELD(event_class, cw->data.u64, "perf_period");

	if (type & PERF_SAMPLE_WEIGHT)
		ADD_FIELD(event_class, cw->data.u64, "perf_weight");

	if (type & PERF_SAMPLE_DATA_SRC)
		ADD_FIELD(event_class, cw->data.u64, "perf_data_src");

	if (type & PERF_SAMPLE_TRANSACTION)
		ADD_FIELD(event_class, cw->data.u64, "perf_transaction");

	if (data_type) {
		/*
		 * The data type this memory sample accessed, resolved from
		 * the instruction's debug info: one record per sample, so
		 * that a consumer gets the per access timestamp, CPU, data
		 * address and direction that the collapsed histograms of
		 * 'perf report -s type' cannot carry.  pahole reads these to
		 * tell true from false sharing and to suggest cacheline
		 * groups, see its --perf-data-type option.
		 */
		ADD_FIELD(event_class, cw->data.string, "perf_sample_type");
		ADD_FIELD(event_class, cw->data.u64, "perf_sample_type_offset");
		ADD_FIELD(event_class, cw->data.u64, "perf_sample_is_write");
		ADD_FIELD(event_class, cw->data.u64, "perf_sample_cpu");
		ADD_FIELD(event_class, cw->data.u64_hex, "perf_sample_addr");
		ADD_FIELD(event_class, cw->data.u64, "perf_sample_dso_id");
	}

	if (type & PERF_SAMPLE_CALLCHAIN) {
		ADD_FIELD(event_class, cw->data.u32, "perf_callchain_size");
		ADD_FIELD(event_class,
			bt_ctf_field_type_sequence_create(
				cw->data.u64_hex, "perf_callchain_size"),
			"perf_callchain");
	}

#undef ADD_FIELD
	return 0;
}

static int add_event(struct ctf_writer *cw, struct evsel *evsel)
{
	struct bt_ctf_event_class *event_class;
	struct evsel_priv *priv;
	const char *name = evsel__name(evsel);
	bool data_type = data_type_evsel(cw, evsel);
	int ret;

	if (evsel->priv) {
		pr_err("Error: attempt to add already added event %s\n", name);
		return -1;
	}
	pr("Adding event '%s' (type %d)\n", name, evsel->core.attr.type);

	event_class = bt_ctf_event_class_create(name);
	if (!event_class)
		return -1;

	ret = add_generic_types(cw, evsel, event_class, data_type);
	if (ret)
		goto err;

	if (evsel->core.attr.type == PERF_TYPE_TRACEPOINT) {
		ret = add_tracepoint_types(cw, evsel, event_class);
		if (ret)
			goto err;
	}

	if (evsel__is_bpf_output(evsel)) {
		ret = add_bpf_output_types(cw, event_class);
		if (ret)
			goto err;
	}

	ret = bt_ctf_stream_class_add_event_class(cw->stream_class, event_class);
	if (ret) {
		pr("Failed to add event class into stream.\n");
		goto err;
	}

	priv = malloc(sizeof(*priv));
	if (!priv)
		goto err;

	priv->event_class = event_class;
	priv->data_type   = data_type;
	evsel->priv       = priv;
	return 0;

err:
	bt_ctf_event_class_put(event_class);
	pr_err("Failed to add event '%s'.\n", name);
	return -1;
}

enum setup_events_type {
	SETUP_EVENTS_ALL,
	SETUP_EVENTS_NOT_TRACEPOINT,
	SETUP_EVENTS_TRACEPOINT_ONLY,
};

static int setup_events(struct ctf_writer *cw, struct perf_session *session,
			enum setup_events_type type)
{
	struct evlist *evlist = session->evlist;
	struct evsel *evsel;
	int ret;

	evlist__for_each_entry(evlist, evsel) {
		bool is_tracepoint = evsel->core.attr.type == PERF_TYPE_TRACEPOINT;

		if (is_tracepoint && type == SETUP_EVENTS_NOT_TRACEPOINT)
			continue;

		if (!is_tracepoint && type == SETUP_EVENTS_TRACEPOINT_ONLY)
			continue;

		ret = add_event(cw, evsel);
		if (ret)
			return ret;
	}
	return 0;
}

#define __NON_SAMPLE_ADD_FIELD(t, n)						\
	do {							\
		pr2("  field '%s'\n", #n);			\
		if (bt_ctf_event_class_add_field(event_class, cw->data.t, #n)) {\
			pr_err("Failed to add field '%s';\n", #n);\
			return -1;				\
		}						\
	} while(0)

#define __FUNC_ADD_NON_SAMPLE_EVENT_CLASS(_name, body) 		\
static int add_##_name##_event(struct ctf_writer *cw)		\
{								\
	struct bt_ctf_event_class *event_class;			\
	int ret;						\
								\
	pr("Adding "#_name" event\n");				\
	event_class = bt_ctf_event_class_create("perf_" #_name);\
	if (!event_class)					\
		return -1;					\
	body							\
								\
	ret = bt_ctf_stream_class_add_event_class(cw->stream_class, event_class);\
	if (ret) {						\
		pr("Failed to add event class '"#_name"' into stream.\n");\
		return ret;					\
	}							\
								\
	cw->_name##_class = event_class;			\
	bt_ctf_event_class_put(event_class);			\
	return 0;						\
}

__FUNC_ADD_NON_SAMPLE_EVENT_CLASS(comm,
	__NON_SAMPLE_ADD_FIELD(u32, pid);
	__NON_SAMPLE_ADD_FIELD(u32, tid);
	__NON_SAMPLE_ADD_FIELD(string, comm);
)

__FUNC_ADD_NON_SAMPLE_EVENT_CLASS(fork,
	__NON_SAMPLE_ADD_FIELD(u32, pid);
	__NON_SAMPLE_ADD_FIELD(u32, ppid);
	__NON_SAMPLE_ADD_FIELD(u32, tid);
	__NON_SAMPLE_ADD_FIELD(u32, ptid);
	__NON_SAMPLE_ADD_FIELD(u64, time);
)

__FUNC_ADD_NON_SAMPLE_EVENT_CLASS(exit,
	__NON_SAMPLE_ADD_FIELD(u32, pid);
	__NON_SAMPLE_ADD_FIELD(u32, ppid);
	__NON_SAMPLE_ADD_FIELD(u32, tid);
	__NON_SAMPLE_ADD_FIELD(u32, ptid);
	__NON_SAMPLE_ADD_FIELD(u64, time);
)

__FUNC_ADD_NON_SAMPLE_EVENT_CLASS(mmap,
	__NON_SAMPLE_ADD_FIELD(u32, pid);
	__NON_SAMPLE_ADD_FIELD(u32, tid);
	__NON_SAMPLE_ADD_FIELD(u64_hex, start);
	__NON_SAMPLE_ADD_FIELD(string, filename);
)

__FUNC_ADD_NON_SAMPLE_EVENT_CLASS(mmap2,
	__NON_SAMPLE_ADD_FIELD(u32, pid);
	__NON_SAMPLE_ADD_FIELD(u32, tid);
	__NON_SAMPLE_ADD_FIELD(u64_hex, start);
	__NON_SAMPLE_ADD_FIELD(string, filename);
)
#undef __NON_SAMPLE_ADD_FIELD
#undef __FUNC_ADD_NON_SAMPLE_EVENT_CLASS

static int setup_non_sample_events(struct ctf_writer *cw,
				   struct perf_session *session __maybe_unused)
{
	int ret;

	ret = add_comm_event(cw);
	if (ret)
		return ret;
	ret = add_exit_event(cw);
	if (ret)
		return ret;
	ret = add_fork_event(cw);
	if (ret)
		return ret;
	ret = add_mmap_event(cw);
	if (ret)
		return ret;
	ret = add_mmap2_event(cw);
	if (ret)
		return ret;
	return 0;
}

static void cleanup_events(struct perf_session *session)
{
	struct evlist *evlist = session->evlist;
	struct evsel *evsel;

	evlist__for_each_entry(evlist, evsel) {
		struct evsel_priv *priv;

		priv = evsel->priv;
		if (priv)
			bt_ctf_event_class_put(priv->event_class);
		zfree(&evsel->priv);
	}

	evlist__put(evlist);
	session->evlist = NULL;
}

static int setup_streams(struct ctf_writer *cw, struct perf_session *session)
{
	struct ctf_stream **stream;
	struct perf_env *env = perf_session__env(session);
	int ncpus;

	/*
	 * Try to get the number of cpus used in the data file,
	 * if not present fallback to the MAX_CPUS.
	 */
	ncpus = env->nr_cpus_avail ?: MAX_CPUS;

	stream = calloc(ncpus, sizeof(*stream));
	if (!stream) {
		pr_err("Failed to allocate streams.\n");
		return -ENOMEM;
	}

	cw->stream     = stream;
	cw->stream_cnt = ncpus;
	return 0;
}

static void free_streams(struct ctf_writer *cw)
{
	int cpu;

	for (cpu = 0; cpu < cw->stream_cnt; cpu++)
		ctf_stream__delete(cw->stream[cpu]);

	zfree(&cw->stream);
}

static int ctf_writer__setup_env(struct ctf_writer *cw,
				 struct perf_session *session)
{
	struct perf_env *env = perf_session__env(session);
	struct bt_ctf_writer *writer = cw->writer;

#define ADD(__n, __v)							\
do {									\
	if (__v && bt_ctf_writer_add_environment_field(writer, __n, __v))	\
		return -1;						\
} while (0)

	ADD("host",    env->hostname);
	ADD("sysname", "Linux");
	ADD("release", perf_env__os_release(env));
	ADD("version", env->version);
	ADD("machine", env->arch);
	ADD("domain", "kernel");
	ADD("tracer_name", "perf");

#undef ADD
	return 0;
}

static int process_feature_event(const struct perf_tool *tool,
				 struct perf_session *session,
				 union perf_event *event)
{
	struct convert *c = container_of(tool, struct convert, tool);
	struct ctf_writer *cw = &c->writer;
	struct perf_record_header_feature *fe = &event->feat;
	int ret = perf_event__process_feature(tool, session, event);

	if (ret)
		return ret;

	switch (fe->feat_id) {
	case HEADER_EVENT_DESC:
		/*
		 * In non-pipe mode (not here) the evsels combine the desc with
		 * the perf_event_attr when it is parsed. In pipe mode the
		 * perf_event_attr events appear first and then the event desc
		 * feature events that set the names appear after. Once we have
		 * the full evsel data we can generate the babeltrace
		 * events. For tracepoint events we still don't have the tracing
		 * data and so need to wait until the tracing data event to add
		 * those events to babeltrace.
		 */
		return setup_events(cw, session, SETUP_EVENTS_NOT_TRACEPOINT);
	case HEADER_HOSTNAME:
		if (session->header.env.hostname) {
			return bt_ctf_writer_add_environment_field(cw->writer, "host",
								   session->header.env.hostname);
		}
		break;
	case HEADER_OSRELEASE:
		if (session->header.env.os_release) {
			return bt_ctf_writer_add_environment_field(cw->writer, "release",
								   session->header.env.os_release);
		}
		break;
	case HEADER_VERSION:
		if (session->header.env.version) {
			return bt_ctf_writer_add_environment_field(cw->writer, "version",
								   session->header.env.version);
		}
		break;
	case HEADER_ARCH:
		if (session->header.env.arch) {
			return bt_ctf_writer_add_environment_field(cw->writer, "machine",
								   session->header.env.arch);
		}
		break;
	default:
		break;
	}
	return 0;
}

static int process_tracing_data(const struct perf_tool *tool,
				struct perf_session *session,
				union perf_event *event)
{
	struct convert *c = container_of(tool, struct convert, tool);
	struct ctf_writer *cw = &c->writer;
	int ret;

	ret = perf_event__process_tracing_data(tool, session, event);
	if (ret < 0)
		return ret;

	/*
	 * Now the attr was set up by the attr event, the name by the feature
	 * event desc event and the tracepoint data set up above, the tracepoint
	 * babeltrace events can be added.
	 */
	return setup_events(cw, session, SETUP_EVENTS_TRACEPOINT_ONLY);
}

static int ctf_writer__setup_clock(struct ctf_writer *cw,
				   struct perf_session *session,
				   bool tod)
{
	struct bt_ctf_clock *clock = cw->clock;
	const char *desc = "perf clock";
	int64_t offset = 0;

	if (tod) {
		struct perf_env *env = perf_session__env(session);

		if (!env->clock.enabled) {
			pr_err("Can't provide --tod time, missing clock data. "
			       "Please record with -k/--clockid option.\n");
			return -1;
		}

		desc   = clockid_name(env->clock.clockid);
		offset = env->clock.tod_ns - env->clock.clockid_ns;
	}

#define SET(__n, __v)				\
do {						\
	if (bt_ctf_clock_set_##__n(clock, __v))	\
		return -1;			\
} while (0)

	SET(frequency,   1000000000);
	SET(offset,      offset);
	SET(description, desc);
	SET(precision,   10);
	SET(is_absolute, 0);

#undef SET
	return 0;
}

static struct bt_ctf_field_type *create_int_type(int size, bool sign, bool hex)
{
	struct bt_ctf_field_type *type;

	type = bt_ctf_field_type_integer_create(size);
	if (!type)
		return NULL;

	if (sign &&
	    bt_ctf_field_type_integer_set_signed(type, 1))
		goto err;

	if (hex &&
	    bt_ctf_field_type_integer_set_base(type, BT_CTF_INTEGER_BASE_HEXADECIMAL))
		goto err;

#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
	bt_ctf_field_type_set_byte_order(type, BT_CTF_BYTE_ORDER_BIG_ENDIAN);
#else
	bt_ctf_field_type_set_byte_order(type, BT_CTF_BYTE_ORDER_LITTLE_ENDIAN);
#endif

	pr2("Created type: INTEGER %d-bit %ssigned %s\n",
	    size, sign ? "un" : "", hex ? "hex" : "");
	return type;

err:
	bt_ctf_field_type_put(type);
	return NULL;
}

static void ctf_writer__cleanup_data(struct ctf_writer *cw)
{
	unsigned int i;

	for (i = 0; i < ARRAY_SIZE(cw->data.array); i++)
		bt_ctf_field_type_put(cw->data.array[i]);
}

static int ctf_writer__init_data(struct ctf_writer *cw)
{
#define CREATE_INT_TYPE(type, size, sign, hex)		\
do {							\
	(type) = create_int_type(size, sign, hex);	\
	if (!(type))					\
		goto err;				\
} while (0)

	CREATE_INT_TYPE(cw->data.s64, 64, true,  false);
	CREATE_INT_TYPE(cw->data.u64, 64, false, false);
	CREATE_INT_TYPE(cw->data.s32, 32, true,  false);
	CREATE_INT_TYPE(cw->data.u32, 32, false, false);
	CREATE_INT_TYPE(cw->data.u32_hex, 32, false, true);
	CREATE_INT_TYPE(cw->data.u64_hex, 64, false, true);

	cw->data.string  = bt_ctf_field_type_string_create();
	if (cw->data.string)
		return 0;

err:
	ctf_writer__cleanup_data(cw);
	pr_err("Failed to create data types.\n");
	return -1;
}

static void ctf_writer__cleanup(struct ctf_writer *cw)
{
	ctf_writer__cleanup_data(cw);

	bt_ctf_clock_put(cw->clock);
	free_streams(cw);
	bt_ctf_stream_class_put(cw->stream_class);
	bt_ctf_writer_put(cw->writer);

	/* and NULL all the pointers */
	memset(cw, 0, sizeof(*cw));
}

static int ctf_writer__init(struct ctf_writer *cw, const char *path,
			    struct perf_session *session, bool tod)
{
	struct bt_ctf_writer		*writer;
	struct bt_ctf_stream_class	*stream_class;
	struct bt_ctf_clock		*clock;
	struct bt_ctf_field_type	*pkt_ctx_type;
	int				ret;

	/* CTF writer */
	writer = bt_ctf_writer_create(path);
	if (!writer)
		goto err;

	cw->writer = writer;

	/* CTF clock */
	clock = bt_ctf_clock_create("perf_clock");
	if (!clock) {
		pr("Failed to create CTF clock.\n");
		goto err_cleanup;
	}

	cw->clock = clock;

	if (ctf_writer__setup_clock(cw, session, tod)) {
		pr("Failed to setup CTF clock.\n");
		goto err_cleanup;
	}

	/* CTF stream class */
	stream_class = bt_ctf_stream_class_create("perf_stream");
	if (!stream_class) {
		pr("Failed to create CTF stream class.\n");
		goto err_cleanup;
	}

	cw->stream_class = stream_class;

	/* CTF clock stream setup */
	if (bt_ctf_stream_class_set_clock(stream_class, clock)) {
		pr("Failed to assign CTF clock to stream class.\n");
		goto err_cleanup;
	}

	if (ctf_writer__init_data(cw))
		goto err_cleanup;

	/* Add cpu_id for packet context */
	pkt_ctx_type = bt_ctf_stream_class_get_packet_context_type(stream_class);
	if (!pkt_ctx_type)
		goto err_cleanup;

	ret = bt_ctf_field_type_structure_add_field(pkt_ctx_type, cw->data.u32, "cpu_id");
	bt_ctf_field_type_put(pkt_ctx_type);
	if (ret)
		goto err_cleanup;

	/* CTF clock writer setup */
	if (bt_ctf_writer_add_clock(writer, clock)) {
		pr("Failed to assign CTF clock to writer.\n");
		goto err_cleanup;
	}

	return 0;

err_cleanup:
	ctf_writer__cleanup(cw);
err:
	pr_err("Failed to setup CTF writer.\n");
	return -1;
}

static int ctf_writer__flush_streams(struct ctf_writer *cw)
{
	int cpu, ret = 0;

	for (cpu = 0; cpu < cw->stream_cnt && !ret; cpu++)
		ret = ctf_stream__flush(cw->stream[cpu]);

	return ret;
}

static int convert__config(const char *var, const char *value, void *cb)
{
	struct convert *c = cb;

	if (!strcmp(var, "convert.queue-size"))
		return perf_config_u64(&c->queue_size, var, value);

	return 0;
}

int bt_convert__perf2ctf(const char *input, const char *path,
			 struct perf_data_convert_opts *opts)
{
	struct perf_session *session;
	struct perf_data data = {
		.path	   = input,
		.mode      = PERF_DATA_MODE_READ,
		.force     = opts->force,
	};
	struct convert c = {};
	struct ctf_writer *cw = &c.writer;
	int err;

	perf_tool__init(&c.tool, /*ordered_events=*/true);
	c.tool.sample          = process_sample_event;
	c.tool.mmap            = perf_event__process_mmap;
	c.tool.mmap2           = perf_event__process_mmap2;
	c.tool.comm            = perf_event__process_comm;
	c.tool.exit            = perf_event__process_exit;
	c.tool.fork            = perf_event__process_fork;
	c.tool.lost            = perf_event__process_lost;
	c.tool.tracing_data    = process_tracing_data;
	c.tool.build_id        = perf_event__process_build_id;
	c.tool.namespaces      = perf_event__process_namespaces;
	c.tool.finished_round  = perf_event__process_finished_round;
	c.tool.attr            = perf_event__process_attr;
	c.tool.feature         = process_feature_event;
	c.tool.ordering_requires_timestamps = true;

	if (opts->all) {
		c.tool.comm = process_comm_event;
		c.tool.exit = process_exit_event;
		c.tool.fork = process_fork_event;
		c.tool.mmap = process_mmap_event;
		c.tool.mmap2 = process_mmap2_event;
	}

	err = perf_config(convert__config, &c);
	if (err)
		return err;

	if (opts->data_type) {
#ifndef HAVE_LIBDW_SUPPORT
		pr_err("Error: Data type profiling is disabled due to missing DWARF support\n");
		return -EINVAL;
#endif
		/*
		 * Resolving the data type of a sample disassembles the
		 * instruction that accessed memory, so the annotation
		 * machinery is set up the way 'perf report -s type' does it.
		 * The source lines are of no use here, only the operands.
		 */
		annotation_options__init();
		annotate_opts.annotate_src = false;
	}

	err = -1;
	/* perf.data session */
	session = perf_session__new(&data, &c.tool);
	if (IS_ERR(session))
		return PTR_ERR(session);

	if (opts->data_type) {
		/*
		 * Reserving the per symbol annotation space has to happen
		 * before symbol__init(), which freezes the priv size, and
		 * the disassemblers have to be picked before the first
		 * symbol is annotated.
		 */
		if (symbol__annotation_init() < 0)
			goto free_session;

		annotation_config__init();

		if (symbol__init(perf_session__env(session)) < 0)
			goto free_session;
	}

	if (opts->time_str) {
		err = perf_time__parse_for_ranges(opts->time_str, session,
						  &c.ptime_range,
						  &c.range_size,
						  &c.range_num);
		if (err < 0)
			goto free_session;
	}

	/* CTF writer */
	if (ctf_writer__init(cw, path, session, opts->tod))
		goto free_session;

	/* Before setup_events(): it is what decides the event class fields */
	cw->data_type = opts->data_type;

	if (c.queue_size) {
		ordered_events__set_alloc_size(&session->ordered_events,
					       c.queue_size);
	}

	/* CTF writer env/clock setup  */
	if (ctf_writer__setup_env(cw, session))
		goto free_writer;

	/*
	 * CTF events setup. Note, in pipe mode no events exist yet (they come
	 * in via header feature events) and so this does nothing.
	 */
	if (setup_events(cw, session, SETUP_EVENTS_ALL))
		goto free_writer;

	if (opts->all && setup_non_sample_events(cw, session))
		goto free_writer;

	if (cw->data_type && add_dso_info_event(cw))
		goto free_writer;

	if (setup_streams(cw, session))
		goto free_writer;

	err = perf_session__process_events(session);
	if (!err)
		err = ctf_writer__flush_streams(cw);
	else
		pr_err("Error during conversion.\n");

	fprintf(stderr,	"[ perf data convert: Converted '%s' into CTF data '%s' ]\n",
		data.path, path);

	fprintf(stderr,	"[ perf data convert: Converted and wrote %.3f MB (%" PRIu64 " samples",
		(double) c.events_size / 1024.0 / 1024.0,
		c.events_count);

	if (!c.non_sample_count)
		fprintf(stderr, ") ]\n");
	else
		fprintf(stderr, ", %" PRIu64 " non-samples) ]\n", c.non_sample_count);

	if (c.skipped) {
		fprintf(stderr,	"[ perf data convert: Skipped %" PRIu64 " samples ]\n",
			c.skipped);
	}

	if (cw->data_type) {
		fprintf(stderr, "[ perf data convert: Resolved the data type of %" PRIu64 " samples in %zu DSOs ]\n",
			c.dt_resolved, c.dt_nr_dsos);

		c.dt_bad_addr = ann_data_stat.bad_addr;
		if (c.dt_bad_addr)
			fprintf(stderr, "[ perf data convert: Skipped %" PRIu64 " samples whose data address is outside the type the recorded IP resolves to, see perf-data(1) ]\n",
				c.dt_bad_addr);

		if (!c.dt_resolved)
			pr_warning("No data type was resolved: the samples need the data address ('perf mem record', or 'perf record -d --sample-cpu') and the binaries need debug info\n");
	}

	if (c.ptime_range)
		zfree(&c.ptime_range);

	zfree(&c.dt_dsos);

	cleanup_events(session);
	perf_session__delete(session);
	ctf_writer__cleanup(cw);

	return err;

free_writer:
	ctf_writer__cleanup(cw);
free_session:
	if (c.ptime_range)
		zfree(&c.ptime_range);

	zfree(&c.dt_dsos);

	perf_session__delete(session);
	pr_err("Error during conversion setup.\n");
	return err;
}
