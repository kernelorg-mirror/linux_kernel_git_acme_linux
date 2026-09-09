/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Convert sample address to data type using DWARF debug info.
 *
 * Written by Namhyung Kim <namhyung@kernel.org>
 */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <inttypes.h>
#include <sys/stat.h>
#include <time.h>
#include <linux/zalloc.h>

#include "annotate.h"
#include "annotate-data.h"
#include "debuginfo.h"
#include "debug.h"
#include "dso.h"
#include "session.h"
#include "machine.h"
#include "cacheline.h"
#include "header.h"
#include "dwarf-regs.h"
#include "evsel.h"
#include "evlist.h"
#include "map.h"
#include "map_symbol.h"
#include "sort.h"
#include "strbuf.h"
#include "symbol.h"
#include "symbol_conf.h"
#include "thread.h"

/* register number of the stack pointer */
#define X86_REG_SP 7

static void delete_var_types(struct die_var_type *var_types);

#define pr_debug_dtp(fmt, ...)					\
do {								\
	if (debug_type_profile)					\
		pr_info(fmt, ##__VA_ARGS__);			\
	else							\
		pr_debug3(fmt, ##__VA_ARGS__);			\
} while (0)

void pr_debug_type_name(Dwarf_Die *die, enum type_state_kind kind)
{
	struct strbuf sb;
	char *str;
	Dwarf_Word size = 0;

	if (!debug_type_profile && verbose < 3)
		return;

	switch (kind) {
	case TSR_KIND_INVALID:
		pr_info("\n");
		return;
	case TSR_KIND_PERCPU_BASE:
		pr_info(" percpu base\n");
		return;
	case TSR_KIND_CONST:
		pr_info(" constant\n");
		return;
	case TSR_KIND_PERCPU_POINTER:
		pr_info(" percpu pointer");
		/* it also prints the type info */
		break;
	case TSR_KIND_POINTER:
		pr_info(" pointer");
		/* it also prints the type info */
		break;
	case TSR_KIND_CANARY:
		pr_info(" stack canary\n");
		return;
	case TSR_KIND_TYPE:
	default:
		break;
	}

	if (dwarf_aggregate_size(die, &size) != 0)
		size = 0;

	strbuf_init(&sb, 32);
	die_get_typename_from_type(die, &sb);
	str = strbuf_detach(&sb, NULL);
	pr_info(" type='%s' size=%#lx (die:%#lx)\n",
		str, (long)size, (long)dwarf_dieoffset(die));
	free(str);
}

static void pr_debug_location(Dwarf_Die *die, u64 pc, int reg)
{
	ptrdiff_t off = 0;
	Dwarf_Attribute attr;
	Dwarf_Addr base, start, end;
	Dwarf_Op *ops;
	size_t nops;

	if (!debug_type_profile && verbose < 3)
		return;

	if (dwarf_attr(die, DW_AT_location, &attr) == NULL)
		return;

	while ((off = dwarf_getlocations(&attr, off, &base, &start, &end, &ops, &nops)) > 0) {
		if (reg != DWARF_REG_PC && end <= pc)
			continue;
		if (reg != DWARF_REG_PC && start > pc)
			break;

		pr_info(" variable location: ");
		switch (ops->atom) {
		case DW_OP_reg0 ...DW_OP_reg31:
			pr_info("reg%d\n", ops->atom - DW_OP_reg0);
			break;
		case DW_OP_breg0 ...DW_OP_breg31:
			pr_info("base=reg%d, offset=%#lx\n",
				ops->atom - DW_OP_breg0, (long)ops->number);
			break;
		case DW_OP_regx:
			pr_info("reg%ld\n", (long)ops->number);
			break;
		case DW_OP_bregx:
			pr_info("base=reg%ld, offset=%#lx\n",
				(long)ops->number, (long)ops->number2);
			break;
		case DW_OP_fbreg:
			pr_info("use frame base, offset=%#lx\n", (long)ops->number);
			break;
		case DW_OP_addr:
			pr_info("address=%#lx\n", (long)ops->number);
			break;
		default:
			pr_info("unknown: code=%#x, number=%#lx\n",
				ops->atom, (long)ops->number);
			break;
		}
		break;
	}
}

static void pr_debug_scope(Dwarf_Die *scope_die)
{
	int tag;

	if (!debug_type_profile && verbose < 3)
		return;

	pr_info("(die:%lx) ", (long)dwarf_dieoffset(scope_die));

	tag = dwarf_tag(scope_die);
	if (tag == DW_TAG_subprogram)
		pr_info("[function] %s\n", die_name(scope_die));
	else if (tag == DW_TAG_inlined_subroutine)
		pr_info("[inlined] %s\n", die_name(scope_die));
	else if (tag == DW_TAG_lexical_block)
		pr_info("[block]\n");
	else
		pr_info("[unknown] tag=%x\n", tag);
}

bool has_reg_type(struct type_state *state, int reg)
{
	return (unsigned)reg < ARRAY_SIZE(state->regs);
}

static void init_type_state(struct type_state *state, const struct arch *arch)
{
	memset(state, 0, sizeof(*state));
	INIT_LIST_HEAD(&state->stack_vars);

	if (arch__is_x86(arch)) {
		state->regs[0].caller_saved = true;
		state->regs[1].caller_saved = true;
		state->regs[2].caller_saved = true;
		state->regs[4].caller_saved = true;
		state->regs[5].caller_saved = true;
		state->regs[8].caller_saved = true;
		state->regs[9].caller_saved = true;
		state->regs[10].caller_saved = true;
		state->regs[11].caller_saved = true;
		state->ret_reg = 0;
		state->stack_reg = X86_REG_SP;
	}
}

static void exit_type_state(struct type_state *state)
{
	struct type_state_stack *stack, *tmp;

	list_for_each_entry_safe(stack, tmp, &state->stack_vars, list) {
		list_del(&stack->list);
		free(stack);
	}
}

/*
 * Compare type name and size to maintain them in a tree.
 * I'm not sure if DWARF would have information of a single type in many
 * different places (compilation units).  If not, it could compare the
 * offset of the type entry in the .debug_info section.
 */
static int data_type_cmp(const void *_key, const struct rb_node *node)
{
	const struct annotated_data_type *key = _key;
	struct annotated_data_type *type;

	type = rb_entry(node, struct annotated_data_type, node);

	if (key->self.size != type->self.size)
		return key->self.size - type->self.size;
	return strcmp(key->self.type_name, type->self.type_name);
}

static bool data_type_less(struct rb_node *node_a, const struct rb_node *node_b)
{
	struct annotated_data_type *a, *b;

	a = rb_entry(node_a, struct annotated_data_type, node);
	b = rb_entry(node_b, struct annotated_data_type, node);

	if (a->self.size != b->self.size)
		return a->self.size < b->self.size;
	return strcmp(a->self.type_name, b->self.type_name) < 0;
}

/*
 * Members of struct/union members are added recursively, and the same DIE
 * that is not what it looks like, the one that makes the type chasers in
 * util/dwarf-aux.c spin, can make a member's type point back at one of its
 * own ancestors, recursing until the stack is gone.  Nothing usable comes
 * out of nesting members this deep anyway.
 */
#define MAX_MEMBER_DEPTH 8

/* Recursively add new members for struct/union */
static int __add_member_cb(Dwarf_Die *die, void *arg)
{
	struct annotated_member *parent = arg;
	struct annotated_member *member;
	Dwarf_Die member_type, die_mem;
	Dwarf_Word size, loc, bit_size = 0;
	Dwarf_Attribute attr;
	struct strbuf sb;
	int tag;

	if (dwarf_tag(die) != DW_TAG_member)
		return DIE_FIND_CB_SIBLING;

	if (__die_get_real_type(die, &member_type) == NULL)
		return DIE_FIND_CB_SIBLING;

	if (dwarf_tag(&member_type) == DW_TAG_typedef) {
		if (die_get_real_type(&member_type, &die_mem) == NULL)
			return DIE_FIND_CB_SIBLING;
	} else {
		die_mem = member_type;
	}

	member = zalloc(sizeof(*member));
	if (member == NULL)
		return DIE_FIND_CB_END;

	strbuf_init(&sb, 32);
	die_get_typename(die, &sb);

	if (dwarf_aggregate_size(&die_mem, &size) < 0)
		size = 0;

	if (dwarf_attr_integrate(die, DW_AT_data_member_location, &attr)) {
		if (dwarf_formudata(&attr, &loc) != 0) {
			if (die_get_data_member_location(die, &loc) != 0)
				loc = 0;
		}
	} else {
		/* bitfield member */
		if (dwarf_attr_integrate(die, DW_AT_data_bit_offset, &attr) &&
		    dwarf_formudata(&attr, &loc) == 0)
			loc /= 8;
		else
			loc = 0;

		if (dwarf_attr_integrate(die, DW_AT_bit_size, &attr) &&
		    dwarf_formudata(&attr, &bit_size) == 0)
			size = (bit_size + 7) / 8;
	}

	member->type_name = strbuf_detach(&sb, NULL);
	/* member->var_name can be NULL */
	if (dwarf_diename(die)) {
		if (bit_size) {
			if (asprintf(&member->var_name, "%s:%ld",
				     dwarf_diename(die), (long)bit_size) < 0)
				member->var_name = NULL;
		} else {
			const char *name = dwarf_diename(die);

			member->var_name = name ? strdup(name) : NULL;
		}

		if (member->var_name == NULL) {
			free(member);
			return DIE_FIND_CB_END;
		}
	}
	member->size = size;
	member->offset = loc + parent->offset;
	member->depth = parent->depth + 1;
	INIT_LIST_HEAD(&member->children);
	list_add_tail(&member->node, &parent->children);

	tag = dwarf_tag(&die_mem);
	if (member->depth >= MAX_MEMBER_DEPTH) {
		/* Tell the browser and JSON consumers this isn't all */
		member->truncated = true;
		pr_debug_dtp("member nesting limit reached at %s\n",
			     member->type_name ?: "(unknown type)");
		return DIE_FIND_CB_SIBLING;
	}

	switch (tag) {
	case DW_TAG_structure_type:
	case DW_TAG_union_type:
		die_find_child(&die_mem, __add_member_cb, member, &die_mem);
		break;
	default:
		break;
	}
	return DIE_FIND_CB_SIBLING;
}

static void add_member_types(struct annotated_data_type *parent, Dwarf_Die *type)
{
	Dwarf_Die die_mem;

	die_find_child(type, __add_member_cb, &parent->self, &die_mem);
}

static void delete_members(struct annotated_member *member)
{
	struct annotated_member *child, *tmp;

	list_for_each_entry_safe(child, tmp, &member->children, node) {
		list_del(&child->node);
		delete_members(child);
		zfree(&child->type_name);
		zfree(&child->var_name);
		free(child);
	}
}

static int fill_member_name(char *buf, size_t sz, struct annotated_member *m,
			    int offset, bool first)
{
	struct annotated_member *child;

	if (list_empty(&m->children))
		return 0;

	list_for_each_entry(child, &m->children, node) {
		int len;

		if (offset < child->offset || offset >= child->offset + child->size)
			continue;

		/* It can have anonymous struct/union members */
		if (child->var_name) {
			len = scnprintf(buf, sz, "%s%s",
					first ? "" : ".", child->var_name);
			first = false;
		} else {
			len = 0;
		}

		return fill_member_name(buf + len, sz - len, child, offset, first) + len;
	}
	return 0;
}

int annotated_data_type__get_member_name(struct annotated_data_type *adt,
					 char *buf, size_t sz, int member_offset)
{
	return fill_member_name(buf, sz, &adt->self, member_offset, /*first=*/true);
}

static struct annotated_data_type *dso__findnew_data_type(struct dso *dso,
							  Dwarf_Die *type_die)
{
	struct annotated_data_type *result = NULL;
	struct annotated_data_type key;
	struct rb_node *node;
	struct strbuf sb;
	char *type_name;
	Dwarf_Word size;

	strbuf_init(&sb, 32);
	if (die_get_typename_from_type(type_die, &sb) < 0)
		strbuf_add(&sb, "(unknown type)", 14);
	type_name = strbuf_detach(&sb, NULL);

	if (dwarf_tag(type_die) == DW_TAG_typedef)
		die_get_real_type(type_die, type_die);

	if (dwarf_aggregate_size(type_die, &size) != 0)
		size = 0;

	/* Check existing nodes in dso->data_types tree */
	key.self.type_name = type_name;
	key.self.size = size;
	node = rb_find(&key, dso__data_types(dso), data_type_cmp);
	if (node) {
		result = rb_entry(node, struct annotated_data_type, node);
		free(type_name);
		return result;
	}

	/* If not, add a new one */
	result = zalloc(sizeof(*result));
	if (result == NULL) {
		free(type_name);
		return NULL;
	}

	result->self.type_name = type_name;
	result->self.size = size;
	INIT_LIST_HEAD(&result->self.children);

	if (symbol_conf.annotate_data_member)
		add_member_types(result, type_die);

	rb_add(&result->node, dso__data_types(dso), data_type_less);
	return result;
}

static bool find_cu_die(struct debuginfo *di, u64 pc, Dwarf_Die *cu_die)
{
	Dwarf_Off off, next_off;
	size_t header_size;

	if (dwarf_addrdie(di->dbg, pc, cu_die) != NULL)
		return cu_die;

	/*
	 * There are some kernels don't have full aranges and contain only a few
	 * aranges entries.  Fallback to iterate all CU entries in .debug_info
	 * in case it's missing.
	 */
	off = 0;
	while (dwarf_nextcu(di->dbg, off, &next_off, &header_size,
			    NULL, NULL, NULL) == 0) {
		if (dwarf_offdie(di->dbg, off + header_size, cu_die) &&
		    dwarf_haspc(cu_die, pc))
			return true;

		off = next_off;
	}
	return false;
}

enum type_match_result {
	PERF_TMR_UNKNOWN = 0,
	PERF_TMR_OK,
	PERF_TMR_NO_TYPE,
	PERF_TMR_NO_POINTER,
	PERF_TMR_NO_SIZE,
	PERF_TMR_BAD_OFFSET,
	PERF_TMR_BAIL_OUT,
};

static const char *match_result_str(enum type_match_result tmr)
{
	switch (tmr) {
	case PERF_TMR_OK:
		return "Good!";
	case PERF_TMR_NO_TYPE:
		return "no type information";
	case PERF_TMR_NO_POINTER:
		return "no/void pointer";
	case PERF_TMR_NO_SIZE:
		return "type size is unknown";
	case PERF_TMR_BAD_OFFSET:
		return "offset bigger than size";
	case PERF_TMR_UNKNOWN:
	case PERF_TMR_BAIL_OUT:
	default:
		return "invalid state";
	}
}

static bool is_compound_type(Dwarf_Die *type_die)
{
	int tag = dwarf_tag(type_die);

	return tag == DW_TAG_structure_type || tag == DW_TAG_union_type;
}

/* returns if Type B has better information than Type A */
static bool is_better_type(Dwarf_Die *type_a, Dwarf_Die *type_b)
{
	Dwarf_Word size_a, size_b;
	Dwarf_Die die_a, die_b;
	Dwarf_Die ptr_a, ptr_b;
	Dwarf_Die *ptr_type_a, *ptr_type_b;

	ptr_type_a = die_get_pointer_type(type_a, &ptr_a);
	ptr_type_b = die_get_pointer_type(type_b, &ptr_b);

	/* pointer type is preferred */
	if ((ptr_type_a != NULL) != (ptr_type_b != NULL))
		return ptr_type_b != NULL;

	if (ptr_type_b) {
		/*
		 * We want to compare the target type, but 'void *' can fail to
		 * get the target type.
		 */
		if (die_get_real_type(ptr_type_a, &die_a) == NULL)
			return true;
		if (die_get_real_type(ptr_type_b, &die_b) == NULL)
			return false;

		type_a = &die_a;
		type_b = &die_b;
	}

	/* bigger type is preferred */
	if (dwarf_aggregate_size(type_a, &size_a) < 0 ||
	    dwarf_aggregate_size(type_b, &size_b) < 0)
		return false;

	if (size_a != size_b)
		return size_a < size_b;

	/* struct or union is preferred */
	if (is_compound_type(type_a) != is_compound_type(type_b))
		return is_compound_type(type_b);

	/* typedef is preferred */
	if (dwarf_tag(type_b) == DW_TAG_typedef)
		return true;

	return false;
}

/* The type info will be saved in @type_die */
static enum type_match_result check_variable(struct data_loc_info *dloc,
					     Dwarf_Die *var_die,
					     Dwarf_Die *type_die, int reg,
					     int offset, bool is_fbreg)
{
	Dwarf_Word size;
	bool needs_pointer = true;
	Dwarf_Die sized_type;

	if (reg == DWARF_REG_PC)
		needs_pointer = false;
	else if (reg == dloc->fbreg || is_fbreg)
		needs_pointer = false;
	else if (arch__is_x86(dloc->arch) && reg == X86_REG_SP)
		needs_pointer = false;

	/* Get the type of the variable */
	if (__die_get_real_type(var_die, type_die) == NULL)
		return PERF_TMR_NO_TYPE;

	/*
	 * Usually it expects a pointer type for a memory access.
	 * Convert to a real type it points to.  But global variables
	 * and local variables are accessed directly without a pointer.
	 */
	if (needs_pointer) {
		if (die_get_pointer_type(type_die, type_die) == NULL ||
		    __die_get_real_type(type_die, type_die) == NULL)
			return PERF_TMR_NO_POINTER;
	}

	if (dwarf_tag(type_die) == DW_TAG_typedef)
		die_get_real_type(type_die, &sized_type);
	else
		sized_type = *type_die;

	/* Get the size of the actual type */
	if (dwarf_aggregate_size(&sized_type, &size) < 0)
		return PERF_TMR_NO_SIZE;

	/* Minimal sanity check */
	if ((unsigned)offset >= size)
		return PERF_TMR_BAD_OFFSET;

	return PERF_TMR_OK;
}

struct type_state_stack *find_stack_state(struct type_state *state,
						 int offset)
{
	struct type_state_stack *stack;

	list_for_each_entry(stack, &state->stack_vars, list) {
		if (offset == stack->offset)
			return stack;

		if (stack->compound && stack->offset < offset &&
		    offset < stack->offset + stack->size)
			return stack;
	}
	return NULL;
}

void set_stack_state(struct type_state_stack *stack, int offset, u8 kind,
			    Dwarf_Die *type_die, int ptr_offset)
{
	int tag;
	Dwarf_Word size;

	if (kind == TSR_KIND_POINTER) {
		/* TODO: arch-dependent pointer size */
		size = sizeof(void *);
	}
	else if (dwarf_aggregate_size(type_die, &size) < 0)
		size = 0;

	stack->type = *type_die;
	stack->size = size;
	stack->offset = offset;
	stack->ptr_offset = ptr_offset;
	stack->kind = kind;

	if (kind == TSR_KIND_POINTER) {
		stack->compound = false;
		return;
	}

	tag = dwarf_tag(type_die);

	switch (tag) {
	case DW_TAG_structure_type:
	case DW_TAG_union_type:
		stack->compound = (kind != TSR_KIND_PERCPU_POINTER);
		break;
	default:
		stack->compound = false;
		break;
	}
}

struct type_state_stack *findnew_stack_state(struct type_state *state,
						    int offset, u8 kind,
						    Dwarf_Die *type_die,
						    int ptr_offset)
{
	struct type_state_stack *stack = find_stack_state(state, offset);

	if (stack) {
		set_stack_state(stack, offset, kind, type_die, ptr_offset);
		return stack;
	}

	stack = malloc(sizeof(*stack));
	if (stack) {
		set_stack_state(stack, offset, kind, type_die, ptr_offset);
		list_add(&stack->list, &state->stack_vars);
	}
	return stack;
}

/* Maintain a cache for quick global variable lookup */
struct global_var_entry {
	struct rb_node node;
	char *name;
	u64 start;
	u64 end;
	u64 die_offset;
	int die_tag;
};

static int global_var_cmp(const void *_key, const struct rb_node *node)
{
	const u64 addr = (uintptr_t)_key;
	struct global_var_entry *gvar;

	gvar = rb_entry(node, struct global_var_entry, node);

	if (gvar->start <= addr && addr < gvar->end)
		return 0;
	return gvar->start > addr ? -1 : 1;
}

static bool global_var_less(struct rb_node *node_a, const struct rb_node *node_b)
{
	struct global_var_entry *gvar_a, *gvar_b;

	gvar_a = rb_entry(node_a, struct global_var_entry, node);
	gvar_b = rb_entry(node_b, struct global_var_entry, node);

	return gvar_a->start < gvar_b->start;
}

static struct global_var_entry *global_var__find(struct data_loc_info *dloc, u64 addr)
{
	struct dso *dso = map__dso(dloc->ms->map);
	struct rb_node *node;

	node = rb_find((void *)(uintptr_t)addr, dso__global_vars(dso), global_var_cmp);
	if (node == NULL)
		return NULL;

	return rb_entry(node, struct global_var_entry, node);
}

static bool global_var__add(struct data_loc_info *dloc, u64 addr,
			    const char *name, Dwarf_Die *type_die)
{
	struct dso *dso = map__dso(dloc->ms->map);
	struct global_var_entry *gvar;
	Dwarf_Word size;

	if (dwarf_aggregate_size(type_die, &size) < 0)
		return false;

	gvar = malloc(sizeof(*gvar));
	if (gvar == NULL)
		return false;

	gvar->name = name ? strdup(name) : NULL;
	if (name && gvar->name == NULL) {
		free(gvar);
		return false;
	}

	gvar->start = addr;
	gvar->end = addr + size;
	gvar->die_offset = dwarf_dieoffset(type_die);
	gvar->die_tag = dwarf_tag(type_die);

	rb_add(&gvar->node, dso__global_vars(dso), global_var_less);
	return true;
}

void global_var_type__tree_delete(struct rb_root *root)
{
	struct global_var_entry *gvar;

	while (!RB_EMPTY_ROOT(root)) {
		struct rb_node *node = rb_first(root);

		rb_erase(node, root);
		gvar = rb_entry(node, struct global_var_entry, node);
		zfree(&gvar->name);
		free(gvar);
	}
}

bool get_global_var_info(struct data_loc_info *dloc, u64 addr,
				const char **var_name, int *var_offset)
{
	struct addr_location al;
	struct symbol *sym;
	u64 mem_addr;

	/* Kernel symbols might be relocated */
	mem_addr = addr + map__reloc(dloc->ms->map);

	addr_location__init(&al);
	sym = thread__find_symbol_fb(dloc->thread, dloc->cpumode,
				     mem_addr, &al);
	if (sym) {
		*var_name = sym->name;
		/* Calculate type offset from the start of variable */
		*var_offset = mem_addr - map__unmap_ip(al.map, sym->start);
	} else {
		*var_name = NULL;
	}
	addr_location__exit(&al);
	if (*var_name == NULL)
		return false;

	return true;
}

static void global_var__collect(struct data_loc_info *dloc)
{
	Dwarf *dwarf = dloc->di->dbg;
	Dwarf_Off off, next_off;
	Dwarf_Die cu_die, type_die;
	size_t header_size;

	/* Iterate all CU and collect global variables that have no location in a register. */
	off = 0;
	while (dwarf_nextcu(dwarf, off, &next_off, &header_size,
			    NULL, NULL, NULL) == 0) {
		struct die_var_type *var_types = NULL;
		struct die_var_type *pos;

		if (dwarf_offdie(dwarf, off + header_size, &cu_die) == NULL) {
			off = next_off;
			continue;
		}

		die_collect_global_vars(&cu_die, &var_types);

		for (pos = var_types; pos; pos = pos->next) {
			const char *var_name = NULL;
			int var_offset = 0;

			if (pos->reg != -1)
				continue;

			if (!die_get_type_die(dwarf, pos->die_off, pos->die_tag,
					      &type_die))
				continue;

			get_global_var_info(dloc, pos->addr, &var_name, &var_offset);

			global_var__add(dloc, pos->addr, var_name, &type_die);
		}

		delete_var_types(var_types);

		off = next_off;
	}
}

bool get_global_var_type(Dwarf_Die *cu_die, struct data_loc_info *dloc,
				u64 ip, u64 var_addr, int *var_offset,
				Dwarf_Die *type_die)
{
	u64 pc;
	int offset;
	const char *var_name = NULL;
	struct global_var_entry *gvar;
	struct dso *dso = map__dso(dloc->ms->map);
	Dwarf_Die var_die;

	if (RB_EMPTY_ROOT(dso__global_vars(dso)))
		global_var__collect(dloc);

	gvar = global_var__find(dloc, var_addr);
	if (gvar) {
		if (!die_get_type_die(dloc->di->dbg, gvar->die_offset,
				      gvar->die_tag, type_die))
			return false;

		*var_offset = var_addr - gvar->start;
		return true;
	}

	/* Try to get the variable by address first */
	if (die_find_variable_by_addr(cu_die, var_addr, &var_die, type_die,
				      &offset)) {
		var_name = dwarf_diename(&var_die);
		*var_offset = offset;
		goto ok;
	}

	if (!get_global_var_info(dloc, var_addr, &var_name, var_offset))
		return false;

	pc = map__rip_2objdump(dloc->ms->map, ip);

	/* Try to get the name of global variable */
	if (die_find_variable_at(cu_die, var_name, pc, &var_die) &&
	    check_variable(dloc, &var_die, type_die, DWARF_REG_PC, *var_offset,
			   /*is_fbreg=*/false) == PERF_TMR_OK)
		goto ok;

	return false;

ok:
	/* The address should point to the start of the variable */
	global_var__add(dloc, var_addr - *var_offset, var_name, type_die);
	return true;
}

static bool die_is_same(Dwarf_Die *die_a, Dwarf_Die *die_b)
{
	return (die_a->cu == die_b->cu) && (die_a->addr == die_b->addr);
}

static void tsr_set_lifetime(struct type_state_reg *tsr,
			     const struct die_var_type *var)
{
	if (var && var->has_range && var->end > var->addr) {
		tsr->lifetime_active = true;
		tsr->lifetime_end = var->end;
	} else {
		tsr->lifetime_active = false;
		tsr->lifetime_end = 0;
	}
}

/**
 * update_var_state - Update type state using given variables
 * @state: type state table
 * @dloc: data location info
 * @addr: instruction address to match with variable
 * @insn_offset: instruction offset (for debug)
 * @var_types: list of variables with type info
 *
 * This function fills the @state table using @var_types info.  Each variable
 * is used only at the given location and updates an entry in the table.
 */
static void update_var_state(struct type_state *state, struct data_loc_info *dloc,
			     u64 addr, u64 insn_offset, struct die_var_type *var_types)
{
	Dwarf_Die mem_die;
	struct die_var_type *var;
	int fbreg = dloc->fbreg;
	int fb_offset = 0;

	if (dloc->fb_cfa) {
		if (die_get_cfa(dloc->di->dbg, addr, &fbreg, &fb_offset) < 0)
			fbreg = -1;
	}

	for (var = var_types; var != NULL; var = var->next) {
		/* Check if addr falls within the variable's valid range */
		if (var->has_range) {
			if (addr < var->addr || (var->end && addr >= var->end))
				continue;
		} else {
			if (addr != var->addr)
				continue;
		}
		/* Get the type DIE using the offset */
		if (!die_get_type_die(dloc->di->dbg, var->die_off,
				      var->die_tag, &mem_die))
			continue;

		if (var->reg == DWARF_REG_FB || var->reg == fbreg || var->reg == state->stack_reg) {
			Dwarf_Die ptr_die;
			Dwarf_Die *ptr_type;
			int offset = var->offset;
			struct type_state_stack *stack;

			ptr_type = die_get_pointer_type(&mem_die, &ptr_die);

			/* If the reg location holds the pointer value, dereference the type */
			if (!var->is_reg_var_addr && ptr_type &&
			    __die_get_real_type(ptr_type, &mem_die) == NULL)
				continue;

			if (var->reg != DWARF_REG_FB)
				offset -= fb_offset;

			stack = find_stack_state(state, offset);
			if (stack && stack->kind == TSR_KIND_TYPE &&
			    !is_better_type(&stack->type, &mem_die))
				continue;

			findnew_stack_state(state, offset, TSR_KIND_TYPE,
					    &mem_die, /*ptr_offset=*/0);

			if (var->reg == state->stack_reg) {
				pr_debug_dtp("var [%"PRIx64"] %#x(reg%d)",
					     insn_offset, offset, state->stack_reg);
			} else {
				pr_debug_dtp("var [%"PRIx64"] -%#x(stack)",
					     insn_offset, -offset);
			}
			pr_debug_type_name(&mem_die, TSR_KIND_TYPE);
		} else if (has_reg_type(state, var->reg)) {
			struct type_state_reg *reg;
			Dwarf_Die orig_type;

			reg = &state->regs[var->reg];

			if (reg->ok && reg->kind == TSR_KIND_TYPE &&
			   (!is_better_type(&reg->type, &mem_die) || var->is_reg_var_addr))
				continue;

			/* Handle address registers with TSR_KIND_POINTER */
			if (var->is_reg_var_addr) {
				if (reg->ok && reg->kind == TSR_KIND_POINTER &&
				    !is_better_type(&reg->type, &mem_die))
					continue;

				reg->offset = -var->offset;
				reg->type = mem_die;
				reg->kind = TSR_KIND_POINTER;
				reg->ok = true;
				tsr_set_lifetime(reg, var);

				pr_debug_dtp("var [%"PRIx64"] reg%d addr offset %x",
					     insn_offset, var->reg, var->offset);
				pr_debug_type_name(&mem_die, TSR_KIND_POINTER);
				continue;
			}

			orig_type = reg->type;
			/*
			 * var->offset + reg value is the beginning of the struct
			 * reg->offset is the offset the reg points
			 */
			reg->offset = -var->offset;
			reg->type = mem_die;
			reg->kind = TSR_KIND_TYPE;
			reg->ok = true;
			tsr_set_lifetime(reg, var);

			pr_debug_dtp("var [%"PRIx64"] reg%d offset %x",
				     insn_offset, var->reg, var->offset);
			pr_debug_type_name(&mem_die, TSR_KIND_TYPE);

			/*
			 * If this register is directly copied from another and it gets a
			 * better type, also update the type of the source register.  This
			 * is usually the case of container_of() macro with offset of 0.
			 */
			if (has_reg_type(state, reg->copied_from)) {
				struct type_state_reg *copy_reg;

				copy_reg = &state->regs[reg->copied_from];

				/* TODO: check if type is compatible or embedded */
				if (!copy_reg->ok || (copy_reg->kind != TSR_KIND_TYPE) ||
				    !die_is_same(&copy_reg->type, &orig_type) ||
				    !is_better_type(&copy_reg->type, &mem_die))
					continue;

				copy_reg->type = mem_die;

				pr_debug_dtp("var [%"PRIx64"] copyback reg%d",
					     insn_offset, reg->copied_from);
				pr_debug_type_name(&mem_die, TSR_KIND_TYPE);
			}
		}
	}
}

/**
 * update_insn_state - Update type state for an instruction
 * @state: type state table
 * @dloc: data location info
 * @cu_die: compile unit debug entry
 * @dl: disasm line for the instruction
 *
 * This function updates the @state table for the target operand of the
 * instruction at @dl if it transfers the type like MOV on x86.  Since it
 * tracks the type, it won't care about the values like in arithmetic
 * instructions like ADD/SUB/MUL/DIV and INC/DEC.
 *
 * Note that ops->reg2 is only available when both mem_ref and multi_regs
 * are true.
 */
static void update_insn_state(struct type_state *state, struct data_loc_info *dloc,
			      Dwarf_Die *cu_die, struct disasm_line *dl)
{
	if (dloc->arch->update_insn_state)
		dloc->arch->update_insn_state(state, dloc, cu_die, dl);
}

/*
 * Prepend this_blocks (from the outer scope) to full_blocks, removing
 * duplicate disasm line.
 */
static void prepend_basic_blocks(struct list_head *this_blocks,
				 struct list_head *full_blocks)
{
	struct annotated_basic_block *first_bb, *last_bb;

	last_bb = list_last_entry(this_blocks, typeof(*last_bb), list);
	first_bb = list_first_entry(full_blocks, typeof(*first_bb), list);

	if (list_empty(full_blocks))
		goto out;

	/* Last insn in this_blocks should be same as first insn in full_blocks */
	if (last_bb->end != first_bb->begin) {
		pr_debug("prepend basic blocks: mismatched disasm line %"PRIx64" -> %"PRIx64"\n",
			 last_bb->end->al.offset, first_bb->begin->al.offset);
		goto out;
	}

	/* Is the basic block have only one disasm_line? */
	if (last_bb->begin == last_bb->end) {
		list_del(&last_bb->list);
		free(last_bb);
		goto out;
	}

	/* Point to the insn before the last when adding this block to full_blocks */
	last_bb->end = list_prev_entry(last_bb->end, al.node);

out:
	list_splice(this_blocks, full_blocks);
}

static void delete_basic_blocks(struct list_head *basic_blocks)
{
	struct annotated_basic_block *bb, *tmp;

	list_for_each_entry_safe(bb, tmp, basic_blocks, list) {
		list_del(&bb->list);
		free(bb);
	}
}

/* Make sure all variables have a valid start address */
static void fixup_var_address(struct die_var_type *var_types, u64 addr)
{
	while (var_types) {
		/*
		 * Some variables have no address range meaning it's always
		 * available in the whole scope.  Let's adjust the start
		 * address to the start of the scope.
		 */
		if (var_types->addr == 0)
			var_types->addr = addr;

		var_types = var_types->next;
	}
}

static void delete_var_types(struct die_var_type *var_types)
{
	while (var_types) {
		struct die_var_type *next = var_types->next;

		free(var_types);
		var_types = next;
	}
}

/* should match to is_stack_canary() in util/annotate.c */
static void setup_stack_canary(struct data_loc_info *dloc)
{
	if (arch__is_x86(dloc->arch)) {
		dloc->op->segment = INSN_SEG_X86_GS;
		dloc->op->imm = true;
		dloc->op->offset = 40;
	}
}

/*
 * It's at the target address, check if it has a matching type.
 * It returns PERF_TMR_BAIL_OUT when it looks up per-cpu variables which
 * are similar to global variables and no additional info is needed.
 */
static enum type_match_result check_matching_type(struct type_state *state,
						  struct data_loc_info *dloc,
						  Dwarf_Die *cu_die,
						  struct disasm_line *dl,
						  Dwarf_Die *type_die)
{
	Dwarf_Word size;
	u32 insn_offset = dl->al.offset;
	int reg = dloc->op->reg1;
	int offset = dloc->op->offset;
	const char *offset_sign = "";
	bool retry = true;

	if (offset < 0) {
		offset = -offset;
		offset_sign = "-";
	}

again:
	pr_debug_dtp("chk [%x] reg%d offset=%s%#x ok=%d kind=%d ",
		     insn_offset, reg, offset_sign, offset,
		     state->regs[reg].ok, state->regs[reg].kind);

	if (!state->regs[reg].ok)
		goto check_non_register;

	if (state->regs[reg].kind == TSR_KIND_TYPE) {
		Dwarf_Die ptr_die;
		Dwarf_Die sized_type;
		Dwarf_Die *ptr_type;
		struct strbuf sb;

		strbuf_init(&sb, 32);
		die_get_typename_from_type(&state->regs[reg].type, &sb);
		pr_debug_dtp("(%s)", sb.buf);
		strbuf_release(&sb);

		/*
		 * Normal registers should hold a pointer (or array) to
		 * dereference a memory location.
		 */
		ptr_type = die_get_pointer_type(&state->regs[reg].type, &ptr_die);
		if (!ptr_type) {
			if (dloc->op->offset < 0 && reg != state->stack_reg)
				goto check_kernel;

			return PERF_TMR_NO_POINTER;
		}

		/* Remove the pointer and get the target type */
		if (__die_get_real_type(ptr_type, type_die) == NULL)
			return PERF_TMR_NO_POINTER;

		dloc->type_offset = dloc->op->offset + state->regs[reg].offset;

		if (dwarf_tag(type_die) == DW_TAG_typedef)
			die_get_real_type(type_die, &sized_type);
		else
			sized_type = *type_die;

		/* Get the size of the actual type */
		if (dwarf_aggregate_size(&sized_type, &size) < 0 ||
		    (unsigned)dloc->type_offset >= size)
			return PERF_TMR_BAD_OFFSET;

		return PERF_TMR_OK;
	}

	if (state->regs[reg].kind == TSR_KIND_POINTER) {
		struct strbuf sb;

		strbuf_init(&sb, 32);
		die_get_typename_from_type(&state->regs[reg].type, &sb);
		pr_debug_dtp("(ptr->%s)", sb.buf);
		strbuf_release(&sb);

		/*
		 * Register holds a pointer (address) to the target variable.
		 * The type is the type of the variable it points to.
		 */
		*type_die = state->regs[reg].type;

		dloc->type_offset = dloc->op->offset + state->regs[reg].offset;

		/* Get the size of the actual type */
		if (dwarf_aggregate_size(type_die, &size) < 0 ||
		    (unsigned)dloc->type_offset >= size)
			return PERF_TMR_BAD_OFFSET;

		return PERF_TMR_OK;
	}

	if (state->regs[reg].kind == TSR_KIND_PERCPU_POINTER) {
		pr_debug_dtp("percpu ptr");

		/*
		 * It's actaully pointer but the address was calculated using
		 * some arithmetic.  So it points to the actual type already.
		 */
		*type_die = state->regs[reg].type;

		dloc->type_offset = dloc->op->offset;

		/* Get the size of the actual type */
		if (dwarf_aggregate_size(type_die, &size) < 0 ||
		    (unsigned)dloc->type_offset >= size)
			return PERF_TMR_BAIL_OUT;

		return PERF_TMR_OK;
	}

	if (state->regs[reg].kind == TSR_KIND_CANARY) {
		pr_debug_dtp("stack canary");

		/*
		 * This is a saved value of the stack canary which will be handled
		 * in the outer logic when it returns failure here.  Pretend it's
		 * from the stack canary directly.
		 */
		setup_stack_canary(dloc);

		return PERF_TMR_BAIL_OUT;
	}

	if (state->regs[reg].kind == TSR_KIND_PERCPU_BASE) {
		u64 var_addr = dloc->op->offset;
		int var_offset;

		pr_debug_dtp("percpu var");

		if (dloc->op->multi_regs) {
			int reg2 = dloc->op->reg2;

			if (dloc->op->reg2 == reg)
				reg2 = dloc->op->reg1;

			if (has_reg_type(state, reg2) && state->regs[reg2].ok &&
			    state->regs[reg2].kind == TSR_KIND_CONST)
				var_addr += state->regs[reg2].imm_value;
		}

		if (get_global_var_type(cu_die, dloc, dloc->ip, var_addr,
					&var_offset, type_die)) {
			dloc->type_offset = var_offset;
			return PERF_TMR_OK;
		}
		/* No need to retry per-cpu (global) variables */
		return PERF_TMR_BAIL_OUT;
	}

	if (state->regs[reg].kind == TSR_KIND_CONST &&
	    dso__kernel(map__dso(dloc->ms->map))) {
		if (dloc->op->offset < 0 && reg != state->stack_reg && reg != dloc->fbreg)
			goto check_kernel;
	}
check_non_register:
	if (reg == dloc->fbreg || reg == state->stack_reg) {
		struct type_state_stack *stack;

		pr_debug_dtp("%s", reg == dloc->fbreg ? "fbreg" : "stack");

		stack = find_stack_state(state, dloc->type_offset);
		if (stack == NULL) {
			if (retry) {
				pr_debug_dtp(" : retry\n");
				retry = false;

				/* update type info it's the first store to the stack */
				update_insn_state(state, dloc, cu_die, dl);
				goto again;
			}
			return PERF_TMR_NO_TYPE;
		}

		if (stack->kind == TSR_KIND_CANARY) {
			setup_stack_canary(dloc);
			return PERF_TMR_BAIL_OUT;
		}

		if (stack->kind != TSR_KIND_TYPE)
			return PERF_TMR_NO_TYPE;

		*type_die = stack->type;
		/* Update the type offset from the start of slot */
		dloc->type_offset -= stack->offset;

		return PERF_TMR_OK;
	}

	if (dloc->fb_cfa) {
		struct type_state_stack *stack;
		u64 pc = map__rip_2objdump(dloc->ms->map, dloc->ip);
		int fbreg, fboff;

		pr_debug_dtp("cfa");

		if (die_get_cfa(dloc->di->dbg, pc, &fbreg, &fboff) < 0)
			fbreg = -1;

		if (reg != fbreg)
			return PERF_TMR_NO_TYPE;

		stack = find_stack_state(state, dloc->type_offset - fboff);
		if (stack == NULL) {
			if (retry) {
				pr_debug_dtp(" : retry\n");
				retry = false;

				/* update type info it's the first store to the stack */
				update_insn_state(state, dloc, cu_die, dl);
				goto again;
			}
			return PERF_TMR_NO_TYPE;
		}

		if (stack->kind == TSR_KIND_CANARY) {
			setup_stack_canary(dloc);
			return PERF_TMR_BAIL_OUT;
		}

		if (stack->kind != TSR_KIND_TYPE)
			return PERF_TMR_NO_TYPE;

		*type_die = stack->type;
		/* Update the type offset from the start of slot */
		dloc->type_offset -= fboff + stack->offset;

		return PERF_TMR_OK;
	}

check_kernel:
	if (dso__kernel(map__dso(dloc->ms->map))) {
		u64 addr;

		/* Direct this-cpu access like "%gs:0x34740" */
		if (dloc->op->segment == INSN_SEG_X86_GS && dloc->op->imm &&
		    arch__is_x86(dloc->arch)) {
			pr_debug_dtp("this-cpu var");

			addr = dloc->op->offset;

			if (get_global_var_type(cu_die, dloc, dloc->ip, addr,
						&offset, type_die)) {
				dloc->type_offset = offset;
				return PERF_TMR_OK;
			}
			return PERF_TMR_BAIL_OUT;
		}

		/* Access to global variable like "-0x7dcf0500(,%rdx,8)" */
		if (dloc->op->offset < 0 && reg != state->stack_reg) {
			addr = (s64) dloc->op->offset;

			if (get_global_var_type(cu_die, dloc, dloc->ip, addr,
						&offset, type_die)) {
				pr_debug_dtp("global var");

				dloc->type_offset = offset;
				return PERF_TMR_OK;
			}
			return PERF_TMR_BAIL_OUT;
		}
	}

	return PERF_TMR_UNKNOWN;
}

/* Iterate instructions in basic blocks and update type table */
static enum type_match_result find_data_type_insn(struct data_loc_info *dloc,
						  struct list_head *basic_blocks,
						  struct die_var_type *var_types,
						  Dwarf_Die *cu_die,
						  Dwarf_Die *type_die)
{
	struct type_state state;
	struct symbol *sym = dloc->ms->sym;
	struct annotation *notes = symbol__annotation(sym);
	struct annotated_basic_block *bb;
	enum type_match_result ret = PERF_TMR_UNKNOWN;

	init_type_state(&state, dloc->arch);

	list_for_each_entry(bb, basic_blocks, list) {
		struct disasm_line *dl = bb->begin;

		BUG_ON(bb->begin->al.offset == -1 || bb->end->al.offset == -1);

		pr_debug_dtp("bb: [%"PRIx64" - %"PRIx64"]\n",
			     bb->begin->al.offset, bb->end->al.offset);

		list_for_each_entry_from(dl, &notes->src->source, al.node) {
			u64 this_ip = sym->start + dl->al.offset;
			u64 addr = map__rip_2objdump(dloc->ms->map, this_ip);

			/* Skip comment or debug info lines */
			if (dl->al.offset == -1)
				continue;

			/* Update variable type at this address */
			update_var_state(&state, dloc, addr, dl->al.offset, var_types);

			if (this_ip == dloc->ip) {
				ret = check_matching_type(&state, dloc,
							  cu_die, dl, type_die);
				pr_debug_dtp(" : %s\n", match_result_str(ret));
				goto out;
			}

			/* Update type table after processing the instruction */
			update_insn_state(&state, dloc, cu_die, dl);
			if (dl == bb->end)
				break;
		}
	}

out:
	exit_type_state(&state);
	return ret;
}

static int arch_supports_insn_tracking(struct data_loc_info *dloc)
{
	if ((arch__is_x86(dloc->arch)) || (arch__is_powerpc(dloc->arch)))
		return 1;
	return 0;
}

/*
 * Construct a list of basic blocks for each scope with variables and try to find
 * the data type by updating a type state table through instructions.
 */
static enum type_match_result find_data_type_block(struct data_loc_info *dloc,
						   Dwarf_Die *cu_die,
						   Dwarf_Die *scopes,
						   int nr_scopes,
						   Dwarf_Die *type_die)
{
	LIST_HEAD(basic_blocks);
	struct die_var_type *var_types = NULL;
	u64 src_ip, dst_ip, prev_dst_ip;
	enum type_match_result ret = PERF_TMR_UNKNOWN;

	/* TODO: other architecture support */
	if (!arch_supports_insn_tracking(dloc))
		return PERF_TMR_BAIL_OUT;

	prev_dst_ip = dst_ip = dloc->ip;
	for (int i = nr_scopes - 1; i >= 0; i--) {
		Dwarf_Addr base, start, end;
		LIST_HEAD(this_blocks);

		if (dwarf_ranges(&scopes[i], 0, &base, &start, &end) < 0)
			break;

		pr_debug_dtp("scope: [%d/%d] ", i + 1, nr_scopes);
		pr_debug_scope(&scopes[i]);

		src_ip = map__objdump_2rip(dloc->ms->map, start);

again:
		/* Get basic blocks for this scope */
		if (annotate_get_basic_blocks(dloc->ms->sym, src_ip, dst_ip,
					      &this_blocks) < 0) {
			/* Try previous block if they are not connected */
			if (prev_dst_ip != dst_ip) {
				dst_ip = prev_dst_ip;
				goto again;
			}

			pr_debug_dtp("cannot find a basic block from %"PRIx64" to %"PRIx64"\n",
				     src_ip - dloc->ms->sym->start,
				     dst_ip - dloc->ms->sym->start);
			continue;
		}
		prepend_basic_blocks(&this_blocks, &basic_blocks);

		/* Get variable info for this scope and add to var_types list */
		die_collect_vars(&scopes[i], &var_types);
		fixup_var_address(var_types, start);

		/* Find from start of this scope to the target instruction */
		ret = find_data_type_insn(dloc, &basic_blocks, var_types,
					    cu_die, type_die);
		if (ret == PERF_TMR_OK) {
			char buf[64];
			int offset = dloc->op->offset;
			const char *offset_sign = "";

			if (offset < 0) {
				offset = -offset;
				offset_sign = "-";
			}

			if (dloc->op->multi_regs)
				snprintf(buf, sizeof(buf), "reg%d, reg%d",
					 dloc->op->reg1, dloc->op->reg2);
			else
				snprintf(buf, sizeof(buf), "reg%d", dloc->op->reg1);

			pr_debug_dtp("found by insn track: %s%#x(%s) type-offset=%#x\n",
				     offset_sign, offset, buf, dloc->type_offset);
			break;
		}

		if (ret == PERF_TMR_BAIL_OUT)
			break;

		/* Go up to the next scope and find blocks to the start */
		prev_dst_ip = dst_ip;
		dst_ip = src_ip;
	}

	delete_basic_blocks(&basic_blocks);
	delete_var_types(var_types);
	return ret;
}

/* The result will be saved in @type_die */
static int find_data_type_die(struct data_loc_info *dloc, Dwarf_Die *type_die)
{
	struct annotated_op_loc *loc = dloc->op;
	Dwarf_Die cu_die, var_die;
	Dwarf_Die *scopes = NULL;
	int reg, offset = loc->offset;
	int ret = -1;
	int i, nr_scopes;
	int fbreg = -1;
	int fb_offset = 0;
	bool is_fbreg = false;
	bool found = false;
	u64 pc;
	char buf[64];
	enum type_match_result result = PERF_TMR_UNKNOWN;
	const char *offset_sign = "";

	if (dloc->op->multi_regs)
		snprintf(buf, sizeof(buf), "reg%d, reg%d", dloc->op->reg1, dloc->op->reg2);
	else if (dloc->op->reg1 == DWARF_REG_PC)
		snprintf(buf, sizeof(buf), "PC");
	else
		snprintf(buf, sizeof(buf), "reg%d", dloc->op->reg1);

	if (offset < 0) {
		offset = -offset;
		offset_sign = "-";
	}

	pr_debug_dtp("-----------------------------------------------------------\n");
	pr_debug_dtp("find data type for %s%#x(%s) at %s+%#"PRIx64"\n",
		     offset_sign, offset, buf,
		     dloc->ms->sym->name, dloc->ip - dloc->ms->sym->start);

	/*
	 * IP is a relative instruction address from the start of the map, as
	 * it can be randomized/relocated, it needs to translate to PC which is
	 * a file address for DWARF processing.
	 */
	pc = map__rip_2objdump(dloc->ms->map, dloc->ip);

	/* Get a compile_unit for this address */
	if (!find_cu_die(dloc->di, pc, &cu_die)) {
		pr_debug_dtp("cannot find CU for address %"PRIx64"\n", pc);
		ann_data_stat.no_cuinfo++;
		return -1;
	}

	reg = loc->reg1;
	offset = loc->offset;

	pr_debug_dtp("CU for %s (die:%#lx)\n",
		     die_name(&cu_die), (long)dwarf_dieoffset(&cu_die));

	if (reg == DWARF_REG_PC) {
		if (get_global_var_type(&cu_die, dloc, dloc->ip, dloc->var_addr,
					&offset, type_die)) {
			dloc->type_offset = offset;

			pr_debug_dtp("found by addr=%#"PRIx64" type_offset=%#x\n",
				     dloc->var_addr, offset);
			pr_debug_type_name(type_die, TSR_KIND_TYPE);
			found = true;
			goto out;
		}
	}

	/* Get a list of nested scopes - i.e. (inlined) functions and blocks. */
	nr_scopes = die_get_scopes(&cu_die, pc, &scopes);

	if (reg != DWARF_REG_PC && dwarf_hasattr(&scopes[0], DW_AT_frame_base)) {
		Dwarf_Attribute attr;
		Dwarf_Block block;

		/* Check if the 'reg' is assigned as frame base register */
		if (dwarf_attr(&scopes[0], DW_AT_frame_base, &attr) != NULL &&
		    dwarf_formblock(&attr, &block) == 0 && block.length == 1) {
			switch (*block.data) {
			case DW_OP_reg0 ... DW_OP_reg31:
				fbreg = dloc->fbreg = *block.data - DW_OP_reg0;
				break;
			case DW_OP_call_frame_cfa:
				dloc->fb_cfa = true;
				if (die_get_cfa(dloc->di->dbg, pc, &fbreg,
						&fb_offset) < 0)
					fbreg = -1;
				break;
			default:
				break;
			}

			pr_debug_dtp("frame base: cfa=%d fbreg=%d\n",
				     dloc->fb_cfa, fbreg);
		}
	}

retry:
	is_fbreg = (reg == fbreg);
	if (is_fbreg)
		offset = loc->offset - fb_offset;

	/* Search from the inner-most scope to the outer */
	for (i = nr_scopes - 1; i >= 0; i--) {
		Dwarf_Die mem_die;
		int type_offset = offset;

		if (reg == DWARF_REG_PC) {
			if (!die_find_variable_by_addr(&scopes[i], dloc->var_addr,
						       &var_die, &mem_die,
						       &type_offset))
				continue;
		} else {
			/* Look up variables/parameters in this scope */
			if (!die_find_variable_by_reg(&scopes[i], pc, reg,
						      &mem_die, &type_offset, is_fbreg, &var_die))
				continue;
		}

		pr_debug_dtp("found \"%s\" (die: %#lx) in scope=%d/%d (die: %#lx) ",
			     die_name(&var_die), (long)dwarf_dieoffset(&var_die),
			     i+1, nr_scopes, (long)dwarf_dieoffset(&scopes[i]));

		if (reg == DWARF_REG_PC) {
			pr_debug_dtp("addr=%#"PRIx64" type_offset=%#x\n",
				     dloc->var_addr, type_offset);
		} else if (reg == DWARF_REG_FB || is_fbreg) {
			pr_debug_dtp("stack_offset=%#x type_offset=%#x\n",
				     fb_offset, type_offset);
		} else {
			pr_debug_dtp("type_offset=%#x\n", type_offset);
		}

		if (!found || dloc->type_offset < type_offset ||
		    (dloc->type_offset == type_offset &&
		     !is_better_type(&mem_die, type_die))) {
			*type_die = mem_die;
			dloc->type_offset = type_offset;
			found = true;
		}

		pr_debug_location(&var_die, pc, reg);
		pr_debug_type_name(&mem_die, TSR_KIND_TYPE);
	}

	if (!found && loc->multi_regs && reg == loc->reg1 && loc->reg1 != loc->reg2) {
		reg = loc->reg2;
		goto retry;
	}

	if (!found && reg != DWARF_REG_PC) {
		result = find_data_type_block(dloc, &cu_die, scopes,
					      nr_scopes, type_die);
		if (result == PERF_TMR_OK) {
			ann_data_stat.insn_track++;
			found = true;
		}
	}

out:
	pr_debug_dtp("final result: ");
	if (found) {
		pr_debug_type_name(type_die, TSR_KIND_TYPE);
		ret = 0;
	} else {
		switch (result) {
		case PERF_TMR_NO_TYPE:
		case PERF_TMR_NO_POINTER:
			pr_debug_dtp("%s\n", match_result_str(result));
			ann_data_stat.no_typeinfo++;
			break;
		case PERF_TMR_NO_SIZE:
			pr_debug_dtp("%s\n", match_result_str(result));
			ann_data_stat.invalid_size++;
			break;
		case PERF_TMR_BAD_OFFSET:
			pr_debug_dtp("%s\n", match_result_str(result));
			ann_data_stat.bad_offset++;
			break;
		case PERF_TMR_UNKNOWN:
		case PERF_TMR_BAIL_OUT:
		case PERF_TMR_OK:  /* should not reach here */
		default:
			pr_debug_dtp("no variable found\n");
			ann_data_stat.no_var++;
			break;
		}
		ret = -1;
	}

	free(scopes);
	return ret;
}

/**
 * find_data_type - Return a data type at the location
 * @dloc: data location
 *
 * This functions searches the debug information of the binary to get the data
 * type it accesses.  The exact location is expressed by (ip, reg, offset)
 * for pointer variables or (ip, addr) for global variables.  Note that global
 * variables might update the @dloc->type_offset after finding the start of the
 * variable.  If it cannot find a global variable by address, it tried to find
 * a declaration of the variable using var_name.  In that case, @dloc->offset
 * won't be updated.
 *
 * It return %NULL if not found.
 */
struct annotated_data_type *find_data_type(struct data_loc_info *dloc)
{
	struct dso *dso = map__dso(dloc->ms->map);
	Dwarf_Die type_die;

	/*
	 * The type offset is the same as instruction offset by default.
	 * But when finding a global variable, the offset won't be valid.
	 */
	dloc->type_offset = dloc->op->offset;

	dloc->fbreg = -1;

	if (find_data_type_die(dloc, &type_die) < 0)
		return NULL;

	return dso__findnew_data_type(dso, &type_die);
}

static int alloc_data_type_histograms(struct annotated_data_type *adt, int nr_entries)
{
	int i;
	size_t sz = sizeof(struct type_hist);

	sz += sizeof(struct type_hist_entry) * adt->self.size;

	/* Allocate a table of pointers for each event */
	adt->histograms = calloc(nr_entries, sizeof(*adt->histograms));
	if (adt->histograms == NULL)
		return -ENOMEM;

	/*
	 * Each histogram is allocated for the whole size of the type.
	 * TODO: Probably we can move the histogram to members.
	 */
	for (i = 0; i < nr_entries; i++) {
		adt->histograms[i] = zalloc(sz);
		if (adt->histograms[i] == NULL)
			goto err;
	}

	adt->nr_histograms = nr_entries;
	return 0;

err:
	while (--i >= 0)
		zfree(&(adt->histograms[i]));
	zfree(&adt->histograms);
	return -ENOMEM;
}

static void delete_data_type_histograms(struct annotated_data_type *adt)
{
	for (int i = 0; i < adt->nr_histograms; i++)
		zfree(&(adt->histograms[i]));

	zfree(&adt->histograms);
	adt->nr_histograms = 0;
}

void annotated_data_type__tree_delete(struct rb_root *root)
{
	struct annotated_data_type *pos;

	while (!RB_EMPTY_ROOT(root)) {
		struct rb_node *node = rb_first(root);

		rb_erase(node, root);
		pos = rb_entry(node, struct annotated_data_type, node);
		delete_members(&pos->self);
		delete_data_type_histograms(pos);
		zfree(&pos->self.type_name);
		free(pos);
	}
}

/**
 * annotated_data_type__update_samples - Update histogram
 * @adt: Data type to update
 * @evsel: Event to update
 * @offset: Offset in the type
 * @nr_samples: Number of samples at this offset
 * @period: Event count at this offset
 * @is_store: Whether the access at this offset is a store
 *
 * This function updates type histogram at @ofs for @evsel.  Samples are
 * aggregated before calling this function so it can be called with more
 * than one samples at a certain offset.  Loads and stores are counted
 * separately so an offset that is both read and written keeps both
 * directions, instead of having them summed into a direction-less
 * count.
 */
int annotated_data_type__update_samples(struct annotated_data_type *adt,
					struct evsel *evsel, int offset,
					int nr_samples, u64 period, bool is_store)
{
	struct type_hist *h;

	if (adt == NULL)
		return 0;

	if (adt->histograms == NULL) {
		int nr = evlist__nr_entries(evsel->evlist);

		if (alloc_data_type_histograms(adt, nr) < 0)
			return -1;
	}

	if (offset < 0 || offset >= adt->self.size)
		return -1;

	h = adt->histograms[evsel->core.idx];

	h->nr_samples += nr_samples;
	h->period += period;
	if (is_store) {
		h->addr[offset].nr_samples_store += nr_samples;
		h->addr[offset].period_store += period;
	} else {
		h->addr[offset].nr_samples_load += nr_samples;
		h->addr[offset].period_load += period;
	}
	return 0;
}

static void print_annotated_data_header(struct hist_entry *he, struct evsel *evsel)
{
	struct dso *dso = map__dso(he->ms.map);
	int nr_members = 1;
	int nr_samples = he->stat.nr_events;
	int width = 7;
	const char *val_hdr = "Percent";

	if (evsel__is_group_event(evsel)) {
		struct hist_entry *pair;

		list_for_each_entry(pair, &he->pairs.head, pairs.node)
			nr_samples += pair->stat.nr_events;
	}

	printf("Annotate type: '%s' in %s (%d samples):\n",
	       he->mem_type->self.type_name, dso__name(dso), nr_samples);

	if (evsel__is_group_event(evsel)) {
		struct evsel *pos;
		int i = 0;

		nr_members = 0;
		for_each_group_evsel(pos, evsel) {
			if (symbol_conf.skip_empty &&
			    evsel__hists(pos)->stats.nr_samples == 0)
				continue;

			printf(" event[%d] = %s\n", i++, pos->name);
			nr_members++;
		}
	}

	if (symbol_conf.show_total_period) {
		width = 11;
		val_hdr = "Period";
	} else if (symbol_conf.show_nr_samples) {
		width = 7;
		val_hdr = "Samples";
	}

	printf("============================================================================\n");
	printf("%*s %10s %10s  %s\n", (width + 1) * nr_members, val_hdr,
	       "offset", "size", "field");
}

static void print_annotated_data_value(struct type_hist *h, u64 period, int nr_samples)
{
	double percent = h->period ? (100.0 * period / h->period) : 0;
	const char *color = get_percent_color(percent);

	if (symbol_conf.show_total_period)
		color_fprintf(stdout, color, " %11" PRIu64, period);
	else if (symbol_conf.show_nr_samples)
		color_fprintf(stdout, color, " %7d", nr_samples);
	else
		color_fprintf(stdout, color, " %7.2f", percent);
}

static void print_annotated_data_type(struct annotated_data_type *mem_type,
				      struct annotated_member *member,
				      struct evsel *evsel, int indent)
{
	struct annotated_member *child;
	struct type_hist *h = mem_type->histograms[evsel->core.idx];
	int i, nr_events = 0, samples = 0;
	u64 period = 0;
	int width = symbol_conf.show_total_period ? 11 : 7;
	struct evsel *pos;

	for_each_group_evsel(pos, evsel) {
		h = mem_type->histograms[pos->core.idx];

		if (symbol_conf.skip_empty &&
		    evsel__hists(pos)->stats.nr_samples == 0)
			continue;

		samples = 0;
		period = 0;
		for (i = 0; i < member->size; i++) {
			samples += h->addr[member->offset + i].nr_samples_load +
				   h->addr[member->offset + i].nr_samples_store;
			period += h->addr[member->offset + i].period_load +
				  h->addr[member->offset + i].period_store;
		}
		print_annotated_data_value(h, period, samples);
		nr_events++;
	}

	printf(" %#10x %#10x  %*s%s\t%s",
	       member->offset, member->size, indent, "", member->type_name,
	       member->var_name ?: "");

	if (!list_empty(&member->children))
		printf(" {\n");

	list_for_each_entry(child, &member->children, node)
		print_annotated_data_type(mem_type, child, evsel, indent + 4);

	if (!list_empty(&member->children))
		printf("%*s}", (width + 1) * nr_events + 24 + indent, "");
	printf(";\n");
}

int hist_entry__annotate_data_tty(struct hist_entry *he, struct evsel *evsel)
{
	print_annotated_data_header(he, evsel);
	print_annotated_data_type(he->mem_type, &he->mem_type->self, evsel, 0);
	printf("\n");

	/* move to the next entry */
	return '>';
}

/*
 * Escape a string for JSON output, writing to fp.
 * Handles: ", \, and control characters.
 */
/*
 * Escape a string for inclusion in the JSON output.  The strings come from
 * DWARF/BTF (type and member names, some producers emit garbage for them,
 * e.g. uninitialized bytes in DW_AT_name) and from DSO paths and event
 * names, so apart from the usual JSON escapes the output must also remain
 * valid UTF-8: well-formed multi-byte sequences pass through untouched,
 * anything else, be it a stray continuation byte or a mangled sequence, is
 * replaced with U+FFFD, the Unicode replacement character, instead of
 * emitting raw bytes that strict JSON consumers reject.
 */
void annotated_data_stat__print(struct annotated_data_stat *s)
{
#define PRINT_STAT(fld) if (s->fld) printf("%10d : %s\n", s->fld, #fld)

	/*
	 * bad_addr counts samples (not resolutions): the ones dropped
	 * because their data address is not the one the PC-relative
	 * operand the recorded IP resolves to computes, both the one
	 * that established the entry's resolution and the ones folding
	 * into it.  It is directly comparable with the converter's
	 * "Skipped N samples" report, and stays out of the resolution
	 * outcome split below, like insn_track.  rejected_addr counts
	 * the same drops at the resolution level, the ones that
	 * established a resolution, which is what keeps ok/bad below
	 * adding up.
	 */
	int bad = s->no_sym +
			s->no_insn +
			s->no_insn_ops +
			s->no_mem_ops +
			s->no_reg +
			s->no_dbginfo +
			s->no_cuinfo +
			s->no_var +
			s->no_typeinfo +
			s->invalid_size +
			s->bad_offset +
			s->rejected_addr;
	int ok = s->total - bad;

	printf("Annotate data type stats:\n");
	printf("total %d, ok %d (%.1f%%), bad %d (%.1f%%)\n",
		s->total, ok, 100.0 * ok / (s->total ?: 1), bad, 100.0 * bad / (s->total ?: 1));
	printf("-----------------------------------------------------------\n");
	PRINT_STAT(no_sym);
	PRINT_STAT(no_insn);
	PRINT_STAT(no_insn_ops);
	PRINT_STAT(no_mem_ops);
	PRINT_STAT(no_reg);
	PRINT_STAT(no_dbginfo);
	PRINT_STAT(no_cuinfo);
	PRINT_STAT(no_var);
	PRINT_STAT(no_typeinfo);
	PRINT_STAT(invalid_size);
	PRINT_STAT(bad_offset);
	PRINT_STAT(bad_addr);
	PRINT_STAT(rejected_addr);
	PRINT_STAT(insn_track);
	printf("\n");

#undef PRINT_STAT
}

static void json_escape(FILE *fp, const char *str)
{
	if (!str)
		return;

	for (const unsigned char *p = (const unsigned char *)str; *p; ) {
		unsigned char c = *p;
		size_t len, i;
		bool valid = true;

		switch (c) {
		case '"':
			fputs("\\\"", fp);
			p++;
			continue;
		case '\\':
			fputs("\\\\", fp);
			p++;
			continue;
		case '\b':
			fputs("\\b", fp);
			p++;
			continue;
		case '\f':
			fputs("\\f", fp);
			p++;
			continue;
		case '\n':
			fputs("\\n", fp);
			p++;
			continue;
		case '\r':
			fputs("\\r", fp);
			p++;
			continue;
		case '\t':
			fputs("\\t", fp);
			p++;
			continue;
		default:
			break;
		}

		if (c < 0x20) {
			fprintf(fp, "\\u%04x", c);
			p++;
			continue;
		}

		if (c < 0x80) {
			fputc(c, fp);
			p++;
			continue;
		}

		/*
		 * A multi-byte sequence: 2 bytes for C2-DF, 3 for E0-EF and
		 * 4 for F0-F4, the remaining lead bytes (C0, C1, F5-FF) can
		 * only start overlong, surrogate or out-of-range encodings.
		 */
		if (c >= 0xc2 && c <= 0xdf)
			len = 2;
		else if (c >= 0xe0 && c <= 0xef)
			len = 3;
		else if (c >= 0xf0 && c <= 0xf4)
			len = 4;
		else
			valid = false;

		for (i = 1; valid && i < len; i++)
			if ((p[i] & 0xc0) != 0x80)
				valid = false;

		/* Reject overlong encodings, surrogates and values past U+10FFFF. */
		if (valid) {
			unsigned char c1 = p[1];

			if ((c == 0xe0 && c1 < 0xa0) ||
			    (c == 0xed && c1 >= 0xa0) ||
			    (c == 0xf0 && c1 < 0x90) ||
			    (c == 0xf4 && c1 >= 0x90))
				valid = false;
		}

		if (valid) {
			fwrite(p, 1, len, fp);
			p += len;
		} else {
			fputs("\\ufffd", fp);
			p++;
		}
	}
}

/* Spaces per nesting level, just to make the output readable. */
#define JSON_INDENT 4

static void json_indent(FILE *fp, int level)
{
	fprintf(fp, "%*s", level * JSON_INDENT, "");
}

/*
 * The "key": value pairs of an object, with the key at the given nesting
 * level and the comma that separates it from the previous one; *first
 * tracks whether this is the object's first field.
 */
static void json_str_field(FILE *fp, const char *key, const char *val,
			   int level, bool *first)
{
	fputs(*first ? "\n" : ",\n", fp);
	*first = false;
	json_indent(fp, level);
	fprintf(fp, "\"%s\": ", key);

	if (val) {
		fputc('"', fp);
		json_escape(fp, val);
		fputc('"', fp);
	} else {
		fputs("null", fp);
	}
}

static void json_int_field(FILE *fp, const char *key, int val, int level,
			   bool *first)
{
	fputs(*first ? "\n" : ",\n", fp);
	*first = false;
	json_indent(fp, level);
	fprintf(fp, "\"%s\": %d", key, val);
}

static void json_u64_field(FILE *fp, const char *key, u64 val, int level,
			   bool *first)
{
	fputs(*first ? "\n" : ",\n", fp);
	*first = false;
	json_indent(fp, level);
	fprintf(fp, "\"%s\": %" PRIu64, key, val);
}

/*
 * JSON export of the data-type access profile, to be consumed by tools
 * like pahole.  For each (dso, data type) it emits the member tree and
 * the per-event, per-offset access histograms so the consumer can
 * highlight hot/co-accessed fields and suggest cacheline groups.
 *
 * This is a stable ABI, versioned by the top level "version" field so
 * that a consumer can tell what it is parsing; pahole parses it, so
 * think twice before changing field names or types; the indentation
 * (4 spaces per nesting level, arrays closing on the line of their last
 * element) is only to help humans inspect the output and is not part of
 * the ABI.
 *
 * The document is a single object with three entries: the schema
 * version, the machine the profile was captured on - the same
 * information 'perf report --header-only' prints for the perf.data
 * file, plus the cacheline size the histograms were collected with -
 * and then one entry per DSO (binary) with the types that had hits in
 * it:
 *
 * {
 *     "version": 1,
 *     "machine": {
 *         "hostname": "<as in 'perf report --header-only'>",
 *         "os_release": "<kernel release>",
 *         "perf_version": "<perf version>",
 *         "arch": "<uname.machine>",
 *         "nrcpus_online": <int>,
 *         "nrcpus_avail": <int>,
 *         "cpudesc": "<model name>",
 *         "cpuid": "<cpuid>",
 *         "total_memory_kb": <u64>,
 *         "cmdline": [ "<perf argv0>", "<perf argv1>", ... ],
 *         "captured_on": "<the mtime of the perf.data file, as seen on the machine doing the analysis>",
 *         "cacheline_size": <bytes>
 *     },
 *     "dsos": [
 *         { "dso": "<dso long name>",
 *           "build_id": "<build ID hex, or null>",
 *           "types": [
 *               { "type": "<type name>",
 *                 "size": <bytes>,
 *                 "members": [                  # member tree, recursive
 *                     { "type": "<type name>", "name": "<member var name or "">",
 *                       "offset": <int, absolute within the outermost type>,
 *                       "size": <bytes>, "truncated": <bool, omitted when false>,
 *                       "children": [                      # leaves omit it
 *                           <nested members, same shape> ]
 *                     },
 *                     ...
 *                 ],
 *                 "histograms": [               # one entry per event with samples
 *                     { "event": "<event name>",
 *                       "total_samples": <u64>,
 *                       "total_period": <u64>,
 *                       "samples": [ { "offset": <int>, "nr_samples_load": <int>,
 *                                      "nr_samples_store": <int>,
 *                                      "period_load": <u64>,
 *                                      "period_store": <u64> }, ... ]
 *                     },
 *                     ...
 *                 ]
 *               },
 *               ...
 *           ]
 *         },
 *         ...
 *     ]
 * }
 *
 *   The DSO centric grouping is what a consumer such as pahole needs:
 *   pahole works on one DSO per session, so it takes the profile, looks
 *   up the entry for the build ID of the binary it is analyzing and gets
 *   exactly the types of that binary that were hit, together with the
 *   machine the profile came from.  Same-named types resolved in
 *   different DSOs are separate objects, in separate DSO entries, and
 *   "size" is in bytes so that a consumer can detect a mismatch even
 *   when the build ID is not available.
 *
 *   "dso" is the DSO long name (the vmlinux or .ko path when known,
 *   the binary path, "[kernel.kallsyms]_text" for a kallsyms-only
 *   kernel), except that a DSO opened through the ~/.debug build-id
 *   cache, which is the default, is named by its path in that cache,
 *   e.g. "/home/acme/.debug/.build-id/de/e74c...aaa4/elf" rather than
 *   by the vmlinux path: in a system-wide perf mem record profile 693
 *   of the 694 objects came out that way, with only the synthesized
 *   vdso carrying a real path.  "children" is present only for members
 *   that have children: a leaf member carries just "type", "name",
 *   "offset" and "size", with no "children" key at all, and those are
 *   the majority (5200 of 6788 members in that same profile).  A member
 *   whose children were cut off at the member nesting bound, see
 *   MAX_MEMBER_DEPTH in annotate-data.c, carries "truncated": true, so
 *   that a consumer can tell such a member from one whose tree really
 *   ends there.
 *
 *   "build_id" is its 40-hex-char build ID, null when the
 *   DSO has none (--no-buildid, anonymous DSOs).  The build ID, not
 *   the path, is the portable identity: paths differ across machines,
 *   while a build ID lets a consumer fetch the exact matching binary
 *   or debuginfo from the ~/.debug build-id cache or debuginfod and
 *   positively verify it is analyzing the same binary that was
 *   profiled, instead of only guessing from "size" that it is.  A
 *   null build ID means "unverified": fall back to name+size matching.
 *
 *   The (DSO, build ID) identity is also what makes a type centric view
 *   possible for the data structures that are part of an ABI, which is
 *   not implemented yet, neither in perf nor in its consumers: the same
 *   library build (the same build ID) profiled in different workloads
 *   can be compared, and the structures shared across an ABI boundary -
 *   a libc struct, the vDSO, the structures an out of tree kernel module
 *   or a BPF program shares with the kernel - can be tracked as they
 *   change from release to release.  This is about the identity a
 *   consumer needs for that, not about the view itself.
 *
 *   Note that "dsos" gathers the DSOs of the host machine and of the
 *   guest machines of a perf.data file recorded with --guest*, while
 *   "machine" describes the machine the profile was captured on.
 *
 *   The histogram is keyed by (type, member offset), and the same offset
 *   is touched by both loads and stores at different call sites, so the
 *   load/store direction is NOT a property of the offset.  Each access is
 *   therefore counted in separate per-direction counters
 *   (nr_samples_load / nr_samples_store, period_load / period_store) taken
 *   from the semantic role the architecture's operand parser assigns to
 *   the memory operand: a store has it as its TARGET, a load as its
 *   SOURCE.  Keeping the two directions separate means pahole can report
 *   per-member reads vs writes (nr_reads / nr_writes) without the last
 *   writer at an offset erasing the other direction - which is the common
 *   case for shared kernel structs (e.g. struct sock fields read in one
 *   path, written in another).  On x86, the parser follows the AT&T text
 *   convention, so instructions that only read the memory operand even
 *   when it is in the target slot (cmp, test, bt - e.g.
 *   "cmpw $2, 0x226(%rdx)" tests sk->sk_type) are corrected to loads at
 *   profile time; that is an x86 parser detail, not part of the format.
 *
 *   Note on atomics / RMW: an instruction such as "lock incl (%rax)" has
 *   the memory operand as its TARGET and is counted purely as a store.
 *   For cache-invalidation / false-sharing analysis that is the intended
 *   semantics - a read-modify-write takes the cacheline exclusive - but it
 *   is a deliberate judgment call baked into the direction, not a measured
 *   load+store split; keep it in mind when reading hot-store fields.
 */

static void member_to_json(FILE *fp, struct annotated_member *member, int level);

static void members_to_json(FILE *fp, struct list_head *head, int level)
{
	struct annotated_member *child;
	int n = 0;

	list_for_each_entry(child, head, node) {
		if (n++)
			fputc(',', fp);
		member_to_json(fp, child, level);
	}
}

static void member_to_json(FILE *fp, struct annotated_member *member, int level)
{
	fputc('\n', fp);
	json_indent(fp, level);
	fputs("{ \"type\": \"", fp);
	json_escape(fp, member->type_name ?: "");
	fputs("\", \"name\": \"", fp);
	json_escape(fp, member->var_name ?: "");
	fprintf(fp, "\", \"offset\": %d, \"size\": %d",
		member->offset, member->size);

	if (member->truncated)
		fputs(", \"truncated\": true", fp);

	if (!list_empty(&member->children)) {
		fputs(", \"children\": [", fp);
		members_to_json(fp, &member->children, level + 1);
		fputs(" ]\n", fp);
		json_indent(fp, level);
		fputc('}', fp);
	} else {
		fputs(" }", fp);
	}
}

struct adt_json_priv {
	FILE *fp;
	struct evlist *evlist;
	bool first_dso;
};

/* Whether this data type got any sample in any of its histograms. */
static bool adt_has_hits(struct annotated_data_type *adt)
{
	int i;

	if (adt->nr_histograms == 0 || adt->histograms == NULL)
		return false;

	for (i = 0; i < adt->nr_histograms; i++) {
		if (adt->histograms[i] && adt->histograms[i]->nr_samples)
			return true;
	}
	return false;
}

static void adt_to_json(FILE *fp, struct annotated_data_type *adt,
			struct evlist *evlist, bool first, int level)
{
	struct evsel *evsel;
	struct type_hist *h;
	int off, n;
	bool he = false;

	if (!first)
		fputc(',', fp);
	fputc('\n', fp);
	json_indent(fp, level);
	fputs("{ \"type\": \"", fp);
	json_escape(fp, adt->self.type_name ?: "");
	fputs("\",\n", fp);
	json_indent(fp, level + 1);
	fprintf(fp, "\"size\": %d,\n", adt->self.size);
	json_indent(fp, level + 1);
	fputs("\"members\": [", fp);
	members_to_json(fp, &adt->self.children, level + 2);
	fputs(" ],\n", fp);
	json_indent(fp, level + 1);
	fputs("\"histograms\": [", fp);

	evlist__for_each_entry(evlist, evsel) {
		if (evsel->core.idx >= adt->nr_histograms)
			continue;
		h = adt->histograms[evsel->core.idx];
		if (h == NULL || h->nr_samples == 0)
			continue;
		if (he)
			fputc(',', fp);
		he = true;
		fputc('\n', fp);
		json_indent(fp, level + 2);
		fputs("{ \"event\": \"", fp);
		json_escape(fp, evsel->name ?: "");
		fputs("\",\n", fp);
		json_indent(fp, level + 3);
		fprintf(fp, "\"total_samples\": %" PRIu64 ",\n", h->nr_samples);
		json_indent(fp, level + 3);
		fprintf(fp, "\"total_period\": %" PRIu64 ",\n", h->period);
		json_indent(fp, level + 3);
		fputs("\"samples\": [", fp);
		n = 0;
		for (off = 0; off < adt->self.size; off++) {
			struct type_hist_entry *e = &h->addr[off];

			if (e->nr_samples_load + e->nr_samples_store == 0 &&
			    e->period_load + e->period_store == 0)
				continue;
			if (n++)
				fputc(',', fp);
			fputs(" { \"offset\": ", fp);
			fprintf(fp, "%d", off);
			fprintf(fp, ", \"nr_samples_load\": %d, "
				"\"nr_samples_store\": %d, \"period_load\": %"
				PRIu64 ", \"period_store\": %" PRIu64 " }",
				e->nr_samples_load, e->nr_samples_store,
				e->period_load, e->period_store);
		}
		fputs(" ] }", fp);
	}
	fputs("\n", fp);
	json_indent(fp, level + 1);
	fputs("]\n", fp);
	json_indent(fp, level);
	fputc('}', fp);
}

static void dso_to_json(FILE *fp, struct dso *dso, struct adt_json_priv *p,
			int level)
{
	struct rb_root *root = dso__data_types(dso);
	struct annotated_data_type *adt;
	struct rb_node *node;
	bool first = true;

	if (!p->first_dso)
		fputc(',', fp);
	fputc('\n', fp);
	json_indent(fp, level);
	fputs("{ \"dso\": \"", fp);
	json_escape(fp, dso__long_name(dso));
	fputs("\",\n", fp);
	json_indent(fp, level + 1);
	fputs("\"build_id\": ", fp);
	if (dso__has_build_id(dso)) {
		char sbuild_id[SBUILD_ID_SIZE];

		build_id__snprintf(dso__bid(dso), sbuild_id, sizeof(sbuild_id));
		fprintf(fp, "\"%s\"", sbuild_id);
	} else {
		fputs("null", fp);
	}
	fputs(",\n", fp);
	json_indent(fp, level + 1);
	fputs("\"types\": [", fp);

	for (node = rb_first(root); node; node = rb_next(node)) {
		adt = rb_entry(node, struct annotated_data_type, node);

		if (!adt_has_hits(adt))
			continue;
		adt_to_json(fp, adt, p->evlist, first, level + 2);
		first = false;
	}
	fputs("\n", fp);
	json_indent(fp, level + 1);
	fputs("]\n", fp);
	json_indent(fp, level);
	fputc('}', fp);
	p->first_dso = false;
}

/*
 * The machine the profile was captured on: the same information 'perf
 * report --header-only' prints for the perf.data file, plus the
 * cacheline size the histograms were collected with.  A consumer such as
 * pahole uses it to tell where the profile came from (a struct layout
 * that is hot on one machine may not be on another) and to group the
 * offsets into cachelines the way perf did.
 */
static void machine_to_json(FILE *fp, struct perf_session *session,
			    unsigned int cln_size)
{
	struct perf_env *env = &session->header.env;
	char captured_on[32] = "";
	struct stat st;
	bool first = true;
	int i;

	if (fstat(perf_data__fd(session->data), &st) == 0) {
		struct tm tm;

		if (localtime_r(&st.st_mtime, &tm))
			strftime(captured_on, sizeof(captured_on),
				 "%a %b %e %H:%M:%S %Y", &tm);
	}

	fputs("{\n", fp);
	json_indent(fp, 1);
	fputs("\"version\": 1,\n", fp);
	json_indent(fp, 1);
	fputs("\"machine\": {", fp);
	/* The fields come with the newline and the comma that precedes them. */
	json_str_field(fp, "hostname", env->hostname, 2, &first);
	json_str_field(fp, "os_release", env->os_release, 2, &first);
	json_str_field(fp, "perf_version", env->version, 2, &first);
	json_str_field(fp, "arch", env->arch, 2, &first);
	json_int_field(fp, "nrcpus_online", env->nr_cpus_online, 2, &first);
	json_int_field(fp, "nrcpus_avail", env->nr_cpus_avail, 2, &first);
	json_str_field(fp, "cpudesc", env->cpu_desc, 2, &first);
	json_str_field(fp, "cpuid", env->cpuid, 2, &first);
	json_u64_field(fp, "total_memory_kb", env->total_mem, 2, &first);

	fputs(",\n", fp);
	json_indent(fp, 2);
	fputs("\"cmdline\": [", fp);
	for (i = 0; i < env->nr_cmdline; i++) {
		fprintf(fp, "%s \"", i ? "," : "");
		json_escape(fp, env->cmdline_argv[i] ?: "");
		fputc('"', fp);
	}
	fputs(" ]", fp);
	first = false;

	json_str_field(fp, "captured_on", captured_on[0] ? captured_on : NULL,
		       2, &first);
	json_u64_field(fp, "cacheline_size", cln_size, 2, &first);
	fputs("\n", fp);
	json_indent(fp, 1);
	fputs("},\n", fp);
	json_indent(fp, 1);
	fputs("\"dsos\": [", fp);
}

static int adt_json_dso_cb(struct dso *dso, struct machine *machine __maybe_unused,
			   void *priv)
{
	struct adt_json_priv *p = priv;
	struct rb_root *root = dso__data_types(dso);
	struct annotated_data_type *adt;
	struct rb_node *node;

	if (RB_EMPTY_ROOT(root))
		return 0;

	/* Skip the DSOs without a single type that had hits. */
	for (node = rb_first(root); node; node = rb_next(node)) {
		adt = rb_entry(node, struct annotated_data_type, node);
		if (adt_has_hits(adt))
			break;
	}
	if (node == NULL)
		return 0;

	dso_to_json(p->fp, dso, p, 2);
	return 0;
}

int perf_session__annotate_data_to_json(struct perf_session *session, const char *filename)
{
	struct adt_json_priv priv;
	struct rb_node *nd;
	FILE *fp = stdout;
	unsigned int cln_size;
	int ret;

	if (filename && strcmp(filename, "-") != 0) {
		fp = fopen(filename, "w");
		if (fp == NULL) {
			pr_err("Cannot open %s for JSON output\n", filename);
			return -1;
		}
	}

	cln_size = session->header.env.cln_size;
	if (!cln_size)
		cln_size = cacheline_size();
	if (!cln_size)
		cln_size = DEFAULT_CACHELINE_SIZE;

	priv.fp = fp;
	priv.evlist = session->evlist;
	priv.first_dso = true;

	machine_to_json(fp, session, cln_size);
	ret = machine__for_each_dso(&session->machines.host, adt_json_dso_cb, &priv);
	if (ret)
		goto out;

	/*
	 * Also cover guest machines; data types can live in a guest
	 * kernel/userspace DSO too.
	 */
	for (nd = rb_first_cached(&session->machines.guests); nd; nd = rb_next(nd)) {
		struct machine *pos = rb_entry(nd, struct machine, rb_node);

		ret = machine__for_each_dso(pos, adt_json_dso_cb, &priv);
		if (ret)
			goto out;
	}

	fputs("\n", fp);
	json_indent(fp, 1);
	fputs("]\n}\n", fp);

out:
	if (fp != stdout) {
		fclose(fp);
		if (ret)
			unlink(filename);
	}
	return ret;
}
