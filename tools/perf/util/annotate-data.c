/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Convert sample address to data type using DWARF debug info.
 *
 * Written by Namhyung Kim <namhyung@kernel.org>
 */

#include <stdio.h>
#include <stdlib.h>

#include "annotate.h"
#include "annotate-data.h"
#include "debuginfo.h"
#include "debug.h"
#include "dso.h"
#include "dwarf-regs.h"
#include "evsel.h"
#include "evlist.h"
#include "map.h"
#include "map_symbol.h"
#include "strbuf.h"
#include "symbol.h"
#include "symbol_conf.h"

/* Pseudo data types */
struct annotated_data_type unknown_type = {
	.self = {
		.type_name = (char *)"(unknown)",
		.children = LIST_HEAD_INIT(unknown_type.self.children),
	},
};

struct annotated_data_type stackop_type = {
	.self = {
		.type_name = (char *)"(stack operation)",
		.children = LIST_HEAD_INIT(stackop_type.self.children),
	},
};

struct annotated_data_type canary_type = {
	.self = {
		.type_name = (char *)"(stack canary)",
		.children = LIST_HEAD_INIT(canary_type.self.children),
	},
};

/* Data type collection debug statistics */
struct annotated_data_stat ann_data_stat;

/*
 * Type information in a register, valid when ok is true.
 * The scratch registers are invalidated after a function call.
 */
struct type_state_reg {
	Dwarf_Die type;
	bool ok;
	bool scratch;
};

/* Type information in a stack location, dynamically allocated */
struct type_state_stack {
	struct list_head list;
	Dwarf_Die type;
	int offset;
	int size;
	bool compound;
};

/* FIXME: This should be arch-dependent */
#define TYPE_STATE_MAX_REGS  16

/*
 * State table to maintain type info in each register and stack location.
 * It'll be updated when new variable is allocated or type info is moved
 * to a new location (register or stack).  As it'd be used with the
 * shortest path of basic blocks, it only maintains a single table.
 */
struct type_state {
	struct type_state_reg regs[TYPE_STATE_MAX_REGS];
	struct list_head stack_vars;
	int ret_reg;
};

static bool has_reg_type(struct type_state *state, int reg)
{
	return (unsigned)reg < ARRAY_SIZE(state->regs);
}

void init_type_state(struct type_state *state, struct arch *arch)
{
	memset(state, 0, sizeof(*state));
	INIT_LIST_HEAD(&state->stack_vars);

	if (arch__is(arch, "x86")) {
		state->regs[0].scratch = true;
		state->regs[1].scratch = true;
		state->regs[2].scratch = true;
		state->regs[4].scratch = true;
		state->regs[5].scratch = true;
		state->regs[8].scratch = true;
		state->regs[9].scratch = true;
		state->regs[10].scratch = true;
		state->regs[11].scratch = true;
		state->ret_reg = 0;
	}
}

void exit_type_state(struct type_state *state)
{
	struct type_state_stack *stack, *tmp;

	list_for_each_entry_safe(stack, tmp, &state->stack_vars, list) {
		list_del(&stack->list);
		free(stack);
	}
}

static void debug_print_type_name(Dwarf_Die *die)
{
	struct strbuf sb;
	char *str;

	if (!verbose)
		return;

	strbuf_init(&sb, 32);
	__die_get_typename(die, &sb);
	str = strbuf_detach(&sb, NULL);
	pr_debug("%s (die:%lx)\n", str, dwarf_dieoffset(die));
	free(str);
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

/* Recursively add new members for struct/union */
static int __add_member_cb(Dwarf_Die *die, void *arg)
{
	struct annotated_member *parent = arg;
	struct annotated_member *member;
	Dwarf_Die member_type, die_mem;
	Dwarf_Word size, loc;
	Dwarf_Attribute attr;
	struct strbuf sb;
	int tag;

	if (dwarf_tag(die) != DW_TAG_member)
		return DIE_FIND_CB_SIBLING;

	member = zalloc(sizeof(*member));
	if (member == NULL)
		return DIE_FIND_CB_END;

	strbuf_init(&sb, 32);
	die_get_typename(die, &sb);

	die_get_real_type(die, &member_type);
	if (dwarf_aggregate_size(&member_type, &size) < 0)
		size = 0;

	if (!dwarf_attr_integrate(die, DW_AT_data_member_location, &attr))
		loc = 0;
	else
		dwarf_formudata(&attr, &loc);

	member->type_name = strbuf_detach(&sb, NULL);
	/* member->var_name can be NULL */
	if (dwarf_diename(die))
		member->var_name = strdup(dwarf_diename(die));
	member->size = size;
	member->offset = loc + parent->offset;
	INIT_LIST_HEAD(&member->children);
	list_add_tail(&member->node, &parent->children);

	tag = dwarf_tag(&member_type);
	switch (tag) {
	case DW_TAG_structure_type:
	case DW_TAG_union_type:
		die_find_child(&member_type, __add_member_cb, member, &die_mem);
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
		free(child->type_name);
		free(child->var_name);
		free(child);
	}
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
	if (__die_get_typename(type_die, &sb) < 0)
		strbuf_add(&sb, "(unknown type)", 14);
	type_name = strbuf_detach(&sb, NULL);
	dwarf_aggregate_size(type_die, &size);

	/* Check existing nodes in dso->data_types tree */
	key.self.type_name = type_name;
	key.self.size = size;
	node = rb_find(&key, &dso->data_types, data_type_cmp);
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

	rb_add(&result->node, &dso->data_types, data_type_less);
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

/* The type info will be saved in @type_die */
static int check_variable(Dwarf_Die *var_die, Dwarf_Die *type_die, int offset,
			  bool is_pointer)
{
	Dwarf_Word size;

	/* Get the type of the variable */
	if (die_get_real_type(var_die, type_die) == NULL) {
		pr_debug("variable has no type\n");
		ann_data_stat.no_typeinfo++;
		return -1;
	}

	/*
	 * Usually it expects a pointer type for a memory access.
	 * Convert to a real type it points to.  But global variables
	 * and local variables are accessed directly without a pointer.
	 */
	if (is_pointer) {
		if ((dwarf_tag(type_die) != DW_TAG_pointer_type &&
		     dwarf_tag(type_die) != DW_TAG_array_type) ||
		    die_get_real_type(type_die, type_die) == NULL) {
			pr_debug("no pointer or no type\n");
			ann_data_stat.no_typeinfo++;
			return -1;
		}
	}

	/* Get the size of the actual type */
	if (dwarf_aggregate_size(type_die, &size) < 0) {
		pr_debug("type size is unknown\n");
		ann_data_stat.invalid_size++;
		return -1;
	}

	/* Minimal sanity check */
	if ((unsigned)offset >= size) {
		pr_debug("offset: %d is bigger than size: %lu\n", offset, size);
		ann_data_stat.bad_offset++;
		return -1;
	}

	return 0;
}

static struct type_state_stack *find_stack_state(struct type_state *state,
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

static void set_stack_state(struct type_state_stack *stack, int offset,
			    Dwarf_Die *type_die)
{
	int tag;
	Dwarf_Word size;

	if (dwarf_aggregate_size(type_die, &size) < 0)
		size = 0;

	tag = dwarf_tag(type_die);

	stack->type = *type_die;
	stack->size = size;
	stack->offset = offset;

	switch (tag) {
	case DW_TAG_structure_type:
	case DW_TAG_union_type:
		stack->compound = true;
		break;
	default:
		stack->compound = false;
		break;
	}
}

static struct type_state_stack *findnew_stack_state(struct type_state *state,
						    int offset, Dwarf_Die *type_die)
{
	struct type_state_stack *stack = find_stack_state(state, offset);

	if (stack) {
		set_stack_state(stack, offset, type_die);
		return stack;
	}

	stack = malloc(sizeof(*stack));
	if (stack) {
		set_stack_state(stack, offset, type_die);
		list_add(&stack->list, &state->stack_vars);
	}
	return stack;
}

/**
 * update_var_state - Update type state using given variables
 * @state: type state table
 * @dloc: data location info
 * @addr: instruction address to update
 * @var_types: list of variables with type info
 *
 * This function fills the @state table using @var_types info.  Each variable
 * is used only at the given location and updates an entry in the table.
 */
void update_var_state(struct type_state *state, struct data_loc_info *dloc,
		      u64 addr, u64 off, struct die_var_type *var_types)
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
		if (var->addr != addr)
			continue;
		/* Get the type DIE using the offset */
		if (!dwarf_offdie(dloc->di->dbg, var->die_off, &mem_die))
			continue;

		if (var->reg == DWARF_REG_FB) {
			findnew_stack_state(state, var->offset, &mem_die);
			pr_debug("var [%lx] stack fbreg (%x, %d) type=", off, var->offset, var->offset);
			debug_print_type_name(&mem_die);
		} else if (var->reg == fbreg) {
			findnew_stack_state(state, var->offset - fb_offset, &mem_die);
			pr_debug("var [%lx] stack cfa (%x, %d) fb-offset=%d type=", off, var->offset - fb_offset, var->offset - fb_offset, fb_offset);
			debug_print_type_name(&mem_die);
		} else if (has_reg_type(state, var->reg) && var->offset == 0) {
			struct type_state_reg *reg;

			reg = &state->regs[var->reg];
			reg->type = mem_die;
			reg->ok = true;
			pr_debug("var [%lx] reg%d type=", off, var->reg);
			debug_print_type_name(&mem_die);
		}
	}
}

static bool get_global_var_type(Dwarf_Die *cu_die, struct map_symbol *ms, u64 ip,
				u64 var_addr, const char *var_name, int var_offset,
				Dwarf_Die *type_die)
{
	u64 pc;
	int offset = var_offset;
	bool is_pointer = false;
	Dwarf_Die var_die;

	pc = map__rip_2objdump(ms->map, ip);

	/* Try to get the variable by address first */
	if (die_find_variable_by_addr(cu_die, pc, var_addr, &var_die, &offset) &&
	    check_variable(&var_die, type_die, offset, is_pointer) == 0 &&
	    die_get_member_type(type_die, offset, type_die))
		return true;

	if (var_name == NULL)
		return false;

	offset = var_offset;

	/* Try to get the name of global variable */
	if (die_find_variable_at(cu_die, var_name, pc, &var_die) &&
	    check_variable(&var_die, type_die, offset, is_pointer) == 0 &&
	    die_get_member_type(type_die, offset, type_die))
		return true;

	return false;
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
void update_insn_state(struct type_state *state, struct data_loc_info *dloc,
		       void *cu_die, struct disasm_line *dl)
{
	struct annotated_insn_loc loc;
	struct annotated_op_loc *src = &loc.ops[INSN_OP_SOURCE];
	struct annotated_op_loc *dst = &loc.ops[INSN_OP_TARGET];
	Dwarf_Die type_die;
	int fbreg = dloc->fbreg;
	int fboff = 0;

	if (ins__is_call(&dl->ins)) {
		Dwarf_Die func_die;

		/* __fentry__ will preserve all registers */
		if (dl->ops.target.sym &&
		    !strcmp(dl->ops.target.sym->name, "__fentry__"))
			return;

		/* Otherwise invalidate scratch registers after call */
		for (unsigned i = 0; i < ARRAY_SIZE(state->regs); i++) {
			if (state->regs[i].scratch)
				state->regs[i].ok = false;
		}

		/* Update register with the return type (if any) */
		if (die_find_realfunc(cu_die, dl->ops.target.addr, &func_die) &&
		    die_get_real_type(&func_die, &type_die)) {
			state->regs[state->ret_reg].type = type_die;
			state->regs[state->ret_reg].ok = true;
			pr_debug("fun [%lx] reg0 return from %s type=", dl->al.offset, dwarf_diename(&func_die));
			debug_print_type_name(&type_die);
		}
		return;
	}

	/* FIXME: remove x86 specific code and handle more instructions like LEA */
	if (!strstr(dl->ins.name, "mov"))
		return;

	if (annotate_get_insn_location(dloc->arch, dl, &loc) < 0) {
		pr_debug("failed to get mov insn loc\n");
		return;
	}

	if (dloc->fb_cfa) {
		u64 ip = dloc->ms->sym->start + dl->al.offset;
		u64 pc = map__rip_2objdump(dloc->ms->map, ip);

		if (die_get_cfa(dloc->di->dbg, pc, &fbreg, &fboff) < 0)
			fbreg = -1;
	}

	/* Case 1. register to register or segment:offset to register transfers */
	if (!src->mem_ref && !dst->mem_ref) {
		if (!has_reg_type(state, dst->reg1))
			return;

		if (has_reg_type(state, src->reg1)) {
			state->regs[dst->reg1] = state->regs[src->reg1];
			if (state->regs[dst->reg1].ok) {
				pr_debug("mov [%lx] reg%d -> reg%d type=", dl->al.offset, src->reg1, dst->reg1);
				debug_print_type_name(&state->regs[dst->reg1].type);
			}
		} else if (dloc->ms->map->dso->kernel &&
			   src->segment == INSN_SEG_X86_GS) {
			struct map_symbol *ms = dloc->ms;
			int offset = src->offset;
			u64 ip = ms->sym->start + dl->al.offset;
			const char *var_name = NULL;
			u64 var_addr;

			/*
			 * In kernel, %gs points to a per-cpu region for the
			 * current CPU.  Access with a constant offset should
			 * be treated as a global variable access.
			 */
			var_addr = src->offset;
			get_percpu_var_info(dloc->thread, ms, dloc->cpumode,
					    var_addr, &var_name, &offset);

			if (get_global_var_type(cu_die, ms, ip, var_addr,
						var_name, offset, &type_die)) {
				state->regs[dst->reg1].type = type_die;
				state->regs[dst->reg1].ok = true;
				pr_debug("mov [%lx] percpu -> reg%d type=", dl->al.offset, dst->reg1);
				debug_print_type_name(&state->regs[dst->reg1].type);
			}
		} else
			state->regs[dst->reg1].ok = false;
	}
	/* Case 2. memory to register transers */
	if (src->mem_ref && !dst->mem_ref) {
		int sreg = src->reg1;

		if (!has_reg_type(state, dst->reg1))
			return;

retry:
		/* Check if it's a global variable */
		if (sreg == DWARF_REG_PC) {
			struct map_symbol *ms = dloc->ms;
			int offset = src->offset;
			u64 ip = ms->sym->start + dl->al.offset;
			const char *var_name = NULL;
			u64 var_addr;

			var_addr = annotate_calc_pcrel(ms, ip, offset, dl);

			get_global_var_info(dloc->thread, ms, ip, dl,
					    dloc->cpumode, &var_addr,
					    &var_name, &offset);

			if (get_global_var_type(cu_die, ms, ip, var_addr,
						var_name, offset, &type_die)) {
				state->regs[dst->reg1].type = type_die;
				state->regs[dst->reg1].ok = true;
				pr_debug("mov [%lx] PC-rel -> reg%d type=", dl->al.offset, dst->reg1);
				debug_print_type_name(&type_die);
			} else {
				if (var_name)
					pr_debug("??? [%lx] PC-rel (%lx: %s%+d)\n", dl->al.offset, var_addr, var_name, offset);
				state->regs[dst->reg1].ok = false;
			}
		}
		/* And check stack variables with offset */
		else if (sreg == fbreg) {
			struct type_state_stack *stack;
			int offset = src->offset - fboff;

			stack = find_stack_state(state, offset);
			if (stack && die_get_member_type(&stack->type,
							 offset - stack->offset,
							 &type_die)) {
				state->regs[dst->reg1].type = type_die;
				state->regs[dst->reg1].ok = true;
				pr_debug("mov [%lx] stack (-%#x, %d) -> reg%d type=", dl->al.offset, -offset, offset, dst->reg1);
				debug_print_type_name(&type_die);
			} else
				state->regs[dst->reg1].ok = false;
		}
		/* And then dereference the pointer if it has one */
		else if (has_reg_type(state, sreg) && state->regs[sreg].ok &&
			 die_deref_ptr_type(&state->regs[sreg].type,
					    src->offset, &type_die)) {
			state->regs[dst->reg1].type = type_die;
			state->regs[dst->reg1].ok = true;
			pr_debug("mov [%lx] %#x(reg%d) -> reg%d type=", dl->al.offset, src->offset, sreg, dst->reg1);
			debug_print_type_name(&type_die);
		}
		/* Or try another register if any */
		else if (src->multi_regs && sreg == src->reg1 &&
			 src->reg1 != src->reg2) {
			sreg = src->reg2;
			goto retry;
		}
		/* It failed to get a type info, mark it as invalid */
		else {
			state->regs[dst->reg1].ok = false;
		}
	}
	/* Case 3. register to memory transfers */
	if (!src->mem_ref && dst->mem_ref) {
		if (!has_reg_type(state, src->reg1) ||
		    !state->regs[src->reg1].ok)
			return;

		/* Check stack variables with offset */
		if (dst->reg1 == fbreg) {
			struct type_state_stack *stack;
			int offset = dst->offset - fboff;

			stack = find_stack_state(state, offset);
			if (stack) {
				/*
				 * The source register is likely to hold a type
				 * of member if it's a compound type.  Do not
				 * update the stack variable type since we can
				 * get the member type later by using the
				 * die_get_member_type().
				 */
				if (!stack->compound)
					set_stack_state(stack, offset,
							&state->regs[src->reg1].type);
			} else {
				findnew_stack_state(state, offset,
						    &state->regs[src->reg1].type);
			}
			pr_debug("mov [%lx] reg%d -> stack (-%#x, %d) type=", dl->al.offset, src->reg1, -offset, offset);
			debug_print_type_name(&state->regs[src->reg1].type);
		}
		/*
		 * Ignore other transfers since it'd set a value in a struct
		 * and won't change the type.
		 */
	}
	/* Case 4. memory to memory transfers (not handled for now) */
}

/* Prepend this_list to full_list, removing duplicate disasm line */
static void prepend_basic_blocks(struct list_head *this_blocks,
				 struct list_head *full_blocks)
{
	struct annotated_basic_block *first_bb, *last_bb;

	last_bb = list_last_entry(this_blocks, typeof(*last_bb), list);
	first_bb = list_first_entry(full_blocks, typeof(*first_bb), list);

	if (list_empty(full_blocks))
		goto out;

	if (last_bb->end != first_bb->begin) {
		pr_debug("prepend basic blocks: mismatched disasm line %lx -> %lx\n",
			 last_bb->end->al.offset, first_bb->begin->al.offset);
		goto out;
	}

	/* Is the basic block have only one disasm_line? */
	if (last_bb->begin == last_bb->end) {
		list_del(&last_bb->list);
		free(last_bb);
		goto out;
	}

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

/* It's at the target address, check if it has a matching type */
static bool find_matching_type(struct type_state *state,
			       struct data_loc_info *dloc, int reg,
			       Dwarf_Die *type_die)
{
	Dwarf_Word size;

	if (state->regs[reg].ok) {
		int tag = dwarf_tag(&state->regs[reg].type);

		/*
		 * Normal registers should hold a pointer (or array) to
		 * dereference a memory location.
		 */
		if (tag != DW_TAG_pointer_type && tag != DW_TAG_array_type)
			return false;

		if (die_get_real_type(&state->regs[reg].type, type_die) == NULL)
			return false;

		dloc->type_offset = dloc->op->offset;

		/* Get the size of the actual type */
		if (dwarf_aggregate_size(type_die, &size) < 0 ||
		    (unsigned)dloc->type_offset >= size)
			return false;

		pr_debug("%s: [%lx] reg=%d offset=%d type=",
			 __func__, dloc->ip - dloc->ms->sym->start, reg, dloc->type_offset);
		debug_print_type_name(type_die);
		return true;
	}

	if (reg == dloc->fbreg) {
		struct type_state_stack *stack;

		stack = find_stack_state(state, dloc->type_offset);
		if (stack == NULL)
			return false;

		*type_die = stack->type;
		/* Update the type offset from the start of slot */
		dloc->type_offset -= stack->offset;

		pr_debug("%s: [%lx] stack offset=%d type=",
			 __func__, dloc->ip - dloc->ms->sym->start, dloc->type_offset);
		debug_print_type_name(type_die);
		return true;
	}

	if (dloc->fb_cfa) {
		struct type_state_stack *stack;
		u64 pc = map__rip_2objdump(dloc->ms->map, dloc->ip);
		int fbreg, fboff;

		if (die_get_cfa(dloc->di->dbg, pc, &fbreg, &fboff) < 0)
			fbreg = -1;

		if (reg != fbreg)
			return false;

		stack = find_stack_state(state, dloc->type_offset - fboff);
		if (stack == NULL)
			return false;

		*type_die = stack->type;
		/* Update the type offset from the start of slot */
		dloc->type_offset -= fboff + stack->offset;

		pr_debug("%s: [%lx] cfa stack offset=%d type_offset=%d type=",
			 __func__, dloc->ip - dloc->ms->sym->start,
			 dloc->type_offset + stack->offset, dloc->type_offset);
		debug_print_type_name(type_die);
		return true;
	}

	return false;
}

/* Iterate instructions in basic blocks and update type table */
static bool find_data_type_insn(struct data_loc_info *dloc, int reg,
				struct list_head *basic_blocks,
				struct die_var_type *var_types,
				Dwarf_Die *cu_die, Dwarf_Die *type_die)
{
	struct type_state state;
	struct symbol *sym = dloc->ms->sym;
	struct annotation *notes = symbol__annotation(sym);
	struct annotated_basic_block *bb;
	bool found = false;

	init_type_state(&state, dloc->arch);

	list_for_each_entry(bb, basic_blocks, list) {
		struct disasm_line *dl = bb->begin;

		pr_debug("bb: [%lx - %lx]\n", bb->begin->al.offset, bb->end->al.offset);
		list_for_each_entry_from(dl, &notes->src->source, al.node) {
			u64 this_ip = sym->start + dl->al.offset;
			u64 addr = map__rip_2objdump(dloc->ms->map, this_ip);

			/* Update variable type at this address */
			update_var_state(&state, dloc, addr, dl->al.offset, var_types);

			if (this_ip == dloc->ip) {
				found = find_matching_type(&state, dloc, reg,
							   type_die);
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
	return found;
}

/*
 * Construct a list of basic blocks for each scope with variables and try to find
 * the data type by updating a type state table through instructions.
 */
static int find_data_type_block(struct data_loc_info *dloc, int reg,
				Dwarf_Die *cu_die, Dwarf_Die *scopes,
				int nr_scopes, Dwarf_Die *type_die)
{
	LIST_HEAD(basic_blocks);
	struct die_var_type *var_types = NULL;
	u64 src_ip, dst_ip;
	int ret = -1;

	if (dloc->fb_cfa) {
		u64 pc = map__rip_2objdump(dloc->ms->map, dloc->ip);
		int fbreg, fboff;

		if (die_get_cfa(dloc->di->dbg, pc, &fbreg, &fboff) < 0)
			fbreg = -1;

		pr_debug("CFA reg=%d offset=%d\n", fbreg, fboff);
	}

	dst_ip = dloc->ip;
	for (int i = nr_scopes - 1; i >= 0; i--) {
		Dwarf_Addr base, start, end;
		LIST_HEAD(this_blocks);

		if (dwarf_ranges(&scopes[i], 0, &base, &start, &end) < 0)
			break;

		pr_debug("scope: [%d/%d] (die:%lx)\n", i + 1, nr_scopes, dwarf_dieoffset(&scopes[i]));
		src_ip = map__objdump_2rip(dloc->ms->map, start);

		/* Get basic blocks for this scope */
		if (annotate_get_basic_blocks(dloc->ms->sym, src_ip, dst_ip,
					      &this_blocks) < 0) {
			pr_debug("cannot find a basic block from %lx to %lx\n",
				 src_ip - dloc->ms->sym->start, dst_ip - dloc->ms->sym->start);
			continue;
		}
		prepend_basic_blocks(&this_blocks, &basic_blocks);

		/* Get variable info for this scope and add to var_types list */
		die_collect_vars(&scopes[i], &var_types);
		fixup_var_address(var_types, start);

		/* Find from start of this scope to the target instruction */
		if (find_data_type_insn(dloc, reg, &basic_blocks, var_types,
					cu_die, type_die)) {
			ret = 0;
			break;
		}

		/* Go up to the next scope and find blocks to the start */
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
	int reg, offset;
	int ret = -1;
	int i, nr_scopes;
	int fbreg = -1;
	int fb_offset = 0;
	bool is_fbreg = false;
	u64 pc;
	char buf[64];

	if (dloc->op->multi_regs)
		snprintf(buf, sizeof(buf), " or reg%d", dloc->op->reg2);
	else if (dloc->op->reg1 == DWARF_REG_PC)
		snprintf(buf, sizeof(buf), " (PC)");
	else
		buf[0] = '\0';

	pr_debug("-----------------------------------------------------------\n");
	pr_debug("%s [%lx] for reg%d%s in %s\n", __func__, dloc->ip - dloc->ms->sym->start,
		 dloc->op->reg1, buf, dloc->ms->sym->name);

	/*
	 * IP is a relative instruction address from the start of the map, as
	 * it can be randomized/relocated, it needs to translate to PC which is
	 * a file address for DWARF processing.
	 */
	pc = map__rip_2objdump(dloc->ms->map, dloc->ip);

	/* Get a compile_unit for this address */
	if (!find_cu_die(dloc->di, pc, &cu_die)) {
		pr_debug("cannot find CU for address %lx\n", pc);
		ann_data_stat.no_cuinfo++;
		return -1;
	}

	reg = loc->reg1;
	offset = loc->offset;

	pr_debug("CU die offset: %lx\n", dwarf_dieoffset(&cu_die));

	if (reg == DWARF_REG_PC) {
		if (die_find_variable_by_addr(&cu_die, pc, dloc->var_addr,
					      &var_die, &offset)) {
			ret = check_variable(&var_die, type_die, offset,
					     /*is_pointer=*/false);
			if (ret == 0)
				pr_debug("found PC-rel by addr=%lx offset=%d\n", dloc->var_addr, offset);
			dloc->type_offset = offset;
			goto out;
		}

		if (dloc->var_name &&
		    die_find_variable_at(&cu_die, dloc->var_name, pc, &var_die)) {
			ret = check_variable(&var_die, type_die, dloc->type_offset,
					     /*is_pointer=*/false);
			if (ret == 0)
				pr_debug("found \"%s\" by name offset=%d\n", dloc->var_name, dloc->type_offset);
			/* dloc->type_offset was updated by the caller */
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
		}
	}

retry:
	is_fbreg = (reg == fbreg);
	if (is_fbreg)
		offset = loc->offset - fb_offset;

	/* Search from the inner-most scope to the outer */
	for (i = nr_scopes - 1; i >= 0; i--) {
		if (reg == DWARF_REG_PC) {
			if (!die_find_variable_by_addr(&scopes[i], pc, dloc->var_addr,
						       &var_die, &offset))
				continue;
		} else {
			/* Look up variables/parameters in this scope */
			if (!die_find_variable_by_reg(&scopes[i], pc, reg,
						      &offset, is_fbreg, &var_die))
				continue;
		}

		/* Found a variable, see if it's correct */
		ret = check_variable(&var_die, type_die, offset,
				     reg != DWARF_REG_PC && !is_fbreg);
		if (ret == 0) {
#if 0
			const char *filename;
			int lineno;

			if (cu_find_lineinfo(&cu_die, pc, &filename, &lineno) < 0) {
				filename = "unknown";
				lineno = 0;
			}
#endif
			pr_debug("found \"%s\" in scope=%d/%d reg=%d offset=%#x (%d) loc->offset=%d fb-offset=%d (die:%lx scope:%lx) type=",
				 dwarf_diename(&var_die), i+1, nr_scopes, reg, offset, offset, loc->offset, fb_offset, dwarf_dieoffset(&var_die),
				 dwarf_dieoffset(&scopes[i])/*, filename, lineno*/);
			debug_print_type_name(type_die);
		}
		dloc->type_offset = offset;
		goto out;
	}

	if (reg != DWARF_REG_PC) {
		ret = find_data_type_block(dloc, reg, &cu_die, scopes,
					   nr_scopes, type_die);
		if (ret == 0)
			goto out;
	}

	if (loc->multi_regs && reg == loc->reg1 && loc->reg1 != loc->reg2) {
		reg = loc->reg2;
		goto retry;
	}

	if (ret < 0) {
		pr_debug("no variable found\n");
		ann_data_stat.no_var++;
	}

out:
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
	struct annotated_data_type *result = NULL;
	struct dso *dso = dloc->ms->map->dso;
	Dwarf_Die type_die;

	dloc->di = debuginfo__new(dso->long_name);
	if (dloc->di == NULL) {
		pr_debug("cannot get the debug info\n");
		return NULL;
	}

	/*
	 * The type offset is the same as instruction offset by default.
	 * But when finding a global variable, the offset won't be valid.
	 */
	if (dloc->var_name == NULL)
		dloc->type_offset = dloc->op->offset;

	dloc->fbreg = -1;

	if (find_data_type_die(dloc, &type_die) < 0)
		goto out;

	result = dso__findnew_data_type(dso, &type_die);

out:
	debuginfo__delete(dloc->di);
	return result;
}

static int alloc_data_type_histograms(struct annotated_data_type *adt, int nr_entries)
{
	int i;
	size_t sz = sizeof(struct type_hist);

	sz += sizeof(struct type_hist_entry) * adt->self.size;

	/* Allocate a table of pointers for each event */
	adt->nr_histograms = nr_entries;
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
	return 0;

err:
	while (--i >= 0)
		free(adt->histograms[i]);
	free(adt->histograms);
	return -ENOMEM;
}

static void delete_data_type_histograms(struct annotated_data_type *adt)
{
	for (int i = 0; i < adt->nr_histograms; i++)
		free(adt->histograms[i]);
	free(adt->histograms);
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
		free(pos->self.type_name);
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
 *
 * This function updates type histogram at @ofs for @evsel.  Samples are
 * aggregated before calling this function so it can be called with more
 * than one samples at a certain offset.
 */
int annotated_data_type__update_samples(struct annotated_data_type *adt,
					struct evsel *evsel, int offset,
					int nr_samples, u64 period)
{
	struct type_hist *h;

	if (adt == NULL)
		return 0;

	if (adt->histograms == NULL) {
		int nr = evsel->evlist->core.nr_entries;

		if (alloc_data_type_histograms(adt, nr) < 0)
			return -1;
	}

	if (offset < 0 || offset >= adt->self.size)
		return -1;

	h = adt->histograms[evsel->core.idx];

	h->nr_samples += nr_samples;
	h->addr[offset].nr_samples += nr_samples;
	h->period += period;
	h->addr[offset].period += period;
	return 0;
}
