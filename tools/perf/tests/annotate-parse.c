// SPDX-License-Identifier: GPL-2.0
/*
 * Tests for the instruction operand parser behind 'perf annotate'.
 *
 * Which operand ends up in the source slot and which one in the target
 * slot is what the data type profiling uses to tell a load from a store:
 * the memory reference of an instruction that only reads it has to land in
 * the source slot.  On x86 the parser works from the AT&T text, so the
 * operands have to be told apart before that decision can be made.
 */
#include "tests.h"
#include "util/debug.h"
#include "util/disasm.h"

#include <linux/compiler.h>
#include <linux/kernel.h>
#include <linux/zalloc.h>
#include <stdlib.h>
#include <string.h>

/*
 * Just enough of an x86 arch for the parser: the objdump syntax chars.
 *
 * Deliberately minimal, and deliberately not the real x86 arch object, so
 * that the tests stay about the operand text alone.  The price is that if
 * mov__parse() ever grows a dependency on some other struct arch field the
 * tests keep passing on this zero/NULL field while the real path changes
 * behaviour, so adding such a dependency means extending this too.
 */
static struct arch arch_x86 = {
	.name = "x86",
	.insn_suffix = "bwlq",
	.objdump = {
		.comment_char	= '#',
		.register_char	= '%',
		.memory_ref_char = '(',
		.imm_char	= '$',
	},
};

struct operand_case {
	const char *raw;
	const char *source;
	const char *target;
	bool source_multi_regs;
	bool target_multi_regs;
	const char *printed;
};

/*
 * mov__scnprintf() renders as "mov  " then source and target joined by a
 * comma, so the expected rendering is built from the operands themselves:
 * what is printed must not depend on where the operand list was split.
 */
#define OPS(_raw, _source, _target, _src_multi, _tgt_multi)		\
	{ .raw = _raw, .source = _source, .target = _target,		\
	  .source_multi_regs = _src_multi,				\
	  .target_multi_regs = _tgt_multi,				\
	  .printed = "mov  " _source "," _target }

static const struct operand_case mov_ops_cases[] = {
	/* Two operands: split on the only separator. */
	OPS("%rax,%rbx",		"%rax",		"%rbx",			false, false),
	OPS("0x8(%rdx),%rax",		"0x8(%rdx)",	"%rax",			false, false),
	OPS("%rax,0x8(%rdx)",		"%rax",		"0x8(%rdx)",		false, false),
	/*
	 * SIB addressing: the separators inside the memory reference are
	 * not operand separators.
	 */
	OPS("0x8(%rax,%rcx,4),%rdx",	"0x8(%rax,%rcx,4)",	"%rdx",		true,  false),
	OPS("%rdx,0x8(%rax,%rcx,4)",	"%rdx",		"0x8(%rax,%rcx,4)",	false, true),
	/*
	 * Three operands: AT&T lists the sources before the destination, so
	 * the memory reference is a source even though it is not the first
	 * operand, and it stays in the source slot together with the other
	 * sources, so that printing the instruction does not lose one.
	 */
	OPS("$0x3e8,0x8(%rdx),%rax",		"$0x3e8,0x8(%rdx)",	"%rax",	false, false),
	OPS("$0x3e8,0x8(%rdx,%rcx,4),%rax",	"$0x3e8,0x8(%rdx,%rcx,4)", "%rax", true, false),
	/*
	 * Two registers in the source slot, but no memory reference:
	 * multi_regs is about the second register *of a memory reference*,
	 * so it must stay false even though the re-split left a comma here.
	 */
	OPS("$0x3e8,%rdx,%rax",		"$0x3e8,%rdx",	"%rax",			false, false),
	OPS("%ymm1,%ymm2,%ymm3",	"%ymm1,%ymm2",	"%ymm3",		false, false),
	/*
	 * The reverse direction: here the memory operand really is the
	 * destination, so it has to stay in the target slot and the access
	 * has to stay a store.
	 */
	OPS("$0x4,%rax,0x8(%rbx)",	"$0x4,%rax",	"0x8(%rbx)",		false, false),
	/*
	 * The disassemblers disagree on the spacing after the commas: GNU
	 * objdump emits none, llvm-objdump emits one.  Both spellings have to
	 * parse the same, and the space after the separator is dropped, in
	 * the two operand form as well, so that the rendering above is the
	 * same for both.
	 */
	OPS("$0x3e8, 0x8(%rdx), %rax",	"$0x3e8,0x8(%rdx)",	"%rax",		false, false),
	OPS("0x8(%rdx), %rax",		"0x8(%rdx)",		"%rax",		false, false),
};

static int test__mov_ops_parse(struct test_suite *t __maybe_unused, int subtest __maybe_unused)
{
	for (size_t i = 0; i < ARRAY_SIZE(mov_ops_cases); i++) {
		const struct operand_case *c = &mov_ops_cases[i];
		struct ins_operands ops = { .raw = strdup(c->raw) };
		int err;

		TEST_ASSERT_VAL("out of memory", ops.raw != NULL);

		err = mov_ops.parse(&arch_x86, &ops, NULL, NULL);

		if (err == 0 && (!ops.source.raw || !ops.target.raw)) {
			pr_debug("FAILED %s: unparsed operand\n", c->raw);
			err = -1;
		}

		if (err == 0 && strcmp(ops.source.raw, c->source)) {
			pr_debug("FAILED %s: source \"%s\" != \"%s\"\n",
				 c->raw, ops.source.raw, c->source);
			err = -1;
		}

		if (err == 0 && strcmp(ops.target.raw, c->target)) {
			pr_debug("FAILED %s: target \"%s\" != \"%s\"\n",
				 c->raw, ops.target.raw, c->target);
			err = -1;
		}

		if (err == 0 && ops.source.multi_regs != c->source_multi_regs) {
			pr_debug("FAILED %s: source multi_regs %d != %d\n",
				 c->raw, ops.source.multi_regs, c->source_multi_regs);
			err = -1;
		}

		if (err == 0 && ops.target.multi_regs != c->target_multi_regs) {
			pr_debug("FAILED %s: target multi_regs %d != %d\n",
				 c->raw, ops.target.multi_regs, c->target_multi_regs);
			err = -1;
		}

		/*
		 * What gets printed is source and target joined by a comma,
		 * so it has to come out the same no matter where the operand
		 * list was split.  Check it, since the split point is exactly
		 * what this change moves.
		 */
		if (err == 0) {
			char bf[256];
			struct ins ins = { .name = "mov" };

			mov__scnprintf(&ins, bf, sizeof(bf), &ops, 4);

			if (strcmp(bf, c->printed)) {
				pr_debug("FAILED %s: printed \"%s\" != \"%s\"\n",
					 c->raw, bf, c->printed);
				err = -1;
			}
		}

		zfree(&ops.source.raw);
		zfree(&ops.source.name);
		zfree(&ops.target.raw);
		zfree(&ops.target.name);
		free(ops.raw);

		TEST_ASSERT_VAL("wrong operand split", err == 0);
	}

	return 0;
}

/*
 * Where the operand lands decides the load/store direction, but whether the
 * target is written at all is decided here: a memory operand that is only
 * read is a load whichever slot it is in.  It is prefix logic, "bt" reads
 * and "bts" writes, so the failure mode is a silent misclassification
 * rather than a parse error, and no amount of reading the code makes the
 * whole table obvious.
 *
 * The function is x86 specific but the decision is pure string matching on
 * the instruction name, so this runs everywhere the symbol is linked in,
 * which is always, see util/annotate-arch/Build.
 */
struct read_only_case {
	const char *name;
	bool read_only;
};

static const struct read_only_case read_only_cases[] = {
	/* cmp: reads both operands, cmpxchg: writes its target. */
	{ .name = "cmp",	.read_only = true  },
	{ .name = "cmpq",	.read_only = true  },
	{ .name = "cmpxchg",	.read_only = false },
	{ .name = "cmpxchg16b",	.read_only = false },
	/*
	 * bt with no suffix or with a size suffix only tests the bit, while
	 * bts/btr/btc set, reset or complement it, so they write.
	 */
	{ .name = "bt",		.read_only = true  },
	{ .name = "btq",	.read_only = true  },
	{ .name = "bts",	.read_only = false },
	{ .name = "btr",	.read_only = false },
	{ .name = "btc",	.read_only = false },
	/* test: reads both operands. */
	{ .name = "test",	.read_only = true  },
	{ .name = "testb",	.read_only = true  },
	/* Everything else writes its target. */
	{ .name = "cmovne",	.read_only = false },
	{ .name = "mov",	.read_only = false },
	{ .name = "xchg",	.read_only = false },
};

static int test__x86_ins_target_is_read_only(struct test_suite *t __maybe_unused,
					    int subtest __maybe_unused)
{
	for (size_t i = 0; i < ARRAY_SIZE(read_only_cases); i++) {
		const struct read_only_case *c = &read_only_cases[i];
		struct ins ins = { .name = c->name };
		bool read_only = x86__ins_target_is_read_only(&ins);

		if (read_only != c->read_only)
			pr_debug("FAILED %s: read_only %d != %d\n",
				 c->name, read_only, c->read_only);

		TEST_ASSERT_VAL("wrong read-only classification",
				read_only == c->read_only);
	}

	return 0;
}

static struct test_case tests__annotate_parse[] = {
	TEST_CASE("x86 mov_ops operand parsing", mov_ops_parse),
	TEST_CASE("x86 ins target is read only", x86_ins_target_is_read_only),
	{ .name = NULL, }
};

struct test_suite suite__annotate_parse = {
	.desc = "annotate instruction operand parsing",
	.test_cases = tests__annotate_parse,
};
