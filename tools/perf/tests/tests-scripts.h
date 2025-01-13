/* SPDX-License-Identifier: GPL-2.0 */
#ifndef TESTS_SCRIPTS_H
#define TESTS_SCRIPTS_H

#include "tests.h"

#define SHELL_SETUP "setup.sh"

enum shell_setup {
	NO_SETUP     = 0,
	RUN_SETUP    = 1,
	FAILED_SETUP = 2,
	PASSED_SETUP = 3,
};

struct shell_info {
	const char *base_path;
	enum shell_setup has_setup;
};

struct test_suite **create_script_test_suites(void);

#endif /* TESTS_SCRIPTS_H */
