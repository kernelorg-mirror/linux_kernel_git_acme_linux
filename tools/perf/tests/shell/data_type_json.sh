#!/bin/bash
# perf data-type JSON export tests
# SPDX-License-Identifier: GPL-2.0

# Records a data-type profile and exports it as JSON via both
# 'perf report --data-type-json' and 'perf annotate --data-type-json', then
# validates that the output is well-formed JSON (python3 -m json.tool
# rejects truncated or unclosed output).

set -e

# Skip checks first: these may exit 2, and must run before any temp file
# is created so a skip does not leak files in /tmp.
if ! perf check feature -q dwarf
then
	echo "Skip: no DWARF (libdw) support"
	exit 2
fi

if ! command -v python3 >/dev/null
then
	echo "Skip: python3 not available"
	exit 2
fi

# The export needs memory events.
if perf mem record -o /dev/null -- true 2>&1 | grep -q "failed: no PMU supports the memory events"
then
	echo "Skip: no PMU supports memory events"
	exit 2
fi

# Skip if per-thread mem record is not supported on this PMU
# (e.g. AMD IBS needs system-wide '-a').
if ! perf mem record -o /dev/null perf test -w datasym 2>/dev/null
then
	echo "Skip: cannot record memory events on this PMU"
	exit 2
fi

perfdata=$(mktemp /tmp/__perf_test.perf.data.XXXXX)
report_json=$(mktemp /tmp/__perf_test.perf.report.json.XXXXX)
annotation_json=$(mktemp /tmp/__perf_test.perf.annotate.json.XXXXX)
validate_json=$(mktemp /tmp/__perf_test.perf.validate.json.XXXXX)

cleanup() {
	rm -f "${perfdata}" "${perfdata}".old "${report_json}" "${annotation_json}" "${validate_json}"

	trap - EXIT TERM INT
}

trap_cleanup() {
	echo "Unexpected signal in ${FUNCNAME[1]}"
	cleanup
	exit 1
}
trap trap_cleanup EXIT TERM INT

test_json_export() {
	# code_with_type / datasym are the standard data-type workloads
	if ! perf mem record -o "${perfdata}" perf test -w datasym 2> /dev/null
	then
		echo "JSON export [Failed: perf mem record]"
		err=1
		return
	fi

	# perf report --data-type-json -s type
	if ! perf report -i "${perfdata}" -s type --data-type-json="${report_json}" 2> /dev/null
	then
		echo "JSON export [Failed: perf report --data-type-json]"
		err=1
		return
	fi

	if ! python3 -m json.tool "${report_json}" > "${validate_json}"
	then
		echo "JSON export [Failed: report output is not valid JSON]"
		cat "${report_json}"
		err=1
		return
	fi

	if ! grep -q '"nr_samples_store"' "${report_json}"
	then
		echo "JSON export [Failed: missing per-direction histogram counters]"
		err=1
		return
	fi

	# perf annotate --data-type-json --data-type
	if ! perf annotate -i "${perfdata}" --data-type --data-type-json="${annotation_json}" 2> /dev/null
	then
		echo "JSON export [Failed: perf annotate --data-type-json]"
		err=1
		return
	fi

	if ! python3 -m json.tool "${annotation_json}" > /dev/null
	then
		echo "JSON export [Failed: annotate output is not valid JSON]"
		err=1
		return
	fi

	echo "JSON export test [Success]"
}

err=0
test_json_export

cleanup
exit $err
