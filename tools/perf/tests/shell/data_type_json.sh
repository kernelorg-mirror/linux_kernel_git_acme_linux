#!/bin/bash
# perf data-type JSON export tests
# SPDX-License-Identifier: GPL-2.0

# Records a data-type profile and exports it as JSON via both
# 'perf report --data-type-json' and 'perf annotate --data-type-json', then
# validates the output: well-formed JSON (python3 -m json.tool rejects
# truncated or unclosed output) in the documented schema - a "version"
# entry, a "machine" entry with the machine the profile was captured on
# plus one entry per DSO, with the types that had hits in it.

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
json=$(mktemp /tmp/__perf_test.perf.data_type.json.XXXXX)
buildid_list=$(mktemp /tmp/__perf_test.perf.buildid.list.XXXXX)
ctfdir=$(mktemp -d /tmp/__perf_test.ctf.XXXXXX)
ctferr=$(mktemp /tmp/__perf_test.ctf.err.XXXXX)
typestat=$(mktemp /tmp/__perf_test.type.stat.XXXXX)

cleanup() {
	rm -rf "${perfdata}" "${perfdata}".old "${json}" "${buildid_list}" \
		"${ctfdir}" "${ctferr}" "${typestat}"

	trap - EXIT TERM INT
}

trap_cleanup() {
	echo "Unexpected signal in ${FUNCNAME[1]}"
	cleanup
	exit 1
}
trap trap_cleanup EXIT TERM INT

# Check one exported profile against the documented schema, with the build
# IDs cross-checked against what 'perf buildid-list' reports for the same
# perf.data file.
validate_data_type_json() {
	local label=$1

	if ! python3 - "${json}" "${buildid_list}" <<'PYEOF'
import json, re, sys

profile = json.load(open(sys.argv[1]))

if profile.get("version") != 1:
    sys.exit("unexpected schema version: %s" % profile.get("version"))
if "machine" not in profile or "dsos" not in profile:
    sys.exit("no machine/dsos entries at the top level")

machine = profile["machine"]
for key in ("hostname", "arch", "cacheline_size", "cmdline"):
    if key not in machine:
        sys.exit("machine entry has no %s" % key)
if not isinstance(machine["cacheline_size"], int) or machine["cacheline_size"] < 1:
    sys.exit("bogus machine cacheline_size")
if not isinstance(machine["cmdline"], list):
    sys.exit("machine cmdline is not an array")

# The build IDs of the DSOs with samples in this perf.data file, to check
# the identity the profile carries against what perf reports for the
# session.  Not every profiled DSO is there: a synthesized vdso, for one,
# is not in the header's build ID table.
session_build_ids = set()
for line in open(sys.argv[2]):
    fields = line.split()
    if fields and re.fullmatch(r"[0-9a-f]{2,64}", fields[0]):
        session_build_ids.add(fields[0])

nr_types = 0
nr_verified_dsos = 0
for dso in profile["dsos"]:
    for key in ("dso", "build_id", "types"):
        if key not in dso:
            sys.exit("dso entry has no %s" % key)
    if dso["build_id"] is not None:
        if not re.fullmatch(r"[0-9a-f]{2,64}", dso["build_id"]):
            sys.exit("bogus build ID: %s" % dso["build_id"])
        if dso["build_id"] in session_build_ids:
            nr_verified_dsos += 1
    for dt in dso["types"]:
        for key in ("type", "size", "members", "histograms"):
            if key not in dt:
                sys.exit("type entry has no %s" % key)
        if not dt["histograms"]:
            sys.exit("type %s has no histogram" % dt["type"])
        for histogram in dt["histograms"]:
            if not histogram["samples"]:
                sys.exit("histogram without samples")
            for sample in histogram["samples"]:
                # Loads and stores are counted in separate counters.
                for key in ("offset", "nr_samples_load", "nr_samples_store",
                            "period_load", "period_store"):
                    if key not in sample:
                        sys.exit("sample has no %s" % key)
        nr_types += 1

if not nr_types:
    sys.exit("no type with hits in the profile")
if not any(dso["build_id"] for dso in profile["dsos"]):
    sys.exit("no DSO carries a build ID")
if not nr_verified_dsos:
    sys.exit("no DSO build ID matches perf buildid-list")
PYEOF
	then
		echo "JSON export [Failed: ${label} output is not in the documented schema]"
		err=1
		return
	fi

	echo "JSON export [Success: ${label}]"
}

test_json_export() {
	# code_with_type / datasym are the standard data-type workloads
	if ! perf mem record -o "${perfdata}" perf test -w datasym 2> /dev/null
	then
		echo "JSON export [Failed: perf mem record]"
		err=1
		return
	fi

	if ! perf buildid-list -i "${perfdata}" > "${buildid_list}" 2> /dev/null
	then
		echo "JSON export [Failed: perf buildid-list]"
		err=1
		return
	fi

	if ! perf report -i "${perfdata}" -s type --data-type-json="${json}" 2> /dev/null
	then
		echo "JSON export [Failed: perf report --data-type-json]"
		err=1
		return
	fi

	if ! python3 -m json.tool "${json}" > /dev/null
	then
		echo "JSON export [Failed: report output is not valid JSON]"
		cat "${json}"
		err=1
		return
	fi

	validate_data_type_json "perf report"

	if ! perf annotate -i "${perfdata}" --data-type --data-type-json="${json}" 2> /dev/null
	then
		echo "JSON export [Failed: perf annotate --data-type-json]"
		err=1
		return
	fi

	if ! python3 -m json.tool "${json}" > /dev/null
	then
		echo "JSON export [Failed: annotate output is not valid JSON]"
		cat "${json}"
		err=1
		return
	fi

	validate_data_type_json "perf annotate"
}

# The aggregate JSON producer and the per-sample CTF one must agree on
# what they resolved and what they dropped: it was exactly this
# cross-check, run by hand on a capture, that found the samples recorded
# with a bogus PEBS IP (the two deliverables disagreed on their access
# direction) and led to the data address test.  Keep it running now that
# both agree, so that any future divergence in what one of them counts
# shows up here.
test_ctf_crosscheck() {
	local resolved skipped report_bad_addr report_samples

	# The CTF writer is an optional build dependency.
	if ! perf data convert --to-ctf="${ctfdir}" --force -i "${perfdata}" >/dev/null 2>"${ctferr}"
	then
		if grep -q "babeltrace2 ctf support is not compiled in" "${ctferr}"
		then
			echo "Skip: no CTF writer (libbabeltrace2) support"
		else
			echo "CTF cross-check [Failed: perf data convert]"
			cat "${ctferr}"
			err=1
		fi
		return
	fi

	# Same capture, same test: what the folded --sort type path drops
	# and accounts against what the converter resolves per sample.
	if ! perf report -i "${perfdata}" -s type --data-type-json="${json}" --type-stat --stdio > "${typestat}" 2>/dev/null
	then
		echo "CTF cross-check [Failed: perf report --type-stat]"
		err=1
		return
	fi

	report_bad_addr=$(awk '/: bad_addr$/ {print $1}' "${typestat}")
	report_bad_addr=${report_bad_addr:-0}

	if ! report_samples=$(python3 -c '
import json, sys
profile = json.load(open(sys.argv[1]))
print(sum(histogram["total_samples"]
          for dso in profile["dsos"] for data_type in dso["types"]
          for histogram in data_type["histograms"]))
' "${json}")
	then
		echo "CTF cross-check [Failed: reading the exported JSON]"
		err=1
		return
	fi

	resolved=$(sed -n 's/.*Resolved the data type of \([0-9]*\) samples.*/\1/p' "${ctferr}")
	resolved=${resolved:-0}

	skipped=$(sed -n 's/.*Skipped \([0-9]*\) samples.*/\1/p' "${ctferr}")
	skipped=${skipped:-0}

	if [ "${report_bad_addr}" != "${skipped}" ]
	then
		echo "CTF cross-check [Failed: 'perf report' dropped ${report_bad_addr} samples, the converter skipped ${skipped}]"
		err=1
	elif [ "${report_samples}" != "${resolved}" ]
	then
		echo "CTF cross-check [Failed: the JSON accounted ${report_samples} samples, the converter resolved ${resolved}]"
		err=1
	else
		echo "CTF cross-check [Success: both producers dropped ${skipped} and resolved ${resolved} samples]"
	fi
}

err=0
test_json_export
test_ctf_crosscheck

cleanup
exit $err
