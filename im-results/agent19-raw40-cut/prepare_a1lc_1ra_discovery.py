#!/usr/bin/env python3
"""Reconstruct the missing Raw40 A1LC B1=1RA five-hole child frontier.

The enumerator and FAR/compact recognizers are discovery tools.  Their output is
then consumed by prepare_a1lc_0lc.py and checked by the generated Lean kernel
proof.  A residual is never silently treated as closed: every open id must be
covered by a FAR code or a reconstructed finite two-sided DFA.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent
OUT = ROOT / "a1lc" / "1RA"
PARENT = "1RB1LC_1RC1RA_0RD---_1LD1LA_------_------"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(ROOT))
from compact_ngram import compact, compact_run, compact_lag, find_lag  # noqa: E402


def run(args, **kwargs):
    return subprocess.run(args, check=True, text=True, **kwargs)


for name in ("enumerate_canon", "farbank"):
    run(["g++", "-std=c++20", "-O3", str(ROOT / f"{name}.cpp"),
         "-o", str(OUT / name)])

enum = run([str(OUT / "enumerate_canon"), PARENT], cwd=OUT,
           capture_output=True)
(OUT / "enum.log").write_text(enum.stdout)
opens = (OUT / "open.txt").read_text().splitlines()
if len(opens) != 188 or len(set(opens)) != len(opens):
    raise SystemExit(f"unexpected canonical open frontier: {len(opens)}")

m = re.search(r"maxscore=(\d+) n=(\d+) delay=(\d+) table=(\S+)", enum.stdout)
if not m:
    raise SystemExit("enumerator did not report its maximum halting leaf")
bound, witness_n, witness_delay = map(int, m.group(1, 2, 3))
witness_table = m.group(4)
if witness_delay != 0 or witness_table.count("HHH") != 1:
    raise SystemExit("unexpected weighted witness shape; inspect enum.log")
witness_slot = witness_table.replace("_", "").index("HHH") // 3
if bound != witness_n + 1 + witness_delay:
    raise SystemExit("enumerator witness score is inconsistent")

def far_valid(code: str, table: str) -> bool:
    """Independent Python replay of certify_shards.py's FAR closure check."""
    rev = int(code[0])
    D = [int(ch) for ch in code[1:]]
    n = len(D) // 2
    if n < 1 or len(D) != 2 * n:
        return False
    N = 6 * n + 1
    H = N - 1
    halt = 1 << H
    T = [0] * (2 * N)
    T[H] = T[N + H] = halt
    flat = table.replace("_", "")
    if len(flat) != 36:
        return False
    transitions = [flat[3 * i:3 * i + 3] for i in range(12)]
    rules = []
    for l in range(n):
        for q in range(6):
            for a in range(2):
                m = transitions[2 * q + a]
                dst = a * N + 6 * l + q
                if m == "---":
                    T[dst] = halt
                    continue
                w = int(m[0])
                r = m[1] == "R"
                k = ord(m[2]) - 65
                if r != bool(rev):
                    T[dst] = 1 << (6 * D[2 * l + w] + k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if D[2 * j + b] == l:
                                rules.append((dst, b * N + 6 * j + k, w * N))
    while True:
        z = halt
        while True:
            old = z
            for j in range(N):
                if T[j] & z:
                    z |= 1 << j
            if z & 1:
                return False
            if old == z:
                break
        changed = False
        for dst, src, off in rules:
            v = T[dst]
            bits = T[src]
            while bits:
                k = (bits & -bits).bit_length() - 1
                v |= T[off + k]
                bits &= bits - 1
            if v != T[dst]:
                T[dst] = v
                changed = True
        if not changed:
            return True


def filter_invalid_far(codes):
    invalid = {}
    for i, code in list(codes.items()):
        if not far_valid(code, opens[i]):
            invalid[i] = code
            del codes[i]
    return invalid


# Reuse every already-checked A1LC FAR code as a seed, then exhaust the
# restricted-growth FAR search through five summary states.
seed_codes = set()
for path in ROOT.glob("a1lc-*.json"):
    data = json.loads(path.read_text())
    for row in data.get("far", []):
        seed_codes.add(row["code"])
    for line in data.get("farGroups", "").splitlines():
        fields = line.split()
        if fields:
            seed_codes.add(fields[0])
(OUT / "far-bank.txt").write_text("".join(code + "\n" for code in sorted(seed_codes)))
far_input = "".join(f"{i} {table.replace('_', '')}\n" for i, table in enumerate(opens))
far = run([str(OUT / "farbank"), "5", str(OUT / "far-bank.txt")],
          cwd=OUT, input=far_input, capture_output=True)
(OUT / "far5.txt").write_text(far.stdout)
(OUT / "far5.log").write_text(far.stderr)
far_codes = {}
for line in far.stdout.splitlines():
    fields = line.split()
    if len(fields) == 2:
        far_codes[int(fields[0])] = fields[1]
if any(i < 0 or i >= len(opens) for i in far_codes):
    raise SystemExit("FAR search returned out-of-range ids")
invalid_far = filter_invalid_far(far_codes)
far5_valid_count = len(far_codes)

# One residual can require a six-state FAR summary even when the other 187
# close at five.  Search only the remaining ids so the larger bank stays cheap.
remaining_for_far6 = sorted(set(range(len(opens))) - set(far_codes))
far6_stats = []
if remaining_for_far6:
    far6_input = "".join(
        f"{i} {opens[i].replace('_', '')}\\n" for i in remaining_for_far6
    )
    far6 = run([str(OUT / "farbank"), "6", str(OUT / "far-bank.txt")],
               cwd=OUT, input=far6_input, capture_output=True)
    (OUT / "far6.txt").write_text(far6.stdout)
    (OUT / "far6.log").write_text(far6.stderr)
    far6_ids = []
    for line in far6.stdout.splitlines():
        fields = line.split()
        if len(fields) == 2:
            i = int(fields[0])
            far_codes[i] = fields[1]
            far6_ids.append(i)
    invalid_far.update(filter_invalid_far(far_codes))
    far6_stats = [line for line in far6.stderr.splitlines() if line.startswith("n=")]
else:
    far6_ids = []
    far6_stats = []

# Remaining residuals need stronger finite summaries.  Try the already-
# established A1LC n-gram, run-length and lag-XOR families.  Each accepted
# record is independently reconstructed by emit_rungram.py and checked by
# FastBiDFA in Lean.
ngram_widths = {(5, 5), (6, 6), (7, 7), (8, 8), (5, 6), (6, 5), (4, 5), (5, 4)}
run_pairs = {
    ((2, 1, 1, 2, 2), (2, 1, 1, 2, 2)),
    ((2, 2, 2, 4, 4), (2, 2, 2, 4, 4)),
    ((3, 2, 2, 4, 4), (3, 2, 2, 4, 4)),
    ((2, 1, 1, 1, 5), (2, 1, 1, 1, 5)),
    ((2, 1, 2, 2, 2), (2, 1, 2, 2, 2)),
}
lag_pairs = {
    ((0, 2, 1, 1, 2, 5), (0, 2, 1, 1, 2, 5)),
    ((0, 2, 1, 2, 3, 3), (0, 2, 1, 2, 3, 3)),
    ((3, 2, 2, 1, 4, 4), (3, 2, 2, 1, 4, 4)),
    ((0, 2, 1, 2, 2, 5), (0, 2, 1, 2, 2, 5)),
    ((0, 2, 1, 1, 1, 6), (0, 2, 1, 1, 1, 6)),
}
# Mine the proven A1LC banks for additional compact recognizers rather than
# guessing a new parameter family for this child.
for path in ROOT.glob("a1lc-*.json"):
    data = json.loads(path.read_text())
    for row in data.get("compact", []):
        method = row.get("method", [])
        if method and method[0] == "ngram":
            ngram_widths.add((int(method[1]), int(method[2])))
        elif method and method[0] == "rungram":
            run_pairs.add((tuple(method[1]), tuple(method[2])))
        elif method and method[0] == "compact-lag":
            lag_pairs.add((tuple(method[1]), tuple(method[2])))
    for group, _ranges in data.get("compactGroups", []):
        kind, left, right = group
        if kind == "ngram":
            ngram_widths.add((int(left), int(right)))
        elif kind == "rungram":
            run_pairs.add((tuple(left), tuple(right)))
        elif kind == "compact-lag":
            lag_pairs.add((tuple(left), tuple(right)))

compact_records = []
unresolved = []
methods = {}
for i in sorted(set(range(len(opens))) - set(far_codes)):
    table = opens[i]
    record = None
    for widths in sorted(ngram_widths, key=lambda x: (sum(x), x)):
        try:
            record = compact(table, widths, cap=100_000)
            methods[i] = ["ngram", *widths]
            break
        except ValueError:
            pass
    if record is None:
        for left, right in sorted(run_pairs, key=lambda x: (sum(x[0]) + sum(x[1]), x)):
            try:
                record = compact_run(table, list(left), list(right), cap=100_000)
                methods[i] = ["rungram", list(left), list(right)]
                break
            except ValueError:
                pass
    if record is None:
        for left, right in sorted(lag_pairs, key=lambda x: (sum(x[0]) + sum(x[1]), x)):
            try:
                record = compact_lag(table, list(left), list(right), cap=100_000)
                methods[i] = ["compact-lag", list(left), list(right)]
                break
            except ValueError:
                pass
    if record is None:
        for seed in ((0, 2, 2, 5), (0, 2, 3, 3), (3, 2, 4, 4)):
            try:
                record = find_lag(table, seed, seed, cap=100_000)
                methods[i] = ["find-lag", list(seed), list(seed)]
                break
            except ValueError:
                pass
    if record is None:
        unresolved.append({"id": i, "table": table})
    else:
        compact_records.append({"id": i, **record})

# Preserve the exact discovery state even when a residual still needs work.
enum_stats = {}
for key, value in re.findall(r"(cycle|last|open|split):(\d+)", enum.stdout):
    enum_stats[key] = int(value)
far_stats = [line for line in far.stderr.splitlines() if line.startswith("n=")] + far6_stats
summary = {
    "parent": PARENT,
    "opens": len(opens),
    "initialBound": bound,
    "bound": bound,
    "witness": {
        "n": witness_n, "slot": witness_slot, "delay": witness_delay,
        "delayPath": [], "table": witness_table,
    },
    "far": [
        {"id": i, "table": opens[i], "code": code}
        for i, code in sorted(far_codes.items())
    ],
    "compact": compact_records,
    "unresolved": unresolved,
    "late": [],
    "open_sha256": hashlib.sha256((OUT / "open.txt").read_bytes()).hexdigest(),
    "tree_sha256": hashlib.sha256((OUT / "tree.json").read_bytes()).hexdigest(),
    "enum_stats": enum_stats,
    "far_stats": far_stats,
    "invalid_far": [{"id": i, "code": code} for i, code in sorted(invalid_far.items())],
    "compact_methods": methods,
}
(OUT / "discovery-draft.json").write_text(json.dumps(summary, indent=2) + "\n")
if unresolved:
    (ROOT / "a1lc-1RA-unresolved.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("A1LC_1RA_UNRESOLVED", json.dumps(unresolved, separators=(",", ":")))
    print("FAR", len(far_codes), "/", len(opens), "COMPACT", len(compact_records))
    print("FAR_DIAG", "far5_valid", far5_valid_count, "far6_output_ids", far6_ids,
          "invalid", sorted(invalid_far.items()))
    print("FAR_STATS", far_stats)
    raise SystemExit(2)

# The committed discovery file is the deterministic input to the Lean source
# generator.  Include each open table so its id/code association is auditable.
( ROOT / "a1lc-1RA-discovery.json" ).write_text(json.dumps(summary, indent=2) + "\n")
print("A1LC_1RA_DISCOVERY_JSON_BEGIN")
print(json.dumps(summary, separators=(",", ":")))
print("A1LC_1RA_DISCOVERY_JSON_END")
print("FAR_DIAG", "far5_valid", far5_valid_count, "far6_output_ids", far6_ids,
      "invalid", sorted(invalid_far.items()))
print("A1LC_1RA_CLOSED", "FAR", len(far_codes), "COMPACT", len(compact_records),
      "BOUND", bound, "WITNESS", witness_table)
print("FAR_STATS", far_stats)
