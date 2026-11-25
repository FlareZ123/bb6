"""Targeted FAR search for the five unresolved raw124/F1=0LF/F0=1RB leaves.

The search output is discovery evidence only. A hit is not a proof until its
FAR data are emitted, kernel-checked, and connected to the original Machine.
"""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
TABLES = [
    "1RB0LE_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF",
    "1RB---_1RC1RF_0RD0RB_1LD1RE_0RA1LF_1RB0LF",
    "1RB---_1RC1RF_0RD0RB_1LD1RE_1RA1LF_1RB0LF",
    "1RB---_1RC1RA_0RD0RE_1LD1RE_0RB1LF_1RB0LF",
    "1RB0RD_1RC---_0RD1LA_1LD1RE_1RB1LF_1RB0LF",
]
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 9
if not 1 <= LIMIT <= 10:
    raise SystemExit("DFA limit must be in 1..10")

rows = []
for i, table in enumerate(TABLES):
    compact = table.replace("_", "")
    if len(compact) != 36:
        raise AssertionError((i, len(compact), table))
    rows.append(f"{i} {compact}")
payload = "\n".join(rows) + "\n"
(ROOT / "0lf-hard-search-input.txt").write_text(payload)

binary = ROOT / "cefar"
subprocess.run(
    ["g++", "-std=c++20", "-O3", str(ROOT / "cefar.cpp"), "-o", str(binary)],
    check=True,
)

timed_out = False
try:
    proc = subprocess.run(
        [str(binary), str(LIMIT)],
        input=payload,
        text=True,
        capture_output=True,
        timeout=55 * 60,
        check=False,
    )
    stdout, stderr, code = proc.stdout, proc.stderr, proc.returncode
except subprocess.TimeoutExpired as exc:
    timed_out = True
    stdout = exc.stdout or ""
    stderr = exc.stderr or ""
    if isinstance(stdout, bytes):
        stdout = stdout.decode("utf-8", "replace")
    if isinstance(stderr, bytes):
        stderr = stderr.decode("utf-8", "replace")
    code = 124

hits = {}
for line in stdout.splitlines():
    parts = line.split()
    if len(parts) == 2 and parts[0].isdigit() and parts[1].isdigit():
        packed = parts[1]
        hits[int(parts[0])] = {"orientation": int(packed[0]), "dfa": packed[1:]}

found = sorted(hits)
unresolved = sorted(set(range(len(TABLES))) - set(found))
(ROOT / "0lf-hard-search-results.txt").write_text(
    "\n".join(
        f"{i} {hits[i]['orientation']} {hits[i]['dfa']}" for i in found
    ) + ("\n" if found else "")
)
stats = {
    "limit": LIMIT,
    "exit_code": code,
    "timed_out": timed_out,
    "found": found,
    "unresolved": unresolved,
    "tables": TABLES,
    "stdout": stdout,
    "stderr": stderr,
}
(ROOT / "0lf-hard-search-stats.txt").write_text(json.dumps(stats, indent=2) + "\n")
print("FAR candidate hits:")
print((ROOT / "0lf-hard-search-results.txt").read_text() or "(none)")
print(f"Unresolved IDs: {unresolved}")
print(stderr)
if code not in (0, 124):
    raise SystemExit(code)
if timed_out:
    raise SystemExit(124)
