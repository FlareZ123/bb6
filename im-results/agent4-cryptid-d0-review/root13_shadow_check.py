#!/usr/bin/env python3
"""Reproduce the 13-step DRegular/external-macro arithmetic shadow.

This is an arithmetic-model check, not a Lean source theorem.
Run from any working directory with the repository checkout intact.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "im-results" / "agent2-cryptid-continuity"))
from check_eighth_root import L, find_exception, second_of_exception, advance

C = 1975700577069254261393123959451562008800234946348086
M13 = 3**13
M14 = 3**14

# Reproduce the first five exceptional/reentry episodes from the blank-root
# DRegular seed. The sixth regular segment begins at section index 27293.
state = L(9, 0, 0)
index = 0
for episode in range(1, 6):
    index, state = find_exception(state, index)
    if episode < 6:
        state = second_of_exception(state)
        assert state is not None
        index += 2

assert index == 27293
state = advance(state, 31777 - index)
index = 31777
assert (state.q, state.b) == (0, 0)

difference = state.a - C
assert difference % M13 == 0
assert difference % M14 == M13
p = difference // M13
assert p % 3 == 1
assert p % 2187 == 205
assert p % 81 == 43
assert state.a % (3**20) == 2863782241
assert state.a.bit_length() == 44970

macro_path = ROOT / "im-results" / "agent4-cryptid-macro-replay" / "macro_trace.json"
steps = json.loads(macro_path.read_text())["steps"]
assert len(steps) >= 14

root_n = state.a
rows = []
for i, step in enumerate(steps[:13], start=1):
    external_n = int(step["input_n"])
    external_out = int(step["output_n"])
    c = int(step["affine_offset_c"])
    r = root_n % 3
    assert r == external_n % 3 == int(step["input_n_mod3"])

    root_out = 8 * ((root_n - r) // 3) + c
    diff = root_out - external_out
    v3 = 0
    while diff and diff % 3 == 0:
        diff //= 3
        v3 += 1
    assert v3 == 13 - i

    rows.append({
        "macro": i,
        "branch": step["branch"],
        "argument": step["a_step2_argument"],
        "input_residue": r,
        "difference_v3_after": v3,
        "output_suffix": "".join(map(str, step["output_suffix"])),
    })
    root_n = root_out

external_14 = int(steps[13]["input_n"])
assert root_n % 3 == 1
assert external_14 % 3 == 2

print("root section index:", index)
print("root parameter bits:", state.a.bit_length())
print("p mod 3:", p % 3)
print("p mod 2187:", p % 2187)
print("p mod 81:", p % 81)
print("a mod 3^20:", state.a % (3**20))
print("a-C mod 3^14:", difference % M14)
for row in rows:
    print(row)
print("after macro 13: root residue", root_n % 3,
      "external macro-14 residue", external_14 % 3)
print("PASS: thirteen matching macro branches; divergence at macro 14")
