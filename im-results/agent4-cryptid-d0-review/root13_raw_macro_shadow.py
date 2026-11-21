#!/usr/bin/env python3
"""Replay external A_step2 macros 11--13 on the lifted authentic-root section.

This uses the same sparse raw-machine A_step2 simulator that generated
macro_trace.json, but starts from the actual DRegular root state at section
index 31,777 and its ten-step DRegular successor. It is computational evidence,
not a Lean proof.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "im-results" / "agent2-cryptid-continuity"))
sys.path.insert(0, str(ROOT / "im-results" / "agent4-cryptid-macro-replay"))

from check_eighth_root import L, find_exception, second_of_exception, advance
from cryptid_A_step2_replay import replay_macro, dregular_suffix, ARGS

C = 1975700577069254261393123959451562008800234946348086
TRACE = ROOT / "im-results" / "agent4-cryptid-macro-replay" / "macro_trace.json"
steps = json.loads(TRACE.read_text())["steps"]

# Reach the exact index-31,777 DRegular section from the authentic-root seed.
state = L(9, 0, 0)
index = 0
for episode in range(1, 6):
    index, state = find_exception(state, index)
    state = second_of_exception(state)
    assert state is not None
    index += 2
assert index == 27293
state = advance(state, 31777-index)
index = 31777
assert state.q == 0 and state.b == 0
assert (state.a-C) % (3**14) == 3**13
p = (state.a-C)//(3**13)
assert p % 2187 == 205

# The first ten DRegular transitions reach the q=4,b=1 exceptional input.
state = advance(state, 10)
index += 10
assert index == 31787 and (state.q, state.b) == (4, 1)
root_n = state.a
root_suffix = dregular_suffix(4, 1)
assert root_suffix == steps[10]["input_suffix"]

rows = []
for j in range(10, 13):
    ext = steps[j]
    m = ARGS[j]
    assert m == ext["a_step2_argument"]
    assert root_n % 3 == ext["input_n_mod3"]
    assert root_suffix == ext["input_suffix"]

    out_n, out_suffix, info = replay_macro(root_n, root_suffix, m)
    ext_out_n = int(ext["output_n"])
    assert out_suffix == ext["output_suffix"]

    diff = out_n - ext_out_n
    v3 = 0
    while diff and diff % 3 == 0:
        diff //= 3
        v3 += 1
    expected_v3 = 12-j
    assert v3 == expected_v3

    rows.append({
        "macro": j+1,
        "argument": m,
        "branch": ext["branch"],
        "input_residue": root_n % 3,
        "root_K_bits": int(info["K"]).bit_length(),
        "external_K_bits": int(ext["sweep_block_pairs"]).bit_length(),
        "root_output_bits": out_n.bit_length(),
        "external_output_bits": ext_out_n.bit_length(),
        "suffix": "".join(map(str, out_suffix)),
        "suffix_match": True,
        "output_difference_v3": v3,
    })
    root_n, root_suffix = out_n, out_suffix

assert root_n % 3 == 1
assert int(steps[13]["input_n"]) % 3 == 2
assert root_suffix == steps[12]["output_suffix"]

print("root section index:", 31777)
print("root parameter bits:", state.a.bit_length())
print("p mod 2187:", p % 2187)
for row in rows:
    print(row)
print("after macro 13: root residue", root_n % 3,
      "external macro-14 residue", int(steps[13]["input_n"]) % 3)
print("PASS: raw A_step2 replay matches branches/suffixes for macros 11-13")
print("PASS: output-difference v3 values are 2, 1, 0; divergence at macro 14")
