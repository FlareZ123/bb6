#!/usr/bin/env python3
"""Targeted phase/suffix diagnostics for the existing four-root projected grammar.

This imports the already committed Agent36 symbolic transition rules and Agent32
finite E-front interpreter. It does not simulate the original machine directly
and does not prove an all-time invariant.
"""
from __future__ import annotations

from collections import defaultdict
import json
from pathlib import Path
import sys

IM_RESULTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(IM_RESULTS / "agent36-cryptid-trace"))
sys.path.insert(0, str(IM_RESULTS / "agent32-d-route-dag"))

from trace_four_starts import ROOTS, Section, advance
from route_bfs import efront


def rank(word: str) -> int:
    trimmed = word.rstrip("0")
    occurrences = sum(
        trimmed[i : i + 3] == "011"
        for i in range(max(0, len(trimmed) - 2))
    )
    return len(trimmed) + 2 * occurrences


def four_root_metrics(macros: int = 30_000) -> dict:
    moduli = (3, 9, 27, 81, 243, 729)
    transition_maps = {m: defaultdict(set) for m in moduli}
    full_states = defaultdict(list)
    suffix_union = set()
    suffix_residue_union = set()
    suffix_mod9_union = set()
    summaries = []

    for name, seed, offset in ROOTS:
        state = Section(seed, "", offset)
        suffixes = set()
        suffix_residues = set()
        suffix_mod9 = set()
        rule_counts = defaultdict(int)
        max_rank = rank(state.suffix)
        max_length = len(state.suffix)
        max_delta = 0
        rank_over_n = None

        for i in range(macros):
            suffixes.add(state.suffix)
            suffix_union.add(state.suffix)
            residue_key = (state.suffix, state.n % 3)
            mod9_key = (state.suffix, state.n % 9)
            suffix_residues.add(residue_key)
            suffix_mod9.add(mod9_key)
            suffix_residue_union.add(residue_key)
            suffix_mod9_union.add(mod9_key)
            full_states[(state.n, state.suffix)].append((name, i))

            old_rank = rank(state.suffix)
            next_state, rule = advance(state)
            rule_counts[rule] += 1
            new_rank = rank(next_state.suffix)
            max_rank = max(max_rank, old_rank, new_rank)
            max_length = max(max_length, len(state.suffix), len(next_state.suffix))
            max_delta = max(max_delta, new_rank - old_rank)
            if rank_over_n is None and new_rank > next_state.n:
                rank_over_n = {
                    "macro": i + 1,
                    "rank": new_rank,
                    "n_bits": next_state.n.bit_length(),
                }
            state = next_state

        suffixes.add(state.suffix)
        suffix_union.add(state.suffix)
        summaries.append(
            {
                "root": name,
                "macros": macros,
                "unique_suffixes": len(suffixes),
                "unique_suffix_residue_pairs": len(suffix_residues),
                "unique_suffix_mod9_pairs": len(suffix_mod9),
                "max_suffix_length": max_length,
                "max_rank": max_rank,
                "max_rank_increment": max_delta,
                "first_rank_over_n": rank_over_n,
                "final_n_bits": state.n.bit_length(),
                "final_time_bits": state.time.bit_length(),
                "final_suffix": state.suffix,
                "rule_counts": dict(sorted(rule_counts.items())),
            }
        )

    ambiguous = {
        str(m): sum(len(outputs) > 1 for outputs in transition_maps[m].values())
        for m in moduli
    }
    # Rebuild transition maps in a separate deterministic pass. Keeping this
    # separate makes the per-root summary above easy to audit.
    for name, seed, offset in ROOTS:
        state = Section(seed, "", offset)
        for _ in range(macros):
            next_state, _ = advance(state)
            for m in moduli:
                key = (state.suffix, state.n % m)
                value = (next_state.suffix, next_state.n % m)
                transition_maps[m][key].add(value)
            state = next_state

    ambiguous = {
        str(m): {
            "keys": len(transition_maps[m]),
            "ambiguous_keys": sum(len(outputs) > 1 for outputs in transition_maps[m].values()),
            "max_distinct_outputs": max((len(outputs) for outputs in transition_maps[m].values()), default=0),
        }
        for m in moduli
    }
    merges = [
        {"n_bits": n.bit_length(), "suffix": suffix, "occurrences": occurrences}
        for (n, suffix), occurrences in full_states.items()
        if len(occurrences) > 1
    ]
    return {
        "summaries": summaries,
        "union_unique_suffixes": len(suffix_union),
        "union_suffix_residue_pairs": len(suffix_residue_union),
        "union_suffix_mod9_pairs": len(suffix_mod9_union),
        "fixed_modulus_transition_ambiguity": ambiguous,
        "exact_state_merges": merges,
    }


def synthetic_e_front_case() -> dict:
    # This residue path is a stress test, not an authentic blank-root trace.
    initial_n = 1_823_245
    state = Section(initial_n, "", 0)
    branches = []
    for _ in range(13):
        branches.append(("A", "E", "B")[state.n % 3])
        state, _ = advance(state)

    assert "".join(branches) == "EEEBBBEEEBEEE"
    assert state.n == 628_692_084_481
    assert state.suffix == "010101010110111111"
    assert state.n % 3 == 1

    front = efront(state.suffix, 12)
    assert front[0] == "return"
    output_suffix = front[1]
    output_constant = front[2]
    output_n = 8 * ((state.n - 4) // 3) + output_constant

    return {
        "initial_n": initial_n,
        "initial_mod_3_14": initial_n % (3**14),
        "modulus_3_14": 3**14,
        "branch_word_before_E_front": "".join(branches),
        "input_n": state.n,
        "input_suffix": state.suffix,
        "input_suffix_rank": rank(state.suffix),
        "next_branch": "E",
        "efront_kind": front[0],
        "efront_steps": front[3],
        "efront_left_pair_count": front[4],
        "efront_raw_output": front[5],
        "output_constant": output_constant,
        "output_n": output_n,
        "output_suffix": output_suffix,
        "output_suffix_rank": rank(output_suffix),
        "rank_increment": rank(output_suffix) - rank(state.suffix),
        "is_authentic_blank_root": False,
    }


def main() -> None:
    print(
        json.dumps(
            {
                "four_root_metrics": four_root_metrics(),
                "synthetic_e_front_case": synthetic_e_front_case(),
                "status": "finite projected diagnostics only; no all-time proof",
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
