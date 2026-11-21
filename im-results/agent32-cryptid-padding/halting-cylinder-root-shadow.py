#!/usr/bin/env python3
"""Screen the A-step2 source-family interpreter for the external BB(6) cylinder.

This is an exact integer replay of the existing macro_engine.py, not a Lean
proof of the combined source chain. It records the closest pure-unary
3-adic shadow to the published C mod 3^108 cylinder in a finite prefix.
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "im-results" / "agent37-root-language-pilot"))
from macro_engine import Config, step  # noqa: E402

C = 1975700577069254261393123959451562008800234946348086
SECTIONS = 20_000
LOW_POWER = 10
LOW_MODULUS = 3**LOW_POWER
LOW_TARGET = C % LOW_MODULUS

# Suffixes of the five known suffix-parametric cylinder candidates:
# (q,b) = (0,0), (1,0), (1,1), (3,1), (4,1).
TARGET_SUFFIXES = {
    "": "q0_b0",
    "01": "q1_b0",
    "011": "q1_b1",
    "0101011": "q3_b1",
    "010101011": "q4_b1",
}


def v3(value: int) -> int:
    if value == 0:
        return 10**9
    value = abs(value)
    out = 0
    while value % 3 == 0:
        value //= 3
        out += 1
    return out


def branch(config: Config) -> str:
    return ("A", "E", "B")[config.n % 3]


def main() -> None:
    trace_path = ROOT / "im-results" / "agent4-cryptid-macro-replay" / "macro_trace.json"
    with trace_path.open() as handle:
        external_trace = json.load(handle)
    external_prefix = "".join(row["branch"] for row in external_trace["steps"][:9])

    maxima = {
        name: {"v3": -1, "index": None, "n_mod_3_10": None}
        for name in TARGET_SUFFIXES.values()
    }
    low_residue_hits = []
    reset_events = []
    counts: Counter[str] = Counter()
    best = None
    config = Config(9, "")

    for index in range(SECTIONS):
        name = TARGET_SUFFIXES.get(config.suffix)
        if name is not None:
            valuation = v3(config.n - C)
            if valuation > maxima[name]["v3"]:
                maxima[name] = {
                    "v3": valuation,
                    "index": index,
                    "n_mod_3_10": config.n % LOW_MODULUS,
                }
            if config.n % LOW_MODULUS == LOW_TARGET:
                low_residue_hits.append({"index": index, "suffix": name})

        if config.suffix == "":
            valuation = v3(config.n - C)
            if best is None or valuation > best["v3"]:
                best = {
                    "index": index,
                    "n": config.n,
                    "n_bits": config.n.bit_length(),
                    "v3": valuation,
                    "p_mod_3": ((config.n - C) // (3**valuation)) % 3
                    if valuation < 10**9 else 0,
                    "n_mod_3_10": config.n % LOW_MODULUS,
                }

        family, cost, nxt = step(config)
        counts[family] += 1
        if family == "E_pairs_1100":
            reset_events.append({
                "index": index,
                "n_mod_27": config.n % 27,
                "suffix": config.suffix,
            })
        if cost is None or nxt is None:
            raise RuntimeError(
                f"interpreter stopped at {index}: {family}; "
                f"n_bits={config.n.bit_length()}, suffix={config.suffix!r}"
            )
        config = nxt

    assert best is not None
    near = Config(best["n"], "")
    root_prefix = []
    for _ in range(9):
        root_prefix.append(branch(near))
        family, cost, nxt = step(near)
        if cost is None or nxt is None:
            raise RuntimeError(f"near-hit prefix stopped at {family}")
        near = nxt
    root_prefix = "".join(root_prefix)

    match = 0
    for left, right in zip(root_prefix, external_prefix):
        if left != right:
            break
        match += 1

    print(json.dumps({
        "status": "model-only; not a Lean/source-composition proof",
        "sections": SECTIONS,
        "C_mod_3_10": LOW_TARGET,
        "best_pure_unary_shadow": {
            **best,
            "n": str(best["n"]),
            "p_mod_3": best["p_mod_3"],
        },
        "root_next_9_branches": root_prefix,
        "external_next_9_branches": external_prefix,
        "matching_prefix_length": match,
        "reset_events": reset_events,
        "family_counts": dict(counts),
        "suffix_class_maxima": maxima,
        "low_modulus_hits": low_residue_hits,
        "final_state": {
            "n_bits": config.n.bit_length(),
            "suffix": config.suffix,
        },
    }, indent=2))


if __name__ == "__main__":
    main()
