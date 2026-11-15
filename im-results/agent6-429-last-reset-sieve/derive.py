#!/usr/bin/env python3
"""Reconstruct the 242 terminal residues and derive last-reset d classes.

Run from any directory:
    python3 im-results/agent6-429-last-reset-sieve/derive.py

This parses exact Lean list definitions. It does not simulate BB(6); it only
intersects the terminal sieve with the last-reset arithmetic parametrization.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[2]
FILES = {
    "base": ROOT / "im-results/agent1-429-262144-sieve/BB429SurvivorBase.lean",
    "split": ROOT / "im-results/agent1-429-262144-sieve/BB429SplitSieve.lean",
    "extra4": ROOT / "im-results/agent30-429-shifted-roots/BB429Combined677.lean",
    "extra9": ROOT / "im-results/agent30-429-shifted-roots/BB429Combined686.lean",
}

def read_list(path: Path, name: str) -> list[int]:
    text = path.read_text()
    match = re.search(
        rf"def {re.escape(name)} : List Nat :=\s*\[([\s\S]*?)\]",
        text,
    )
    if not match:
        raise ValueError(f"Could not find {name} in {path}")
    return [int(x) for x in re.findall(r"\d+", match.group(1))]

base = read_list(FILES["base"], "base58")
split_text = FILES["split"].read_text()
excluded_parts = []
for match in re.finditer(
    r"def part\d+ : List Nat :=\s*\[([\s\S]*?)\]", split_text
):
    excluded_parts.extend(int(x) for x in re.findall(r"\d+", match.group(1)))

extra4 = read_list(FILES["extra4"], "extra")
extra9 = read_list(FILES["extra9"], "extra9")
excluded = set(excluded_parts + extra4 + extra9)
survivors = sorted(
    16384 * j + r
    for j in range(16)
    for r in base
    if 16384 * j + r not in excluded
)

def v2(n: int) -> int:
    if n == 0:
        return 10**9
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k

v2_distribution: dict[str, int] = {}
for u in survivors:
    key = str(v2(u + 3))
    v2_distribution[key] = v2_distribution.get(key, 0) + 1

rows = []
for n in range(1, 18, 2):
    modulus = 1 << (18 - n)
    branch = 9 if n % 4 == 1 else 10
    if branch == 9:
        eligible = [u for u in survivors if v2(u + 3) >= n + 1]
        offset = 10  # A = u0+3 = d+10
    else:
        eligible = [u for u in survivors if v2(u + 3) == n]
        offset = 6   # A = u0+3 = d+6
    residues = sorted({
        (((u + 3) >> n) - offset) % modulus
        for u in eligible
    })
    rows.append({
        "n": n,
        "branch": branch,
        "modulus": modulus,
        "eligible_survivor_count": len(eligible),
        "distinct_d_residue_count": len(residues),
        "d_residues_modulus": residues,
    })

constant_checks = []
for n in range(1, 18, 2):
    u3 = 3 * (1 << n) - 3
    u14 = 14 * (1 << n) - 3
    constant_checks.append({
        "n": n,
        "U_for_A3": u3,
        "A3_is_survivor": u3 in survivors,
        "U_for_A14": u14,
        "A14_is_survivor": u14 in survivors,
        "valid_A14_branch": n % 4 == 1,
    })

result = {
    "source_files": {key: str(path.relative_to(ROOT)) for key, path in FILES.items()},
    "construction": {
        "base_residue_count": len(base),
        "first_exclusion_entry_count": len(excluded_parts),
        "extra_four_count": len(extra4),
        "extra_nine_count": len(extra9),
        "unique_excluded_count": len(excluded),
        "survivor_count": len(survivors),
        "modulus": 262144,
    },
    "v2_distribution_of_U_plus_3": v2_distribution,
    "constant_seed_checks": constant_checks,
    "variable_branch_d_residues": rows,
}
assert len(base) == 58
assert len(excluded_parts) == 673
assert len(extra4) == 4
assert len(extra9) == 9
assert len(survivors) == 242
out = Path(__file__).with_name("d-residues.json")
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result["variable_branch_d_residues"], indent=2))
print(f"Wrote {out}")
