#!/usr/bin/env python3
"""Reconstruct terminal survivors and intersect the last-reset equation."""
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
# Expansion of BB429Mod8.Allowed from im-results/agent6-harmonic429/BB429Mod8.lean.
allowed8 = {
    (0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),
    (4,2),(5,0),(5,1),(5,2),(5,3),(6,2),(7,2),(7,3),
}
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
    after_mod8 = []
    lifts = 16 // min(16, modulus)
    for residue in residues:
        possible = False
        for k in range(lifts):
            d = residue + k * modulus
            if branch == 9:
                x = (2**(n + 2) * (d + 10) + 2*d - 3*n - 25) // 4
            else:
                x = (2**(n + 2) * (d + 6) + 2*d - 3*n - 21) // 4
            y = 2 * (x - d) + 1
            if (x % 8, y % 4) in allowed8:
                possible = True
                break
        if possible:
            after_mod8.append(residue)
    rows.append({
        "n": n,
        "branch": branch,
        "modulus": modulus,
        "terminal_sieve_count": len(residues),
        "mod8_prestate_count": len(after_mod8),
        "d_residues_modulus": residues,
        "d_residues_after_mod8_prestate": after_mod8,
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

long_burst_mod16 = []
for n_mod32 in range(1, 32, 2):
    branch = 9 if n_mod32 % 4 == 1 else 10
    allowed_d = []
    for d in range(16):
        if (branch == 9 and d % 2 != 0) or (branch == 10 and d % 2 != 1):
            continue
        numerator = (2*d - 3*n_mod32 - 25) if branch == 9 else (2*d - 3*n_mod32 - 21)
        assert numerator % 4 == 0
        x = (numerator // 4) % 8
        y4 = (2 * (x - d) + 1) % 4
        y8 = (2 * (x - d) + 1) % 8
        # BB429RootMod16.rooted_not_7_7 excludes the rooted pair (7,7).
        if (x, y4) in allowed8 and not (x == 7 and y8 == 7):
            allowed_d.append(d)
    long_burst_mod16.append({
        "n_mod32": n_mod32,
        "branch": branch,
        "allowed_d_mod16": allowed_d,
        "rooted_not_7_7_applied": True,
    })

expected_long_burst = {
    1: [4, 8], 3: [1, 5, 9], 5: [2, 10, 14], 7: [7, 11, 15],
    9: [0, 4], 11: [1, 5, 13], 13: [6, 10, 14], 15: [3, 7, 11],
    17: [0, 12], 19: [1, 9, 13], 21: [2, 6, 10], 23: [3, 7, 15],
    25: [8, 12], 27: [5, 9, 13], 29: [2, 6, 14], 31: [3, 11, 15],
}
assert {row["n_mod32"]: row["allowed_d_mod16"] for row in long_burst_mod16} == expected_long_burst

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
    "root_mod8_allowed_pairs": sorted(allowed8),
    "root_mod16_not_7_7_source": "im-results/agent39-429-1021/BB429RootMod16.lean",
    "v2_distribution_of_U_plus_3": v2_distribution,
    "constant_seed_checks": constant_checks,
    "variable_branch_d_residues": rows,
    "long_burst_mod16": long_burst_mod16,
    "long_burst_mod16_scope": "Branches 9 and 10 only; constant-seed branches 1-7 remain separate for n>=18.",
}
assert len(base) == 58
assert len(excluded_parts) == 673
assert len(extra4) == 4
assert len(extra9) == 9
assert len(allowed8) == 17
assert len(survivors) == 242
out = Path(__file__).with_name("d-residues.json")
out.write_text(json.dumps(result, indent=2) + "\n")
print("n branch modulus terminal-sieve root-mod8")
for row in rows:
    print(row["n"], row["branch"], row["modulus"],
          row["terminal_sieve_count"], row["mod8_prestate_count"])
print("long-burst d mod 16:", long_burst_mod16)
print(f"Wrote {out}")
