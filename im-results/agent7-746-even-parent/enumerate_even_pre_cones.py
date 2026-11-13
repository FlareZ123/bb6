#!/usr/bin/env python3
"""Exact BigInt reverse-parent census for the #746 even fatal predecessor.

The two parent formulae below are copied algebraically from ResetParent in
im-results/agent10-cascade/FirstInverseComplete.lean. This script is a data
generator/diagnostic, not a proof: a Lean closed-cone certificate must still
check every generated predecessor against the source ResetParent relation.
"""
from __future__ import annotations

import argparse
import json
import re
from collections import deque
from pathlib import Path


def v3_valuation(x: int) -> int:
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def reset_parents(u: int) -> tuple[list[tuple[int, str, int | None]], int]:
    """Return every h with ResetParent h u, plus v3(2*u+5)."""
    out: list[tuple[int, str, int | None]] = []

    # The even image band has a unique scale k = bit_length(u)-3.
    k = u.bit_length() - 3
    if k >= 0:
        p = 1 << k
        if 6 * p - 1 <= u <= 8 * p - 3:
            h = 2 * u - 8 * p - k
            assert h >= 0
            out.append((h, "even", None))

    # Enumerate every odd exponent t with 3^(t+1) | 2*u+5.
    numerator = 2 * u + 5
    valuation = v3_valuation(numerator)
    power3 = 3
    for t in range(valuation):
        d = numerator // power3
        if d & 1:
            x = (1 << t) * d
            k = x.bit_length() - 3
            if k >= 0:
                p = 1 << k
                if 6 * p + 1 <= x <= 8 * p - 1:
                    h = 2 * x - 8 * p - k - 5
                    assert h >= 0
                    out.append((h, "odd", t))
        power3 *= 3

    return out, valuation


def main_even_chain(n: int) -> list[int]:
    """The same-scale even-parent orbit y_m = 4*2^n - D_m."""
    power2 = 1 << n
    deficit = 3 * n + 7
    chain: list[int] = []
    while deficit <= power2 + 1:
        chain.append(4 * power2 - deficit)
        deficit = 2 * deficit + n - 1
    return chain


def reverse_cone(n: int) -> tuple[set[int], dict[str, int]]:
    if n < 4:
        raise ValueError("n must be at least 4")
    power2 = 1 << n
    target = 4 * power2 - 3 * n - 7
    chain = main_even_chain(n)
    chain_set = set(chain)
    assert chain and chain[0] == target

    depths = {target: 0}
    branch_ids = {target: -1}
    queue = deque([target])
    branch_stats: dict[int, dict[str, int]] = {}
    branch_counter = 0
    edges = leaves = merges = odd_edges = odd_branches = 0
    max_v3 = max_odd_t = 0

    while queue:
        u = queue.popleft()
        depth = depths[u]
        parents, valuation = reset_parents(u)
        max_v3 = max(max_v3, valuation)
        edges += len(parents)
        if not parents:
            leaves += 1

        for h, kind, t in parents:
            if kind == "odd":
                odd_edges += 1
                assert t is not None
                max_odd_t = max(max_odd_t, t)

            if h in depths:
                merges += 1
                continue

            child_depth = depth + 1
            if u in chain_set and kind == "odd":
                branch_counter += 1
                odd_branches += 1
                branch_id = branch_counter
                branch_stats[branch_id] = {
                    "root_depth": child_depth,
                    "size": 1,
                    "depth": 1,
                }
            else:
                branch_id = branch_ids[u]
                if branch_id >= 0:
                    stats = branch_stats[branch_id]
                    stats["size"] += 1
                    stats["depth"] = max(
                        stats["depth"],
                        child_depth - stats["root_depth"] + 1,
                    )

            depths[h] = child_depth
            branch_ids[h] = branch_id
            queue.append(h)

    values = set(depths)
    assert chain_set <= values
    min_bits = min(x.bit_length() for x in values)
    stats = {
        "n": n,
        "target": target,
        "nodes": len(values),
        "edges": edges,
        "leaves": leaves,
        "max_depth": max(depths.values()),
        "main_chain": len(chain),
        "off_chain": len(values) - len(chain),
        "odd_branches_from_main_chain": odd_branches,
        "odd_edges_total": odd_edges,
        "max_side_branch_size": max(
            (s["size"] for s in branch_stats.values()), default=0
        ),
        "max_side_branch_depth": max(
            (s["depth"] for s in branch_stats.values()), default=0
        ),
        "max_v3_of_2u_plus_5": max_v3,
        "max_odd_exponent_t": max_odd_t,
        "minimum_bit_length": min_bits,
        "minimum_log2_deficit_from_n": n - (min_bits - 1),
        "merges": merges,
        "contains_root_2": 2 in values,
        "is_tree": edges == len(values) - 1 and merges == 0,
    }
    return values, stats


def emit_lean(n: int, values: set[int], path: Path) -> None:
    name = f"evenPre{n}"
    sorted_values = sorted(values)
    lines = [
        "import ClosedCertFast",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "",
        f"namespace CascadeEvenPre{n}",
        "open CascadeResetInverse",
        "",
        f"def {name} : Nat := 4*2^{n}-{3*n+7}",
        f"def {name}Cone : List Nat := [",
    ]
    for i, value in enumerate(sorted_values):
        comma = "," if i + 1 < len(sorted_values) else ""
        lines.append(f"  0x{value:x}{comma}")
    lines.extend(
        [
            "]",
            "",
            f"theorem {name}Cone_closed :",
            f"    closedCertFast {name}Cone = true := by",
            "  native_decide",
            "",
            f"theorem {name}Cone_mem : {name} ∈ {name}Cone := by",
            "  native_decide",
            "",
            f"theorem two_not_mem_{name}Cone : 2 ∉ {name}Cone := by",
            "  native_decide",
            "",
            f"theorem {name}_root_unreachable :",
            f"    ¬ CascadeSweep.ReachC (2,0) ({name},0) := by",
            f"  exact closedCertFast_excludes {name} {name}Cone",
            f"    {name}Cone_closed {name}Cone_mem two_not_mem_{name}Cone",
            "",
            f"end CascadeEvenPre{n}",
            "",
        ]
    )
    path.write_text("\n".join(lines))


def compare_lean(values: set[int], path: Path) -> dict[str, int]:
    source = path.read_text()
    source = source.split("theorem evenPre887Cone_closed", 1)[0]
    listed = {int(token, 16) for token in re.findall(r"0x[0-9a-fA-F]+", source)}
    return {
        "listed_nodes": len(listed),
        "computed_nodes": len(values),
        "missing_from_lean": len(values - listed),
        "extra_in_lean": len(listed - values),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--compare-lean", type=Path)
    parser.add_argument("--emit-lean", type=Path)
    args = parser.parse_args()

    values, stats = reverse_cone(args.n)
    output: dict[str, object] = stats
    if args.compare_lean:
        output["comparison"] = compare_lean(values, args.compare_lean)
    if args.emit_lean:
        emit_lean(args.n, values, args.emit_lean)
        output["lean_output"] = str(args.emit_lean)
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
