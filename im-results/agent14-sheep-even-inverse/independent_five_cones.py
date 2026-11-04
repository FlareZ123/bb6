"""Independent five-cone proof-premise audit. Standard library only."""
from math import gcd
from independent_cones_data import FAMILIES, node_value
from independent_cones_bounds import check_bounds
from independent_cones_low import scan_low


def audit_family(j0, period, nodes):
    assert nodes[0] == (0, 0, 1)
    edges, rows, samples, hrows = [], 0, 0, 0
    for i, node in enumerate(nodes):
        cutoffs = check_bounds(j0, period, node)
        hrows += len(cutoffs)
        for h, cutoff in enumerate(cutoffs):
            new_edges, low_rows, representatives = scan_low(
                j0, period, nodes, i, h, cutoff)
            edges.extend(new_edges)
            rows += low_rows
            samples += representatives
    assert sorted(target for _, target, _, _ in edges) == list(range(1, len(nodes)))
    for i, (s, b, d) in enumerate(nodes):
        for t, (s2, b2, d2) in enumerate(nodes[:i]):
            A = 2 ** s * d2 - 2 ** s2 * d
            B = b * d2 - b2 * d
            value = A * 2 ** j0 + B
            assert value != 0 and (A == 0 or value * A > 0), (j0, i, t)
    assert 10 not in [node_value(node, j0) for node in nodes]
    return dict(j=j0, period=period, nodes=len(nodes), edges=edges,
                h_rows=hrows, a_rows=rows, period_representatives=samples,
                exceptional_gap_rows=hrows)


def main():
    totals = [0, 0, 0]
    for family in FAMILIES:
        info = audit_family(*family)
        print("PASS:", info, flush=True)
        for i, key in enumerate(("h_rows", "a_rows", "period_representatives")):
            totals[i] += info[key]
    for i, (j, p, _) in enumerate(FAMILIES):
        for j2, p2, _ in FAMILIES[:i]:
            assert (j - j2) % gcd(p, p2) != 0
    print("PASS: all families disjoint; total h/a/residue rows:", totals)


if __name__ == "__main__":
    main()
