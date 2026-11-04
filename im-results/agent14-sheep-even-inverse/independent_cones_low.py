"""Exact full-period low-a generic Sheep inverse classification."""
from math import gcd
from independent_cones_data import order2, same_node, node_value, even_return


def scan_low(j0, period, nodes, i, h, cutoff):
    s, b, d = nodes[i]
    D = d * 3 ** h
    C = D + 2 ** h * (b - d)
    matches_edges = []
    period_cases = 0
    for a in range(1, cutoff):
        K = D * (2 * a - 1) - 2 * C
        M = D * (2 ** (a + 1) + 1)
        order = order2(M)
        assert pow(2, order, M) == 1
        q = order // gcd(order, period)
        assert pow(2, period * q, M) == 1
        samples = sum(pow(2, j0 + period*k + s + h + 1, M) == K % M
                      for k in range(q))
        period_cases += q
        if not samples:
            continue
        assert samples == q, (j0, i, h, a, samples, q)
        child = (s + a + h + 1,
                 2 ** (a+h+1) * (b-d) + 2 ** a * D * (3-2*a), M)
        indices = [z for z, node in enumerate(nodes) if same_node(node, child)]
        assert len(indices) == 1, (j0, i, h, a, child)
        target = indices[0]
        assert target > i
        N = j0 + s + h + 1
        assert (2 ** N - K) % M == 0
        v = (2 ** N - K) // M
        assert v >= 5 and v % 2 == 1
        x = 2 ** a * v
        assert x == node_value(nodes[target], j0)
        assert even_return(x) == node_value(nodes[i], j0)
        j1 = j0 + period
        v1 = (2 ** (j1+s+h+1) - K) // M
        assert v1 >= 5 and v1 % 2 == 1
        assert even_return(2 ** a * v1) == node_value(nodes[i], j1)
        matches_edges.append((i, target, h, a))
    return matches_edges, cutoff-1, period_cases
