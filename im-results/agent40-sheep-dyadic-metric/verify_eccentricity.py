"""Exhaustive independent validation of the all-p generic Sheep dyadic metric.

Only Python standard library. Every quotient edge is enumerated from the
published exact modular inverse relation, then checked against the
canonical-word metric via complete all-source BFS. All-p proof is in README.
Finite tests are not a proof of an unbounded physical blank-root decision.
"""
from collections import Counter, deque
from math import comb


def v2(n: int) -> int:
    return (n & -n).bit_length() - 1


def word(p: int, residue: int) -> list[tuple[int, int]]:
    result = []
    while residue:
        a = v2(residue)
        u = residue >> a
        numerator = (1 + (1 << (a + 1))) * u + 2*a - 3
        h = min(v2(numerator) - 1, p - a - 1)
        t = p - a - h - 1
        residue = (1 + 3**h * (numerator >> (h + 1))) % (1 << t)
        result.append((a, h))
        p = t
    return result


def evaluate_word(p: int, letters: list[tuple[int, int]]) -> int:
    result = 0
    for a, h in reversed(letters):
        q = 1 << (p-a)
        result = ((1 << a) * pow(1 + (1 << (a+1)), -1, q) *
                  (3-2*a + (1 << (h+1)) * pow(3**h, -1, q) *
                   (result-1))) % (1 << p)
    return result


def quotient_graph(p: int) -> dict[int, set[int]]:
    mod = 1 << p
    vertices = list(range(0, mod, 2))
    graph = {r: set() for r in vertices}
    for target in vertices:
        graph[0].add(target)  # Genuine generic zero-hub.
        for a in range(1, p):
            modulus = 1 << (p-a)
            dinv = pow(1 + (1 << (a+1)), -1, modulus)
            for h in range(p-a):
                parent = ((1 << a) * dinv *
                          (3-2*a + (1 << (h+1)) * pow(3**h, -1, modulus) *
                           (target-1))) % mod
                graph[parent].add(target)
    return graph


def bfs(graph: dict[int, set[int]], start: int) -> dict[int, int]:
    dist = {start: 0}
    queue = deque([start])
    while queue:
        vertex = queue.popleft()
        for target in graph[vertex]:
            if target not in dist:
                dist[target] = dist[vertex] + 1
                queue.append(target)
    return dist


def check_exact_cylinders(p: int, graph: dict[int, set[int]]) -> int:
    checked = 0
    for source in graph:
        letters = word(p, source)
        reached = {source}
        cost = 0
        for k in range(len(letters)+1):
            t = p-cost
            tail = evaluate_word(t, letters[k:])
            assert word(t, tail) == letters[k:], (p, source, letters, k)
            predicted = {r for r in graph if r % (1 << t) == tail}
            assert reached == predicted, (
                p, source, k, sorted(reached.symmetric_difference(predicted))[:10]
            )
            checked += 1
            if k < len(letters):
                reached = set().union(*(graph[r] for r in reached))
                a, h = letters[k]
                cost += a+h+1
    return checked


def check(max_p: int = 11) -> None:
    cylinders = 0
    for p in range(1, max_p+1):
        graph = quotient_graph(p)
        vertices = 1 << (p-1)
        assert len(graph) == vertices
        if p <= 9:
            count = check_exact_cylinders(p, graph)
            cylinders += count
            print(f"PASS p={p}: {count} exact-k cylinders", flush=True)

        histogram = Counter()
        far_target = (1 << p)-2
        for source in graph:
            letters = word(p, source)
            length = len(letters)
            cost = sum(a+h+1 for a,h in letters)
            assert cost <= p
            dist = bfs(graph, source)
            assert len(dist) == vertices
            assert dist[0] == length
            ecc = max(dist.values())
            assert ecc == length + int(cost <= p-2), (
                p, source, letters, cost, ecc
            )
            if cost <= p-2:
                assert dist[far_target] == length+1
            histogram[ecc] += 1

        expected = ({0: 1} if p == 1 else
                    {j: 2*comb(p-1, 2*j-1) for j in range(1,p//2+1)})
        assert histogram == expected, (p, histogram, expected)
        print(f"PASS p={p}: {vertices} vertices, "
              f"{sum(map(len,graph.values()))} edges; "
              f"eccentricities {dict(sorted(histogram.items()))}", flush=True)
    print(f"PASS all p<= {max_p}; {cylinders} exact-k cylinders checked", flush=True)


if __name__ == "__main__":
    check()
