"""Exact independent finite shortest-distance validation of generic Sheep dyadic graph.

Run from this directory with Python 3. Imports only the two independently
written Agent40 arithmetic modules in the same folder. No input files, no
network and no randomness. The all-parameter result is a paper theorem,
not an inference from these finite tests.
"""
from collections import Counter, deque
from math import comb
from coherent_independent import decode
from mixed_independent import dyadic_parent


def verify():
    total_vertices = 0
    total_edges = 0
    for p in range(1, 16):
        modulus = 1 << p
        distances = {0: 0}
        queue = deque([0])
        while queue:
            target = queue.popleft()
            for a in range(1, p):
                for h in range(p-a):
                    parent = dyadic_parent(p, a, h, target)
                    total_edges += 1
                    if parent not in distances:
                        distances[parent] = distances[target]+1
                        queue.append(parent)
        assert len(distances) == modulus//2
        shells = Counter()
        for source in range(0, modulus, 2):
            code_length = len(decode(p, source))
            assert distances[source] == code_length, (p, source, distances[source], code_length)
            shells[code_length] += 1
            total_vertices += 1
        assert all(shells[j] == comb(p, 2*j) for j in range(p//2+1))
        print(f'PASS p={p}, vertices={modulus//2}, maximum shortest distance={max(distances.values())}',flush=True)
    print(f'PASS {total_vertices} vertices, {total_edges} exact algebraic reverse edges; all canonical lengths and binomial layers match')


if __name__ == '__main__':
    verify()
