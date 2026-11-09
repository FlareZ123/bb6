"""Classify cycles by permitted right-reentry state in original D E3 seam.

Finite abstraction only: cycles need not be physically realizable.
"""
from collections import deque
from pathlib import Path

RULES = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def successors(key):
    state, offset, bits = key & 7, (key >> 3) & 31, key >> 8
    bit = (bits >> offset) & 1
    if offset == 1 or (
        state == 5 and (bit == 1 or bits & ((1 << offset) - 1) == 0)
    ):
        return []
    write, move, next_state = RULES[state][bit]
    changed = bits | 1 << offset if write else bits & ~(1 << offset)
    position = offset + move
    assert position >= 0
    if position > 17:
        return [((changed << 8) | (17 << 3) | s, s) for s in range(6)]
    return [((changed << 8) | (position << 3) | next_state, -1)]


def maximal_path(nodes, edges, mask):
    indegree = {u: 0 for u in nodes}
    for outgoing in edges.values():
        for v, label in outgoing:
            if label < 0 or (mask >> label) & 1:
                indegree[v] += 1
    queue = deque(u for u, degree in indegree.items() if degree == 0)
    depth = dict.fromkeys(nodes, 0)
    visited = 0
    while queue:
        u = queue.popleft()
        visited += 1
        for v, label in edges[u]:
            if label < 0 or (mask >> label) & 1:
                depth[v] = max(depth[v], depth[u] + 1)
                indegree[v] -= 1
                if indegree[v] == 0:
                    queue.append(v)
    return max(depth.values()) if visited == len(nodes) else None


def main():
    path = (
        Path(__file__).resolve().parent.parent
        / "agent31-d-exceptional"
        / "ESeamClosedStates.txt"
    )
    nodes = {int(line) for line in path.read_text(encoding="utf-8").splitlines()
             if line.isdecimal()}
    edges = {u: successors(u) for u in nodes}
    assert len(nodes) == 6399
    assert sum(map(len, edges.values())) == 7306
    assert all(v in nodes for outgoing in edges.values() for v, _ in outgoing)
    assert all((171 + (r << 11)) * 256 + 84 in nodes for r in range(128))
    assert all(
        (u & 7) == 2 and ((u >> (8 + ((u >> 3) & 31))) & 1) == 1
        for u in nodes if ((u >> 3) & 31) == 1
    )
    ranks = [maximal_path(nodes, edges, subset) for subset in range(64)]
    acyclic = [s for s in range(64) if ranks[s] is not None]
    cyclic = [s for s in range(64) if ranks[s] is None]
    maximal = [a for a in acyclic if not any(
        a != b and (a & b) == a for b in acyclic
    )]
    minimal = [a for a in cyclic if not any(
        a != b and (a & b) == b for b in cyclic
    )]
    label = lambda m: ''.join(c for i, c in enumerate("ABCDEF") if (m >> i) & 1)
    assert len(acyclic) == 28 and len(cyclic) == 36
    assert sorted(map(label, maximal)) == ["BCDE", "BCEF", "BDEF"]
    assert sorted(map(label, minimal)) == ["A", "CDF"]
    assert {label(m): ranks[m] for m in maximal} == {
        "BCDE": 128, "BCEF": 137, "BDEF": 82
    }
    assert ranks[0] == 65 and ranks[12] == 110
    print("states 6399, edges 7306, seeds 128")
    print("acyclic subsets", len(acyclic), "cyclic subsets", len(cyclic))
    print("maximal acyclic subsets and longest paths:",
          [(label(m), ranks[m]) for m in maximal])
    print("minimal cyclic subsets:", [label(m) for m in minimal])
    print("C/D-only longest abstract path:", ranks[12])


if __name__ == "__main__":
    main()
