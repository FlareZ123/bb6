"""Exact fixed-q finite shadow-cone census for the two original P1 feeders.

This evaluates only the dyadic shadow recurrence. It is NOT a proof of source
blank-root exclusion or Turing-machine nonhalting. The full source bridge still
requires source terminal obstructions, encoding, and budget/safety hypotheses.

No arbitrary simulation step cutoff enters cases reported as closed. The
implemented bound is a sanity guard only; if triggered, status is 'incomplete'.
"""
from collections import deque

VALUES = (1, 2, 6, 26, 29, 33, 37, 41, 45, 53, 65, 70, 89, 101, 113)
MAX_NODES = 1000000


def fixed_shadow(q: int, feeder: int) -> dict:
    """Compute all states of exact (m,z) shadow closure at integer q."""
    assert q >= 1 and feeder in (0, 1)
    L = 16 * q + 8 + feeder
    initial = (0, (12 if feeder == 0 else 10) * q + 4)
    visited = {initial}
    todo = deque((initial,))
    highest_cost = 0
    highest_valuation = 0
    while todo:
        m, z = todo.popleft()
        if z == 0:
            return {"status": "incomplete:zero", "count": len(visited)}
        highest_cost = max(m, highest_cost)
        v2 = (z & -z).bit_length() - 1
        highest_valuation = max(v2, highest_valuation)
        for t in range(v2 + 1):
            quotient = z // (2 ** t)
            next_double_plus_one = L + m + t + quotient
            if next_double_plus_one % 2 != 1:
                continue
            successor = (m + t + 1, (next_double_plus_one - 1) // 2)
            if successor not in visited:
                visited.add(successor)
                todo.append(successor)
                if len(visited) > MAX_NODES:
                    return {"status": "incomplete:node_cap", "count": len(visited)}
    return {
        "status": "closed",
        "count": len(visited),
        "max_cost": highest_cost,
        "max_v2_z": highest_valuation,
        "nodes": sorted(visited),
    }


def main() -> None:
    print("q,feeder0_nodes,feeder1_nodes,feeder0_cost,feeder1_cost,feeder0_max_v2,feeder1_max_v2")
    for q in VALUES:
        left, right = fixed_shadow(q, 0), fixed_shadow(q, 1)
        if left["status"] != "closed" or right["status"] != "closed":
            print(q, left, right)
            continue
        print(
            f'{q},{left["count"]},{right["count"]},'
            f'{left["max_cost"]},{right["max_cost"]},'
            f'{left["max_v2_z"]},{right["max_v2_z"]}'
        )


if __name__ == "__main__":
    main()
