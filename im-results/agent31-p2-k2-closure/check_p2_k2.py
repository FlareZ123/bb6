"""Independent literal-table regression for D E,p=2 k=3t+2 packets.

192 exact pairs of FIRST physical F/0 returns, including complete right tape.
Synthetic F/0 starts only. This bounded check does not prove all-t,u claims.
"""
TABLE = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def first_physical_return(right: list[int]) -> tuple[int, list[int]]:
    occupied = {i for i, bit in enumerate(right, start=1) if bit}
    head, state = 0, 5
    for elapsed in range(1, 300001):
        instruction = TABLE[state][int(head in occupied)]
        assert instruction is not None, ("unexpected halt", elapsed - 1)
        write, direction, state = instruction
        if write:
            occupied.add(head)
        else:
            occupied.discard(head)
        head += direction
        if state == 5 and head not in occupied and all(i > head for i in occupied):
            return elapsed, [int(i in occupied) for i in range(head + 1, max(occupied, default=head) + 1)]
    raise AssertionError("event timeout at 300000 defined primitive transitions")


def expected(t: int, u: int, j: int) -> tuple[int, int, list[int], list[int]]:
    k, q, a = 3 * t + 2, 3 * u + j, 8 * t + 6
    m, r = 4 * a + 3, 2 * u + (3 if j == 2 else 2)
    e_time = 12 * k * k + 49 * k + 68 + 4 * q
    first = [1] * (8 * k + 5) + [0] + [1] * (2 * q + 6) + [0, 1] * 3 + [1, 1]
    triple_cost = 6 * m * r + 29 * r + 12 * r * r
    a_prefix = 12 * a * a + 41 * a + 32
    if j == 0:
        a_time = a_prefix + triple_cost + 2 * (m + 4 * r) + 6
        second = [1] * (2 * (m + 4 * r) + 6) + [0, 1, 0, 1, 1, 1]
    elif j == 1:
        a_time = a_prefix + triple_cost + 2 * (m + 4 * r) + 36
        second = [1] * (2 * (m + 4 * r) + 5) + [0, 1] * 4
    else:
        a_time = a_prefix + triple_cost + 6 + 6 * (m + 4 * r + 3) + 41 + 2 * (m + 4 * r + 7) + 6
        second = [1] * (2 * (m + 4 * r + 7) + 5)
    return e_time, a_time, first, second


def main() -> None:
    counts = [0, 0, 0]
    max_elapsed = 0
    for t in range(8):
        for u in range(8):
            for j in range(3):
                k, q = 3 * t + 2, 3 * u + j
                original = [1] * (3 * k + 4) + [0, 1] * q + [0, 1, 1, 0] + [1] * 6
                expected_e, expected_a, expected_first, expected_second = expected(t, u, j)
                e_time, first = first_physical_return(original)
                assert (e_time, first) == (expected_e, expected_first), (t, u, j, "first")
                a_time, second = first_physical_return(first)
                assert (a_time, second) == (expected_a, expected_second), (t, u, j, "second")
                counts[j] += 1
                max_elapsed = max(max_elapsed, e_time + a_time)
    for j, count in enumerate(counts):
        print(f"q residue {j}: PASS {count} source-table two-first-return tests, full tapes and exact times")
    print(f"PASS {sum(counts)} instances: t,u=0..7, j=0..2; longest two-event run {max_elapsed} steps")
    print("Scope: bounded synthetic-start evidence, not a universal proof or genuine blank-root result")


if __name__ == "__main__":
    main()
