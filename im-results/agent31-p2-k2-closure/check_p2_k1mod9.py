"""Literal original D-machine regression: E,p=2 with k=9s+1.

45 synthetic starts (s=0..2,u=0..4,j=0..2): exactly three FIRST
physical F/0 returns each, exact times and all right cells. Bounded only.
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
    for elapsed in range(1, 1000001):
        instruction = TABLE[state][int(head in occupied)]
        assert instruction is not None, ("unexpected undefined F/1 halt", elapsed-1)
        write, direction, state = instruction
        if write:
            occupied.add(head)
        else:
            occupied.discard(head)
        head += direction
        if state == 5 and head not in occupied and all(i > head for i in occupied):
            return elapsed, [int(i in occupied) for i in range(head+1, max(occupied, default=head)+1)]
    raise AssertionError("first physical F/0 return timeout at 1000000 steps")


def predicted(s: int, u: int, j: int) -> tuple[tuple[int, ...], tuple[list[int], ...]]:
    k, q = 9*s+1, 3*u+j
    ke, ka = 24*s+3, 64*s+10
    m = 4*ka+3
    r = 2*u + (2 if j == 2 else 1)
    e1 = 12*k*k+49*k+68+4*q
    e2 = 12*ke*ke+49*ke+58
    prefix_cost = 12*ka*ka+41*ka+32
    triple_cost = 6*(m+2)*r+29*r+12*r*r
    delta = m+2+4*r
    if j == 0:
        a = prefix_cost+4+triple_cost+2*delta+6
        final = [1]*(2*delta+6)+[0, 1, 0, 1, 1, 1]
    elif j == 1:
        a = prefix_cost+4+triple_cost+2*delta+36
        final = [1]*(2*delta+5)+[0, 1]*4
    else:
        a = prefix_cost+4+triple_cost+6+(6*(delta+3)+41)+2*(delta+7)+6
        final = [1]*(2*(delta+7)+5)
    first = [1]*(8*k+5)+[0]+[1]*(2*q+6)+[0, 1]*3+[1, 1]
    second = [1]*(8*ke+9)+[0, 1]*2+[0]+[1]*(2*q+3)+[0, 1]*3+[1, 1]
    return (e1, e2, a), (first, second, final)


def main() -> None:
    counts = [0, 0, 0]
    max_steps = 0
    for s in range(3):
        for u in range(5):
            for j in range(3):
                k, q = 9*s+1, 3*u+j
                original = [1]*(3*k+4)+[0, 1]*q+[0, 1, 1, 0]+[1]*6
                costs, outputs = predicted(s, u, j)
                total = 0
                for stage in range(3):
                    elapsed, original = first_physical_return(original)
                    assert (elapsed, original)==(costs[stage], outputs[stage]), (s,u,j,stage,elapsed,costs[stage])
                    total += elapsed
                counts[j] += 1
                max_steps = max(max_steps, total)
    for j, n in enumerate(counts):
        print(f"q≡{j} (mod 3): PASS {n} complete three-return original-table traces")
    print(f"PASS {sum(counts)} instances, {sum(counts)*3} first physical F/0 returns, longest {max_steps} primitive steps")
    print("Synthetic starts; bounded validation only. No all-parameter original-source CI claim.")


if __name__ == "__main__":
    main()
