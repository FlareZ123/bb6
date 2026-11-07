"""Literal finite generic Sheep trajectories for arbitrarily long 14 mod 16 walks.

For every N<=100, x0=2^(2N+4)-2 follows N actual generic first-even
returns at residue 14 modulo 16, then leaves at the next return.
The all-N proof and a separate Lean no-infinite-start certificate are in
FINITE-NOT-INFINITE.md and SheepNoncompactLean.lean.
"""


def first_even(x: int) -> tuple[int, int, int, int]:
    assert x >= 14 and x % 16 == 14
    assert x % 2 == 0 and ((x//2) % 2) == 1 and x//2 >= 7
    f = x + 1 + (x//2-1)//2
    assert f % 2 == 0 and f == (5*x+2)//4
    return 1, 0, f, x//2


def verify(max_edges: int = 100) -> None:
    for n in range(max_edges+1):
        x = (1 << (2*n+4))-2
        x0 = x
        for i in range(n+1):
            assert x % 16 == 14
            assert x+2 == (5**i)*(1 << (2*(n-i)+4))
            if i == n:
                break
            a,h,y,u = first_even(x)
            assert a == 1 and h == 0 and u >= 7
            x = y
        _,_,next_x,_ = first_even(x)
        assert next_x % 16 != 14
        print(f"PASS {n} self-loop edges: start_bits={x0.bit_length()}, "
              f"end_bits={x.bit_length()}, exit_residue={next_x%16}")
    print(f"PASS all {max_edges+1} finite generic integer witnesses")


if __name__ == "__main__":
    verify(100)
