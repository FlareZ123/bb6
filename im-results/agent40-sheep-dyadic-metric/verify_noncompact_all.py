"""Every m divisible by 16: finite -2 self-loop prefixes, no infinite real lift.

For m=2^p*q (p>=4,q odd), choose x0=4^N*m-2. Its N genuine
first-even returns all remain -2 modulo m, and the next return exits.
The no-infinite positive integer statement is proved in the companion
paper and Lean's modulo-16 forced section orbit.
"""


def first_even(x: int) -> int:
    assert x >= 14 and x%16 == 14
    u = x//2
    assert u >= 7 and u%2 == 1
    f = x+1+(u-1)//2
    assert f == (5*x+2)//4 and f%2 == 0
    return f


def check() -> None:
    total = 0
    for p in range(4,11):
        for q in (1,3,5,7,9,11,15,21,25,35):
            m = (1 << p)*q
            for n in range(40):
                x = 4**n*m-2
                for i in range(n+1):
                    assert x%m == m-2
                    assert x+2 == (5**i)*(4**(n-i))*m
                    if i < n:
                        x = first_even(x)
                x_next = first_even(x)
                assert x_next%m != m-2
                total += 1
    print(f"PASS {total} literal finite generic self-loop trajectories "
          "over 70 moduli")


if __name__ == "__main__":
    check()
