"""Data and exact semantics for an independent Sheep E inverse-cone audit."""
from math import gcd

FAMILIES = [
    (118, 14580, [(0, 0, 1), (3, -2, 15), (6, -196, 135)]),
    (246, 24300, [(0, 0, 1), (5, -68, 81), (3, -2, 15),
                  (8, 266, 2025), (6, -46, 225)]),
    (558, 8100, [(0, 0, 1), (5, 22, 135), (7, -182, 675),
                 (3, -2, 15)]),
    (846, 8100, [(0, 0, 1), (5, 22, 135), (11, -37472, 8775),
                 (3, -2, 15), (6, -46, 225)]),
    (702, 11340, [(0, 0, 1), (5, 22, 135), (3, -2, 15),
                   (7, -452, 405)]),
]


def v3(n):
    ans = 0
    while n % 3 == 0:
        n //= 3
        ans += 1
    return ans


def order2(modulus):
    assert modulus % 2 == 1
    if modulus == 1:
        return 1
    power, steps = 2 % modulus, 1
    while power != 1:
        power = (power * 2) % modulus
        steps += 1
    return steps


def node_value(node, j):
    s, b, d = node
    n = 2 ** (j + s) + b
    assert n % d == 0
    return n // d


def even_return(source):
    assert source >= 6 and source % 2 == 0
    a = (source & -source).bit_length() - 1
    v = source >> a
    assert a >= 1 and v % 2 == 1 and v >= 3
    z = source + a + (3 if v == 3 else (v - 1) // 2)
    h = ((z - 1) & (1 - z)).bit_length() - 1
    return 1 + 3 ** h * ((z - 1) >> h)


def same_node(n1, n2):
    s, b, d = n1
    t, c, e = n2
    return (2 ** s) * e == (2 ** t) * d and b * e == c * d
