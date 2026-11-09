"""Exhaustive modular certificate for all-depth Sheep special-source exits.

The exact h=0 exceptional source equation is x=3*2**a+a+3.
For every P-chain step x->y, x+12 == 2*(y+12) (mod 5)
and x+12 == -(y+12) (mod 17). The parent quotients have
(Y+12) mod (5,17) equal to (3,2) for Z and (1,4) for X.
"""

from math import lcm

PERIOD = lcm(24, 5, 17)
TERMINAL_PERIOD = lcm(192, 5, 17)


def source_offset(a: int, modulus: int) -> int:
    return (3 * pow(2, a, modulus) + a + 15) % modulus


def interior_candidates(a_mod_5_17: tuple[int, int], depth: int) -> list[int]:
    residue5, residue17 = a_mod_5_17
    target5 = residue5 * pow(2, depth, 5) % 5
    target17 = (residue17 * (-1 if depth % 2 else 1)) % 17
    return [
        a for a in range(PERIOD)
        if a % 24 == 9
        and source_offset(a, 5) == target5
        and source_offset(a, 17) == target17
    ]


def run() -> None:
    assert PERIOD == 2040
    assert TERMINAL_PERIOD == 16320
    expected = {
        "Z": [1137, 1065, 321, 1473],
        "X": [1785, 1641, 153, 417],
    }
    for name, quotient_residues in (("Z", (3, 2)), ("X", (1, 4))):
        results = []
        for depth in range(4):
            hits = interior_candidates(quotient_residues, depth + 4)
            assert len(hits) == 1, (name, depth, hits)
            results.append(hits[0])
            print(f"{name} positive P-depth {depth} mod4: exceptional a={hits[0]} (mod {PERIOD})")
        assert results == expected[name]
        for depth in range(4, 12):
            assert interior_candidates(quotient_residues, depth) == [results[depth % 4]]

    terminal_z = [
        a for a in range(TERMINAL_PERIOD)
        if a % 192 == 189
        and source_offset(a, 5) == 3
        and source_offset(a, 17) == 2
    ]
    assert terminal_z == [7677], terminal_z
    print(f"Z terminal P-depth zero: exceptional a={terminal_z[0]} (mod {TERMINAL_PERIOD})")


if __name__ == "__main__":
    run()
