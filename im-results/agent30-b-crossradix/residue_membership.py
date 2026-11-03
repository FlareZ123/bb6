"""Exact finite-depth residue membership for Machine B's scalar G.

No halting decision follows from a finite-depth residue computation.
"""


def g(z: int) -> int:
    assert z >= 0
    return 3 * (z // 2) + 4 + 5 * (z & 1)


def g_iter(n: int, z: int) -> int:
    assert n >= 0 and z >= 0
    for _ in range(n):
        z = g(z)
    return z


def in_output_residues(n: int, r: int) -> bool:
    """Test r in {G^n(x) mod 3^n : 0 <= x < 2^n}, O(n) arithmetic operations.

    The inverse residue step uses G(2q)=3q+4 and G(2q+1)=3q+9.
    """
    assert n >= 0
    modulus = 3**n
    r %= modulus
    for _ in range(n):
        mod3 = r % 3
        if mod3 == 2:
            return False
        parity = int(mod3 == 0)
        next_modulus = modulus // 3
        q = (r - 4 - 5 * parity) // 3
        r = (2 * q + parity) % next_modulus
        modulus = next_modulus
    return r == 0


def self_test() -> None:
    for n in range(13):
        modulus = 3**n
        outputs = {g_iter(n, x) % modulus for x in range(2**n)}
        accepted = {r for r in range(modulus) if in_output_residues(n, r)}
        assert outputs == accepted, n
        assert len(outputs) == 2**n, n
        print(f"n={n:2d}  output classes={len(outputs):6d}  modulo={modulus:7d}  verified")

    for n in (20, 40, 100):
        for x in (0, 1, 2, (1 << n) - 1, 2**n + 1234567):
            assert in_output_residues(n, g_iter(n, x))
        print(f"n={n:3d}  large-output consistency passed")


if __name__ == "__main__":
    self_test()
