"""Independent exact-integer falsification of universal even-section gateway claims."""

from __future__ import annotations

import hashlib


def section(t: int) -> int | None:
    assert t >= 5
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    assert u >= 5 and u % 2 == 1
    return t + a + (u - 1) // 2


def even_return(t: int) -> int | None:
    assert t % 2 == 0 and t >= 6
    z = section(t)
    if z is None:
        return None
    v = z - 1
    h = (v & -v).bit_length() - 1
    w = v >> h
    assert w % 2 == 1
    return 1 + 3**h * w


def is_power_two(x: int) -> bool:
    return x > 0 and x & (x - 1) == 0


def main() -> None:
    hits: list[tuple[int, int]] = []
    odd_e_hits: list[tuple[int, int]] = []
    for x in range(6, 400_001, 2):
        y = section(x)
        if y is not None and is_power_two(y):
            j = y.bit_length() - 1
            assert j >= 7 and j % 4 == 3
            assert (x // 2) % 2 == 1 and x // 2 >= 5
            assert 5*(x//2)+1 == 2**(j+1)
            hits.append((x, j))
        e = even_return(x)
        if e is not None and is_power_two(e) and (e.bit_length() - 1) % 2 == 1:
            j = e.bit_length() - 1
            assert j >= 7 and j % 4 == 3
            assert e == y
            odd_e_hits.append((x, j))

    assert hits == [(102, 7), (1638, 11), (26214, 15)]
    assert odd_e_hits == hits

    u = 3
    witness_digest = hashlib.sha256()
    for k in range(1, 101):
        u = 16*u+3
        x = 2*u
        j = 4*k+3
        assert u % 2 == 1 and u >= 5
        assert 5*u+1 == 2**(j+1)
        assert section(x) == 2**j
        assert even_return(x) == 2**j
        witness_digest.update(f"{k}:{x}:{j}\n".encode())

    print("PASS exact 199998 even-section inputs 6..400000")
    print("Direct section power hits:", hits)
    print("Odd-exponent first-even power hits:", odd_e_hits)
    print("PASS exact 100 constructive witnesses, through exponent j=403")
    print("SHA256 witness ledger:", witness_digest.hexdigest())


if __name__ == "__main__":
    main()
