"""Reconstruct a genuine Sheep blank-section prefix through v2=17.

Every even-return edge is verified by two exact implementations:
a closed odd-block expression and direct iteration of the original
published F return formula. This is a finite check, not nonhalting.
"""
import hashlib

N = 65924
EXPECTED_SHA256 = "3313b753edcd2584a561fee50f67b1aa7db7f58be804c67600205aa9867e6b37"


def v2(x):
    assert x > 0
    return (x & -x).bit_length() - 1


def F(x):
    a = v2(x)
    u = x >> a
    if u == 1:
        return None
    return x + a + (3 if u == 3 else (u - 1) // 2)


def first_even_closed(x):
    z = F(x)
    assert z is not None
    w = z - 1
    h = v2(w)
    return 1 + pow(3, h) * (w >> h), h + 1


def first_even_direct(x):
    z = F(x)
    assert z is not None
    n = 1
    while z % 2:
        z = F(z)
        assert z is not None
        n += 1
    return z, n


def main():
    x = 10
    max_v = 0
    firsts = []
    for i in range(N + 1):
        a = v2(x)
        if a > max_v:
            max_v = a
            firsts.append((i, a))
        if i < N:
            y, n = first_even_closed(x)
            direct_y, direct_n = first_even_direct(x)
            assert (y, n) == (direct_y, direct_n)
            assert y > x and y % 2 == 0
            x = y

    byte_length = (x.bit_length() + 7) // 8
    digest = hashlib.sha256(x.to_bytes(byte_length, "big")).hexdigest()
    assert v2(x) == 17
    assert x.bit_length() == 52736
    assert x % 1000000007 == 269057283
    assert digest == EXPECTED_SHA256
    assert firsts[-1] == (N, 17)

    print("PASS: exact section-entry 10,", N, "full even returns")
    print("PASS: every compressed edge equals independently iterated F returns")
    print("first-record indices and valuations:", firsts)
    print("final state v2:", v2(x), "bit length:", x.bit_length(),
          "SHA256:", digest)
    print("Scope: verified finite section prefix only; no BB6 decision")


if __name__ == "__main__":
    main()
