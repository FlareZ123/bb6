"""Independent arithmetic regression for the true-blank D six-state episode eight.

This reproduces the previously source-proven DRegular eleven-case arithmetic
and established exceptional return formulas. It is NUMERICAL evidence, not a
Lean kernel proof or a full nonhalting proof. Run as Python 3.11+ script.
"""
from dataclasses import dataclass
from hashlib import sha256


@dataclass(frozen=True)
class L:
    a: int
    q: int = 0
    b: int = 0


def next_regular(s: L) -> L | None:
    a, q, b = s.a, s.q, s.b
    if a % 3 == 2:
        k = (a - 2) // 3
        if q == 0:
            return L(8 * k + 9)
        if q == 1:
            return L(8 * k + 10 + b)
        return L(8 * k + 10, q - 1, b)
    if a % 3 == 0:
        k = (a - 3) // 3
        if q == 0:
            return L(8 * k + 11)
        d = q - 1 + 4 * ((b + 1) // 3)
        if (b + 1) % 3 == 0:
            return L(8 * k + 11 + 2 * d)
        if (b + 1) % 3 == 1:
            return L(8 * k + 13 + 2 * d)
        return L(8 * k + 7 + 2 * d, 1, 5)
    k = (a - 4) // 3
    if q == 0:
        return L(8 * k + 5, 1, 5)
    if b == 0:
        return L(8 * k + 5, 1, 2 * q + 5)
    if b == 1:
        return None
    if b == 2:
        return L(8 * k + 9, q + 1)
    return L(8 * k + 9, q + 2, b - 3)


def second_of_exception(s: L) -> L | None:
    assert s.a % 3 == 1 and s.q >= 1 and s.b == 1
    k = (s.a - 4) // 3
    t, residue = divmod(k, 3)
    q = s.q
    if q == 1:
        return (L(64 * t + 27) if residue == 0 else
                L(64 * t + 37, 3) if residue == 1 else
                L(64 * t + 49, 6))
    if residue == 0:
        return L(64 * t + 17 + 2 * q, 1, 5)
    if residue == 1:
        return L(64 * t + 33, 4, 5) if q == 2 else None
    u, rem = divmod(2 * q, 3)
    if rem == 0:
        return L(64 * t + 65 + 8 * u)
    if rem == 1:
        return L(64 * t + 77 + 8 * u)
    return L(64 * t + 59 + 8 * u, 3, 2)


def fingerprint(n: int) -> str:
    return sha256(n.to_bytes((n.bit_length() + 7) // 8, "little")).hexdigest()


def advance(s: L, count: int) -> L:
    for step in range(count):
        new = next_regular(s)
        assert new is not None, f"unexpected regular-language exit at step {step}"
        s = new
    return s


def find_exception(s: L, index: int) -> tuple[int, L]:
    while True:
        nxt = next_regular(s)
        if nxt is None:
            return index, s
        s = nxt
        index += 1


def main() -> None:
    state = L(9)
    index = 0
    first_six_indexes = [8394, 9422, 12089, 23037, 27291, 31787]
    for episode, expected_index in enumerate(first_six_indexes, start=1):
        index, state = find_exception(state, index)
        assert index == expected_index, (episode, index, expected_index)
        print(f"Episode {episode}: section {index}, a_bits={state.a.bit_length()}, "
              f"(a mod 81,q,b)={(state.a % 81,state.q,state.b)}")
        if episode < 6:
            successor = second_of_exception(state)
            assert successor is not None
            state = successor
            index += 2

    assert state.q == 4 and state.b == 1 and state.a % 243 == 214
    t6 = (state.a - 7) // 9
    assert t6 % 27 == 23
    w6 = t6 // 27
    state = L(32768 * w6 + 28577, 3, 2)
    index += 5
    print(f"Sixth reentry after five designated exceptional steps: section {index}")

    state = advance(state, 34)
    index += 34
    assert (state.a % 9, state.q, state.b) == (4, 3, 1)
    t7 = (state.a - 4) // 9
    print(f"Seventh exceptional input: section {index}, a_bits={state.a.bit_length()}")
    state = L(64 * t7 + 23, 1, 5)
    index += 2

    state = advance(state, 6046)
    index += 6046
    assert (state.a % 9, state.q, state.b) == (1, 3, 1)
    assert state.a.bit_length() == 53597 and state.a % 81 == 19
    assert fingerprint(state.a) == (
        "dca8fef2d5858a9a53065a3dd9d73a068bceb4d4df0a0ede58eeceed341ef952")
    t8 = (state.a - 10) // 9
    print(f"Eighth exceptional input: section {index}, "
          f"a_bits={state.a.bit_length()}, a_mod81={state.a % 81}, "
          f"a_SHA256_little_endian={fingerprint(state.a)}")
    state = L(64 * t8 + 81)
    index += 2
    print(f"Eighth E/A pure-unary reentry: section {index}, a_bits={state.a.bit_length()}")

    state = advance(state, 6090)
    index += 6090
    assert (state.a % 9, state.q, state.b) == (4, 9, 1)
    assert state.a.bit_length() == 62217
    print(f"Ninth E/B candidate (NOT source-certified by this test): section {index}, "
          f"a_bits={state.a.bit_length()}, a_mod243={state.a % 243}")
    print("PASS: independent exact-integer arithmetic checks for eighth episode")


if __name__ == "__main__":
    main()
