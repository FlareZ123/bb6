#!/usr/bin/env python3
"""Independent exact-count checks for Agent 9's S-section first-passage law.

No external packages. The output concerns synthetic section starts and does
not classify either designated six-state blank-tape machine.
"""
from fractions import Fraction
from itertools import product
from math import comb


def formula(height: int, time: int) -> int:
    """Number of first exits among all 3**time symbolic residue words."""
    k = height + 1
    if time < k:
        return 0
    unrestricted = 0
    for b in range((time - k) // 7 + 1):
        if (time - k - 7 * b) % 5:
            continue
        a = (time - k - 7 * b) // 5
        unrestricted += comb(time, a) * comb(time - a, b)
    numerator = k * unrestricted
    assert numerator % time == 0
    return numerator // time


def dynamic_counts(height: int, horizon: int) -> list[int]:
    """Independent positive-queue recurrence, with already-exited paths removed."""
    alive = {height: 1}
    result = []
    for _ in range(horizon):
        next_alive = {}
        exit_count = 0
        for level, count in alive.items():
            if level == 0:
                exit_count += count
            else:
                next_alive[level - 1] = next_alive.get(level - 1, 0) + count
            next_alive[level + 4] = next_alive.get(level + 4, 0) + count
            next_alive[level + 6] = next_alive.get(level + 6, 0) + count
        result.append(exit_count)
        alive = next_alive
    return result


def brute_count(height: int, time: int) -> int:
    """Fully independent length-time ternary-word enumerator."""
    total = 0
    for word in product((0, 1, 2), repeat=time):
        level = height
        for t, digit in enumerate(word, 1):
            if digit == 0:
                if level == 0:
                    total += (t == time)
                    break
                level -= 1
            elif digit == 1:
                level += 4
            else:
                level += 6
    return total


def word_for_integer(q: int, length: int) -> tuple[int, ...]:
    """Actual positive-integer q arithmetic, ignoring c until first transfer."""
    word = []
    for _ in range(length):
        k, digit = divmod(q, 3)
        word.append(digit)
        q = (4 * k if digit == 0 else 4 * k - 3 if digit == 1 else 4 * k + 1)
        assert q >= 16
    return tuple(word)


def check() -> None:
    for h in (0, 1, 3, 8):
        dynamic = dynamic_counts(h, 160)
        for n, observed in enumerate(dynamic, 1):
            assert observed == formula(h, n), (h, n, observed, formula(h, n))
        for n in range(1, 10):
            assert brute_count(h, n) == formula(h, n), (h, n)
        print(f"height {h}: exact formula = DP to time 160, brute force to time 9")

    tilt = Fraction(15, 22)
    decay = (1 + tilt**5 + tilt**7) / (3 * tilt)
    assert decay == Fraction(3032754763, 5102095680)
    for h in (0, 1, 3, 8):
        k = h + 1
        for n in range(k, 161):
            assert Fraction(formula(h, n), 3**n) <= Fraction(k, n) * tilt**k * decay**n
    print("all-time rational 1/n Chernoff bound checked over n<=160")

    for n in range(1, 8):
        modulus = 3**n
        distinct = {word_for_integer(r + 10 * modulus, n) for r in range(modulus)}
        assert len(distinct) == modulus
    print("integer q mod 3**n -> digit-word bijection checked to n=7")

    def poly(x: Fraction) -> Fraction:
        return 1 + x**5 + x**7 - 3*x

    low = Fraction(334894995, 10**9)
    high = Fraction(334894996, 10**9)
    assert poly(low) > 0 > poly(high)
    print("nontrivial extinction root in (334894995/10**9, 334894996/10**9)")
    print("S initial height 3: first-transfer probability in",
          (float(low**4), float(high**4)))
    print("all checks passed")


if __name__ == "__main__":
    check()
