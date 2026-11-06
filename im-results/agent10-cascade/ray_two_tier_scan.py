"""Finite inverse-grammar coverage scan for #746 high-margin ray gates.

The Lean source checks, not this script, prove the universal root
exclusions. The counts are of algebraic candidates, not true rooted visits.
"""
from collections import Counter
from hashlib import sha256


def scan(last_n: int = 1500) -> None:
    first = Counter()
    third = Counter()
    digest = sha256()
    for n in range(20, last_n + 1):
        if n % 6 not in (4, 5):
            continue
        p = 1 << n
        deficit = n + 4
        j = 0
        while 2048 * deficit + 16384 * n + 16384 <= p:
            z = 8 * p - 2 * deficit + 5
            if z % 9 == 0:
                d = z // 9
                k = n - 2
                s = 1 << k
                if 6 * s + 1 <= 2 * d <= 8 * s - 1:
                    h = 4 * d - 8 * s - k - 5
                    w = 2 * h - 2 * p - k
                    assert h >= 0 and w >= 0 and d % 2 == 1
                    assert 9 * h + 8 * deficit + 9 * n + 7 == 14 * p
                    assert p < w and 8 * w + 32 < 9 * p
                    h27 = (2 * h + 5) % 27 == 0
                    w27 = (2 * w + 5) % 27 == 0
                    assert not (h27 and w27)
                    if h27:
                        label = "first_level_27_gate"
                    elif w27:
                        label = "second_level_27_gate"
                    elif h % 3 != 0 or (2 * w + 5) % 9 != 0:
                        label = "excluded_first_level"
                    else:
                        label = "excluded_second_level"
                    first[label] += 1
                    digest.update(f"{n},{j},1,{label}\n".encode())
            if z % 81 == 0:
                d = z // 81
                k = n - 3
                s = 1 << k
                if 6 * s + 1 <= 8 * d <= 8 * s - 1:
                    h = 16 * d - p - n - 2
                    assert h > 0 and d % 2 == 1
                    assert 81 * h + 32 * deficit + 81 * n + 82 == 47 * p
                    assert (1 << (n - 1)) < h
                    assert 2 * h + 2 < 3 * (1 << (n - 1))
                    third[h % 3] += 1
                    digest.update(f"{n},{j},3,{h % 3}\n".encode())
            deficit = 2 * deficit + n - 1
            j += 1

    first_total = sum(first.values())
    excluded = first["excluded_first_level"] + first["excluded_second_level"]
    print(f"Strong-margin synthetic pairs, n=20..{last_n} with n mod6=4/5")
    print(f"t=1: {first_total} pairs; {excluded} meet proved root-exclusion gates")
    print(f"t=1 classes: {dict(sorted(first.items()))}")
    print(f"t=3: {sum(third.values())} pairs; {third[0]+third[1]} wrong-mod3 parents")
    print(f"t=3 classes: {dict(sorted(third.items()))}")
    print(f"SHA256: {digest.hexdigest()}")
    print("Finite synthetic counts imply no machine halt or density theorem.")


if __name__ == "__main__":
    scan()
