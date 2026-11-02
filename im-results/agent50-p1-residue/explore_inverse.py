"""Exploratory finite P1 inverse-branch sieve. No nonhalting conclusion.

The original P1 accelerated map, generic G inverse completeness and
Reach restrictions are formally established in the repository. This
script samples finite trees; truncation is reported as unresolved.
"""

def g_inverses(b: int, d: int) -> list[tuple[int, int]]:
    if b <= 0 or b % 4:
        return []
    k = b // 4 - 1
    v = d + 2 * k + 2
    out = []
    while True:
        out.append((k, v))
        if v < 3 or v % 2 == 0:
            return out
        v = (v - 3) // 2
        k += v // 2 + 1  # IMPORTANT: use NEW inverse v, not old v


def power_of_two_after_div14(value: int) -> bool:
    if value < 14 or value % 14:
        return False
    q = value // 14
    return q & (q - 1) == 0


def finite_inverse_sieve(n: int, depth: int = 3) -> tuple[int, int]:
    target = 14 * (1 << n) - 2 * n - 16
    stack = [(target, 3, 0)]
    leaves = 0
    unresolved = 0
    while stack:
        b, d, level = stack.pop()
        if level > depth:
            leaves += 1
            unresolved += 1
            continue
        candidates = g_inverses(b, d)
        if not candidates:
            leaves += 1
            unresolved += 1
            continue
        for k, v in candidates:
            if v < 2 or k < 2:
                leaves += 1
                unresolved += 1
                continue
            x, y = 2 * k - 4, v + 4
            if y % 2 == 0:
                if power_of_two_after_div14(x + 12):
                    stack.append((x, y, level + 1))
                else:
                    leaves += 1
            elif x == 2 or x % 4 == 0:
                stack.append((x, y, level + 1))
            else:
                leaves += 1
    return leaves, unresolved


if __name__ == "__main__":
    for residue in (2, 18, 34, 50):
        numbers = [n for n in range(residue, 500, 64) if n >= 6]
        print("n mod 64 =", residue)
        for n in numbers:
            leaves, unresolved = finite_inverse_sieve(n)
            print(f"  n={n}: leaves={leaves}, truncated_or_unresolved={unresolved}")
