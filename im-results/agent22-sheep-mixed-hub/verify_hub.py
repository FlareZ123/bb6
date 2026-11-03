"""Independent exact arithmetic regression for Sheep's synthetic 2^p*q hub."""

def v2(n: int) -> int:
    return (n & -n).bit_length() - 1


def sheep_f(t: int) -> int | None:
    a = v2(t)
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    return t + a + (u - 1) // 2


def sheep_even(t: int) -> int | None:
    z = sheep_f(t)
    if z is None:
        return None
    h = v2(z - 1)
    return 1 + pow(3, h) * ((z - 1) >> h)


def witness(p: int, q: int, s: int) -> tuple[int, int]:
    m = (1 << p) * q
    u = 5 * q
    c = (u - 1) // 2
    L = p + c + 1
    b = s + m * L - (p + c)
    a = p + b
    x = (1 << a) * u
    y = x + a + c
    return x, y


def main() -> None:
    count = 0
    maxbits = 0
    for p in range(1, 7):
        for q in range(1, 26, 2):
            m = (1 << p) * q
            for s in range(0, m, 2):
                x, y = witness(p, q, s)
                assert x % m == 0 and y % m == s
                assert x % 2 == 0 and y % 2 == 0
                assert sheep_f(x) == y and sheep_even(x) == y
                assert v2(x) >= p
                count += 1
                maxbits = max(maxbits, x.bit_length())
    print(f"PASS: {count} constructed exact section/first-even edges; max source bits {maxbits}")


if __name__ == "__main__":
    main()
