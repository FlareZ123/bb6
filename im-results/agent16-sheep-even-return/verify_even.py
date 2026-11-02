"""Independent exact finite consistency tests for the Sheep even-to-even map."""


def step(t: int) -> int | None:
    assert t >= 5
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    return t + a + (u - 1) // 2


def next_even(t: int) -> int | None:
    assert t >= 5
    z = step(t)
    if z is None:
        return None
    x = z - 1
    h = (x & -x).bit_length() - 1
    return 1 + pow(3, h) * (x >> h)


def direct_next_even(t: int) -> tuple[int | None, int]:
    z = step(t)
    if z is None:
        return None, 0
    count = 1
    while z % 2:
        z1 = step(z)
        assert z1 is not None
        z = z1
        count += 1
    return z, count


def run() -> None:
    for t in range(5, 20001):
        computed = next_even(t)
        direct, count = direct_next_even(t)
        assert computed == direct, (t, computed, direct)
        assert computed is None or (computed % 2 == 0 and computed > t)
    print("PASS: 19,996 first-even finite identities, including all branches")

    t = 10
    for i in range(2000):
        assert t % 2 == 0
        z = next_even(t)
        direct, count = direct_next_even(t)
        assert z == direct and z is not None, (i, t)
        t = z
    print("PASS: 2,000 consecutive real even-to-even returns from t=10")
    print("Final even-state bit length:", t.bit_length())


if __name__ == "__main__":
    run()
