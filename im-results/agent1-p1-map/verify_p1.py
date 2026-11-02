"""Independent small-step/macro check of a published BB(6) reduction.

Not a nonhalting proof.
Source: google-deepmind/cryptids, BusyBeaver/BB6/
M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean
"""
MACHINE = "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"


def g(k: int, c: int) -> tuple[int, int]:
    while True:
        if c >= 2*k:
            if c <= 2*k + 1:
                return 0, 2*c + 3
            return 4*k + 4, c - 2*k - 2
        k, c = k - c//2 - 1, 2*c + 3


def next_hub(a: int, c: int) -> tuple[int, int] | None:
    if c == 0:
        return 2, a + 1
    if c == 1:
        return a + 2, 0
    if a % 2 == 0:
        return a + 3, c - 2
    if c == 2:
        return None
    if c == 3:
        return g(a//2, 1)
    return g(a//2 + 1, c - 2)


class RawMachine:
    def __init__(self):
        triples = [block[i:i+3] for block in MACHINE.split("_")
                   for i in (0, 3)]
        self.rules = [
            None if s == "---" else (int(s[0]), 1 if s[1] == "R" else -1,
                                       ord(s[2])-ord("A"))
            for s in triples
        ]
        self.state = self.head = self.steps = 0
        self.ones: set[int] = set()

    def tick(self) -> bool:
        rule = self.rules[2*self.state + int(self.head in self.ones)]
        if rule is None:
            return False
        write, move, state = rule
        if write:
            self.ones.add(self.head)
        else:
            self.ones.discard(self.head)
        self.head += move
        self.state = state
        self.steps += 1
        return True

    def hub(self) -> tuple[int, int] | None:
        if self.state != 0:
            return None
        a = 0
        while self.head - a - 1 in self.ones:
            a += 1
        c = 0
        while self.head + c in self.ones:
            c += 1
        return (a, c) if a+c == len(self.ones) else None


def verify(hubs: int = 100, per_hub_limit: int = 1_000_000) -> int:
    raw = RawMachine()
    for i in range(hubs):
        source = raw.hub()
        assert source is not None, (i, "expected P1")
        expected = next_hub(*source)
        for _ in range(per_hub_limit):
            if not raw.tick():
                assert expected is None, (i, source, "unexpected halt")
                break
            actual = raw.hub()
            if actual is not None:
                assert actual == expected, (i, source, expected, actual)
                break
        else:
            raise RuntimeError(("timeout in hub", i, source))
    return raw.steps


def explore(n: int = 100_000) -> tuple[int, int]:
    a, c = 2, 1
    for i in range(n):
        nxt = next_hub(a, c)
        assert nxt is not None, ("accelerated halt", i, a, c)
        a, c = nxt
    return a, c


if __name__ == "__main__":
    count = 100
    print("100 hub transitions agree with direct TM;",
          verify(count), "ordinary steps")
    print("After 100000 accelerated steps from (2,1):", explore())
