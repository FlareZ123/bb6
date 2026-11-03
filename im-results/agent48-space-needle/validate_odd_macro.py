"""Rooted Space Needle odd-run macro cross-check and high-level call audit."""
from collections import Counter
import hashlib


def high_next(d: int) -> int | None:
    """Exact high-level successor from the pinned source-derived formula."""
    x = d + 2
    v = (x & -x).bit_length() - 1
    u = x >> v
    if u == 1:
        return None
    return d + v + 3 * ((u - 1) // 2)


def macro_next(d: int) -> tuple[int | None, int]:
    """Collapse an odd-counter block, or take one even-counter step."""
    if d % 2 == 0:
        return high_next(d), 1
    x = d + 1
    t = (x & -x).bit_length() - 1
    assert t >= 1
    m = x >> t
    assert m % 2 == 1
    return (5**t) * m - 1, t


def main() -> None:
    digest = hashlib.sha256()
    raw = 0
    macro = 0
    d = 1
    blocks = Counter()
    limit = 100000
    while raw < limit:
        e, t = macro_next(d)
        if e is None:
            print("Observed a terminal counter at high-level index", raw)
            return
        actual = d
        for _ in range(t):
            actual = high_next(actual)
            assert actual is not None
        assert actual == e
        raw += t
        macro += 1
        if t > 1:
            blocks[t] += 1
        digest.update(f"{raw},{macro},{t},{d.bit_length()},{e.bit_length()},{e & ((1<<64)-1)}\n".encode())
        d = e
    assert raw == 100000
    assert macro == 75221
    assert d.bit_length() == 93880
    assert digest.hexdigest() == "652153a408f55ea94900411554a7d1be4ff1dea351c54abb8e3e285b02476dd2"
    print("Rooted high-level calls:", raw)
    print("Odd-run macro calls:", macro)
    print("Exact high-level call reduction fraction:", f"{(raw-macro)/raw:.6f}")
    print("Longest odd block length:", max(blocks))
    print("Odd blocks of length>1:", sorted(blocks.items()))
    print("Last counter bit length:", d.bit_length())
    print("SHA256 macro checkpoints:", digest.hexdigest())


if __name__ == "__main__":
    main()
