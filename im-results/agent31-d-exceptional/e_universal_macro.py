"""D E-sector universal first-event interpreter, 2026-11-06.

Mathematical basis: finite right-window E3 marker-safety certificate and the
inductive C/D sweep, detailed in E-universal-first-event-cocycle.md.
For a synthetic source F/0 tape I_(3k+4)(0Y), simulate only the short m=3
E boundary. If that E3 first event finishes, lift its exact primitive time
and physical output for arbitrary k without touching the huge unary prefix.
Does not decide whether every possible finite Y has an event.
"""
from dataclasses import dataclass
from cylinder_first_event import RULE


@dataclass(frozen=True)
class First:
    kind: str  # "halt" = F/1 encountered; "return" = physically blank-left F/0
    steps: int
    right: str | None


def first_event(state: int, left_nearest: list[int], right: str,
                cap: int = 1000000) -> First | None:
    ones = {-i - 1 for i, bit in enumerate(left_nearest) if bit}
    ones.update(i + 1 for i, bit in enumerate(right) if bit == "1")
    head = 0
    for t in range(cap):
        bit = int(head in ones)
        if state == 5:
            if bit:
                return First("halt", t, None)
            if t > 0 and not any(j < head for j in ones):
                last = max(ones, default=head)
                word = "".join(
                    "1" if j in ones else "0" for j in range(head + 1, last + 1)
                )
                return First("return", t, word)
        write, direction, state = RULE[(state, bit)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    return None  # Event not established within the explicit computation cap.


def base_e(word: str, cap: int = 1000000) -> First | None:
    if any(c not in "01" for c in word):
        raise ValueError("right word must be binary")
    return first_event(4, [0, 0, 1, 0, 1, 0, 1, 0, 1, 1], word, cap)


def lifted_e(k: int, word: str, cap: int = 1000000) -> First | None:
    """First physical event from I_(3k+4)(0word), if E3 computation finishes.

    A return supplies the complete physical right word, right of scanned 0.
    A halt time counts defined transitions before F/1; source frozen state
    enters at the next step. Never infer blank-root reachability from this.
    """
    if k < 0:
        raise ValueError("k must be nonnegative")
    event = base_e(word, cap)
    if event is None:
        return None
    prefix_time = 12 * k * k + 41 * k + 33
    if event.kind == "halt":
        return First("halt", prefix_time + event.steps, None)
    return First("return", prefix_time + event.steps + 8 * k,
                 "1" * (8 * k) + event.right)


def regression() -> None:
    tested = 0
    for size in range(11):
        for x in range(1 << size):
            word = format(x, f"0{size}b") if size else ""
            for k in range(5):
                expected = lifted_e(k, word)
                raw = first_event(5, [], "1" * (3 * k + 4) + "0" + word)
                if expected != raw:
                    raise AssertionError((k, word, expected, raw))
                tested += 1
    print(f"PASS: {tested} exact raw-tape first-event regressions")


if __name__ == "__main__":
    regression()
