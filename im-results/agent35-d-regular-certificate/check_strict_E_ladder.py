"""Independent primitive first-physical-F/0 audit for the parameterized E ladder."""
from primitive import TM


def audit(m: int, u: int, r: int) -> tuple[int, list[int]]:
    n = 3 ** (m + 1) * u + 1
    suffix = [0, 1] * r + [0] + [1] * (3 * m + 3) + [0] + [1] * 6
    tape = {i + 1 for i, v in enumerate([1] * n + suffix) if v}
    head = 0
    state = 5
    expected = []
    total = 0

    for j in range(m):
        k = 8 ** j * 3 ** (m - j) * u - 1
        total += 12 * k * k + 49 * k + 58 + 6 * (r + 2 * j)
        expected.append(total)

    events = []
    for t in range(1, total + 1):
        bit = int(head in tape)
        instr = TM.get((state, bit))
        if instr is None:
            raise AssertionError(("HALTED", m, u, r, t))
        write, direction, state = instr
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
        if state == 5 and head not in tape and (not tape or min(tape) > head):
            events.append(t)

    if events != expected:
        raise AssertionError(
            ("EXTRA_OR_MISSING", m, u, r, len(events), len(expected),
             events[:15], expected[:15])
        )
    return len(events), events


if __name__ == "__main__":
    cases = 0
    for m in range(4):
        for u in range(1, 4):
            for r in range(3):
                audit(m, u, r)
                cases += 1
        print("strictly verified depth", m, "cases", cases, flush=True)
    print("PASS", cases, "strict physical F0 checks")
