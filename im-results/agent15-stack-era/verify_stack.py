"""Reproducible raw-vs-macro check for the BB(6) 1RB1LA_1RC0RF cryptid.

The macro rules are a transcription of the BusyBeaverWiki macro table (2026-05-10).
This is a computational regression check, not a proof of nonhalting.
"""
from collections import Counter

RLE = "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF"

# The first 50 independent published era boundaries (primitive step, L, cursor, R).
# The complete list is printed by the simulator; these checkpoints test orientation.
CHECKPOINTS = {
    0: (43, (1,), 4, (1,)),
    1: (120, (1,), 10, (1,)),
    2: (567, (12, 6), 5, (1,)),
    3: (1881, (19, 2, 7), 9, (1,)),
    11: (42995, (20, 94, 18), 5, (1,)),
    12: (69570, (120,), 41, (1,)),
    13: (149943, (87, 11, 16), 93, (1,)),
    49: (9522575, (218, 572), 101, (1,)),
}


def bump(stack):
    """Increment head run, creating a one-run for an absent neighbor."""
    return (stack[0] + 1, *stack[1:]) if stack else (1,)


def macro_next(left, cursor, right):
    """Return (next left, cursor, right, primitive time, rule) or fail."""
    if cursor >= 3:
        return bump(left), cursor - 2, bump(right), 2 * cursor + 7, "Sweep"
    if cursor == 2:
        return bump(left), 0, bump(right), 11, "SweepE"
    if cursor == 1:
        if not left:
            raise AssertionError("Unsupported cursor-one source")
        return left[1:], left[0], (1, *right), 6, "Shift"
    if not left or not right:
        raise AssertionError("Unsupported zero-cursor source")
    a, tail = left[0], left[1:]
    r = right[0]
    if r == 1:
        if len(right) > 1:
            raise AssertionError("Halting macro configuration reached")
        return tail, a + 5, (), 8, "EraDone"
    if r == 2:
        return tail, a + 3, bump(right[1:]), 8, "Two"
    if len(right) == 1:
        if r == 3:
            return (a + 4, *tail), 0, (1,), 12, "BounceE"
        return (a + 4, *tail), r - 3, (1,), r + 9, "Bounce"
    mids, z = right[1:-1], right[-1]
    new_left = (*reversed(mids), r - 2, a + 4, *tail)
    primitive_time = r + 3 * len(mids) + sum(mids) + (13 if z == 1 else z + 12)
    if z == 1:
        return new_left, 0, (1,), primitive_time, "MultiNE"
    return new_left, z - 1, (1,), primitive_time, "MultiN"


def expected_tape(left, cursor, right):
    """Occupied cells relative to the A-head at the macro boundary."""
    occupied = set()
    if cursor:
        occupied.update(range(1 - cursor, 1))
        loc = -cursor - 1
    else:
        loc = -1
    for a in left:
        occupied.update(range(loc - a + 1, loc + 1))
        loc -= a + 1
    loc = 3
    for a in right:
        occupied.update(range(loc, loc + a))
        loc += a + 1
    return occupied


def generate_macro(eras=50):
    """Yield (raw time, L, c, R, rule), including the initial checkpoint."""
    clock, left, cursor, right = 43, (1,), 4, (1,)
    yield clock, left, cursor, right, "Init"
    recorded = 1
    era_done = False
    while recorded < eras:
        left, cursor, right, elapsed, rule = macro_next(left, cursor, right)
        clock += elapsed
        yield clock, left, cursor, right, rule
        if era_done:
            assert right == (1,) and cursor >= 4 and left
            recorded += 1
            era_done = False
        if rule == "EraDone":
            era_done = True


def parse_machine():
    result = {}
    for state, pair in zip("ABCDEF", RLE.split("_")):
        for symbol in range(2):
            instruction = pair[3 * symbol : 3 * symbol + 3]
            if instruction == "---":
                result[state, symbol] = None
            else:
                result[state, symbol] = (
                    int(instruction[0]),
                    1 if instruction[1] == "R" else -1,
                    instruction[2],
                )
    return result


def verify(eras=50, raw_limit=100000):
    records = list(generate_macro(eras))
    points = [(t, l, c, r) for t, l, c, r, rule in records if rule == "Init" or (r == (1,) and c >= 4 and l and rule == "Sweep")]
    # The only solo-to-era Sweep has a predecessor with empty right stack;
    # using every candidate Sweep in this filter can include within-era states.
    eras_seen = [(records[0][0], records[0][1], records[0][2], records[0][3])]
    for i, rec in enumerate(records[1:], start=1):
        if records[i - 1][4] == "EraDone":
            eras_seen.append(rec[:4])
    assert len(eras_seen) == eras
    for n, expected in CHECKPOINTS.items():
        assert eras_seen[n] == expected, (n, eras_seen[n], expected)

    boundaries = {rec[0]: rec[1:4] for rec in records if rec[0] <= raw_limit}
    machine = parse_machine()
    state, head, tape = "A", 0, set()
    checks = 0
    for step in range(raw_limit + 1):
        if step in boundaries:
            assert state == "A", (step, state)
            left, cursor, right = boundaries[step]
            actual = {p - head for p in tape}
            assert actual == expected_tape(left, cursor, right), (step, left, cursor, right)
            checks += 1
        if step == raw_limit:
            break
        instr = machine[state, int(head in tape)]
        assert instr is not None, ("Unexpected primitive halt", step)
        write, direction, state = instr
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
    assert checks == len(boundaries)
    return {
        "machine": RLE,
        "macro_boundaries": len(records),
        "published_era_checkpoints": len(CHECKPOINTS),
        "eras": len(eras_seen),
        "last_era": eras_seen[-1],
        "raw_steps": raw_limit,
        "raw_vs_macro_exact_matches": checks,
        "last_raw_ones": len(tape),
    }


if __name__ == "__main__":
    print(verify())
