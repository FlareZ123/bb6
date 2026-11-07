"""Independent literal-RLE physical execution check for the #623 frontier witness.

Run with Python 3. No accelerator, root heuristic or sparse control
approximation is involved. The first 96 raw blank-tape moves are checked.
"""
from collections import defaultdict

RLE = "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA"
ROWS = RLE.split("_")
assert len(ROWS) == 6 and all(len(row) == 6 for row in ROWS)

table = {}
for state, row in enumerate(ROWS):
    for scanned in (0, 1):
        action = row[3 * scanned:3 * scanned + 3]
        if action != "---":
            assert action[0] in "01" and action[1] in "LR"
            assert action[2] in "ABCDEF"
            table[state, scanned] = (
                int(action[0]),
                1 if action[1] == "R" else -1,
                ord(action[2]) - ord("A"),
            )

expected_slots = [
    (0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (2, 1),
    (1, 1), (0, 1), (4, 1), (4, 0), (5, 1),
]
expected_times = [0, 1, 2, 3, 6, 9, 11, 13, 14, 52, 53]

tape = defaultdict(int)
state, head = 0, 0
seen = {}
for time in range(96):
    slot = state, tape[head]
    if slot not in seen:
        seen[slot] = time
    assert slot in table, f"Premature halt at move {time} on {slot}"
    value, direction, state = table[slot]
    tape[head] = value
    head += direction

assert len(table) == 11
assert list(seen) == expected_slots
assert list(seen.values()) == expected_times
assert (5, 0) not in seen
print("PASS: literal #623 blank tape follows 96 successful primitive moves.")
for slot, time in seen.items():
    print(f"first read {slot} at move {time}")
print("F/0 remains unseen; no halting/nonhalting decision follows.")
