"""Literal RLE independent regression of the ten-left-cell nonblank halter.

Uses the 11 raw transitions parsed by check_right_projection.py.
This synthetic input differs from the fully blank tape; no blank-halt claim.
"""
from check_right_projection import table

INITIAL_INTEGER = 1320 << 8
tape = {-i for i in range(1, INITIAL_INTEGER.bit_length() + 1)
        if (INITIAL_INTEGER >> i) & 1}
assert all(-i not in tape for i in range(1, 11))
state = position = 0
for t in range(598):
    if t == 596:
        assert state == 0 and position not in tape
        assert position + 1 in tape and position + 2 in tape
        print("PASS: exact A0/right11 halting guard at primitive time 596")
    action = table.get((state, int(position in tape)))
    assert action is not None, ("unexpected earlier halt", t)
    write, direction, state = action
    (tape.add if write else tape.discard)(position)
    position += direction
assert state == 5 and position in tape
assert (5, 1) not in table
print("PASS: F/1 halting after exactly 598 primitive transitions")
