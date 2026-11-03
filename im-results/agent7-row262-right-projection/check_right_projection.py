"""Independent literal-RLE test of eight first-A-return right-projection edges.

This finite original-TM audit reproduces the Lean certificate's eight concrete
witnesses. It does not simulate a single blank-tape orbit across these edges:
each witness deliberately specifies a fresh, arbitrary left-tape context.
"""

MACHINE = "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---"
rows = MACHINE.split("_")
assert len(rows) == 6 and all(len(row) == 6 for row in rows)
table = {}
for state, row in enumerate(rows):
    for read in (0, 1):
        entry = row[read * 3 : (read + 1) * 3]
        if entry != "---":
            write, direction, target = entry
            table[state, read] = (int(write), 1 if direction == "R" else -1, ord(target) - ord("A"))
assert len(table) == 11 and (5, 1) not in table

# nearest-first left, head bit, nearest-first right, step count, expected output
witnesses = [
    ("", "0", "", 2, "1", "1"),
    ("11101", "1", "1", 7, "1", "100001"),
    ("100", "1", "100001", 5, "0", "100100001"),
    ("", "0", "100100001", 6, "0", "1000001"),
    ("", "0", "1000001", 5, "0", "01"),
    ("", "0", "01", 2, "1", "11"),
    ("11100", "1", "11", 7, "0", "1000011"),
    ("", "0", "1000011", 5, "0", "11"),
]

projection = ("0", "")
for index, (left, head, right, count, expected_head, expected_right) in enumerate(witnesses, 1):
    assert (head, right) == projection
    tape = {-(j + 1) for j, bit in enumerate(left) if bit == "1"}
    tape.update({0} if head == "1" else set())
    tape.update({j + 1 for j, bit in enumerate(right) if bit == "1"})
    state = position = 0
    history = []
    for t in range(count):
        write, move, state = table[state, int(position in tape)]
        if write:
            tape.add(position)
        else:
            tape.discard(position)
        position += move
        history.append(state)
    assert history[-1] == 0 and all(st != 0 for st in history[:-1])
    new_head = "1" if position in tape else "0"
    extent = max((cell - position for cell in tape if cell > position), default=0)
    new_right = "".join("1" if position + j in tape else "0" for j in range(1, extent + 1))
    assert (new_head, new_right) == (expected_head, expected_right)
    projection = (new_head, new_right)
    print(f"edge {index}: {count} primitive steps, ({head}, {right or 'empty'}) -> ({new_head}, {new_right})")

assert projection == ("0", "11")
state = position = 0
tape = {1, 2}
for t in range(2):
    write, move, state = table[state, int(position in tape)]
    if write:
        tape.add(position)
    else:
        tape.discard(position)
    position += move
assert (state, position in tape) == (5, True) and (5, 1) not in table
print("PASS: 8 independent first-A returns and F/1 two-step halting guard")
