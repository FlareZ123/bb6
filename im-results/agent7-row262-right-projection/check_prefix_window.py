"""Independent original-RLE regression for the 19 first-A-return 4-left-bit witnesses.

The 19 entries use different full left tapes and are not one blank-tape orbit.
"""
from check_right_projection import table

# nearest-first full left, head, right, exact primitive steps, next left4, head, right
DATA = "0000|0||2|0000|1|1\n000000|1|1|4|0000|0|101\n0000|0|101|5|0101|0|\n0101|0||2|0101|1|1\n010111|1|1|4|0111|1|101\n011101|1|101|4|1101|1|10101\n11010000|1|10101|6|0000|1|100010101\n000000|1|100010101|4|0000|0|10100010101\n0000|0|10100010101|5|0101|0|010101\n0101|0|010101|2|0101|1|110101\n010100|1|110101|4|0100|1|10110101\n010000|1|10110101|4|0000|1|1010110101\n000000|1|1010110101|4|0000|0|101010110101\n0000|0|101010110101|5|0101|1|0110101\n010111|1|0110101|4|0111|1|100110101\n011110|1|100110101|4|1110|1|10100110101\n111000000|1|10100110101|7|0000|0|1000010100110101\n0000|0|1000010100110101|5|0001|0|10100110101\n0001|0|10100110101|5|0101|0|110101"

projection = ("0000", "0", "")
total = 0
for index, line in enumerate(DATA.splitlines(), 1):
    left, head, right, steps, next_left, next_head, next_right = line.split("|")
    steps = int(steps)
    assert (left[:4], head, right) == projection
    tape = {-(j + 1) for j, b in enumerate(left) if b == "1"}
    if head == "1":
        tape.add(0)
    tape.update({j + 1 for j, b in enumerate(right) if b == "1"})
    state = pos = 0
    for t in range(1, steps + 1):
        write, move, state = table[state, int(pos in tape)]
        (tape.add if write else tape.discard)(pos)
        pos += move
        if t < steps:
            assert state != 0, (index, t, "early A return")
    assert state == 0
    actual_left = "".join("1" if pos - j in tape else "0" for j in range(1, 5))
    actual_head = "1" if pos in tape else "0"
    extent = max((cell - pos for cell in tape if cell > pos), default=0)
    actual_right = "".join("1" if pos + j in tape else "0" for j in range(1, extent + 1))
    projection = (actual_left, actual_head, actual_right)
    assert projection == (next_left, next_head, next_right), (index, projection)
    total += steps
    print(f"edge {index:2d}: first A return in {steps} steps; projection {projection}")
assert projection == ("0101", "0", "110101") and total == 80
print("PASS: 19 separate source-RLE first A returns, 80 primitive transitions")
