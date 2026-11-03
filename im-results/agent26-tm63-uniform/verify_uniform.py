"""Independent physical-tape randomized regression for TM63Uniform.counted_all."""
from random import Random

RLE = '1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD'
RULES = []
for pair in RLE.split('_'):
    row = []
    for i in (0, 3):
        raw = pair[i:i+3]
        row.append(None if raw == '---' else
                   (int(raw[0]), 1 if raw[1] == 'R' else -1, ord(raw[2]) - 65))
    RULES.append(row)
assert len(RULES) == 6 and all(len(row) == 2 for row in RULES)


def physical(left, head, right):
    marks = {-i for i, b in enumerate(left, 1) if b}
    if head:
        marks.add(0)
    marks.update(i for i, b in enumerate(right, 1) if b)
    return marks


def exercise(k, c, left, right):
    original_word = '100' + '111' * k
    goal_word = '111' + '100' * k
    l0 = list(map(int, original_word[-2::-1])) + left
    h0 = int(original_word[-1])
    r0 = [0, 1, 1, 1, 0, 0] + [1] * (3 * (c + 1)) + [0, 0, 0] + right
    score = 48 + 12 * (k + c)
    marks = physical(l0, h0, r0)
    state, head_pos = 3, 0
    for t in range(score):
        action = RULES[state][int(head_pos in marks)]
        assert action is not None, (k, c, t, 'premature halt')
        bit, direction, state = action
        if bit:
            marks.add(head_pos)
        else:
            marks.discard(head_pos)
        head_pos += direction
    l1 = list(map(int, goal_word[-2::-1])) + left
    h1 = int(goal_word[-1])
    r1 = [0, 1, 1, 1, 0, 0] + [1] * (3 * (c + 2)) + right
    assert (state, head_pos) == (3, 0), (k, c, state, head_pos)
    assert marks == physical(l1, h1, r1), (k, c, marks ^ physical(l1, h1, r1))


def main():
    rng = Random(2026110326)
    count = 0
    for k in range(31):
        for c in range(20):
            for _ in range(5):
                left = [rng.randrange(2) for _ in range(rng.randrange(41))]
                right = [rng.randrange(2) for _ in range(rng.randrange(41))]
                exercise(k, c, left, right)
                count += 1
    print(f'PASS {count} original-TM63 full-tape exact-score trials, k=0..30,c=0..19,random left/right exteriors')


if __name__ == '__main__':
    main()
