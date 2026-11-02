"""Conservative source-RLE overlap audit against the dated 663-root snapshot.

The zero-edge orbit is used ONLY when its control graph is closed with either
all writes zero or one fixed head direction. Other zero-edge paths are not
asserted to agree with the physical machine (the head may revisit a 1).

This is a classification audit of a dated list, not proof the list is complete.
"""
from pathlib import Path


def parse_rle(line: str) -> list[list[str]]:
    states = line.strip().split('_')
    if len(states) != 6 or any(len(s) != 6 for s in states):
        raise ValueError(f"Invalid six-state two-symbol RLE: {line}")
    actions = [[s[:3], s[3:]] for s in states]
    allowed = set('ABCDEF')
    for row in actions:
        for act in row:
            if act != '---' and not (
                len(act) == 3 and act[0] in '01'
                and act[1] in 'LR' and act[2] in allowed
            ):
                raise ValueError(f"Invalid RLE action {act}: {line}")
    return actions


def classify_zero_orbit(actions: list[list[str]]) -> tuple[bool, bool]:
    current = 0
    seen: set[int] = set()
    writes: list[str] = []
    directions: list[str] = []
    while current not in seen:
        seen.add(current)
        act = actions[current][0]
        if act == '---':
            return False, False
        writes.append(act[0])
        directions.append(act[1])
        current = ord(act[2]) - ord('A')
    return all(d == directions[0] for d in directions), all(w == '0' for w in writes)


def matches(actions: list[list[str]], required: tuple[tuple[int, int, str], ...]) -> bool:
    return all(actions[state][read] == act for state, read, act in required)


BOUNCE = ((0, 0, '1RB'), (1, 0, '0LA'), (0, 1, '0RB'))
TRANSIENT = ((0, 0, '1RB'), (1, 0, '0LA'), (0, 1, '0RC'), (2, 0, '1RC'))


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    path = root / 'resources' / 'BB6_holdouts_663_2026-10-16.txt'
    lines = [line.strip() for line in path.read_text(encoding='utf-8').splitlines()
             if line.strip()]
    if len(lines) != 663 or len(set(lines)) != len(lines):
        raise AssertionError('Expected exactly 663 distinct pinned October roots')
    counters = {'directed': 0, 'zero_writer': 0,
                'bounce': 0, 'transient': 0, 'any_certified': 0}
    for line in lines:
        actions = parse_rle(line)
        directed, zero_writer = classify_zero_orbit(actions)
        bounce = matches(actions, BOUNCE)
        transient = matches(actions, TRANSIENT)
        counters['directed'] += directed
        counters['zero_writer'] += zero_writer
        counters['bounce'] += bounce
        counters['transient'] += transient
        counters['any_certified'] += directed or zero_writer or bounce or transient
    for key, value in counters.items():
        print(f'{key}: {value} / {len(lines)} dated listed rooted RLEs')
    assert counters == {key: 0 for key in counters}
    print('None of the dated 663 roots is directly certified by these easy leaves.')
    print('This does NOT establish anything about the current live holdout census.')


if __name__ == '__main__':
    main()
