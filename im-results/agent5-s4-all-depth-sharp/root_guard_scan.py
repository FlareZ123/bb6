"""Reproduce the S4 source-map root orbit's all-suffix danger events.

This is finite simulation, not a proof of the unbounded blank-tape orbit.
"""
from collections import Counter
from checker import chain, classify_prefix

SEED = (301, 650, 645, 322, 163, 160)
OFFSETS = (509, 290, 219)


def scan(steps: int = 1_000_000) -> None:
    current = SEED
    counts: Counter[str] = Counter()
    for n in range(steps):
        verdict = classify_prefix(OFFSETS, current)
        counts['safe' if verdict.universally_safe else 'unsafe'] += 1
        if not verdict.universally_safe:
            counts[f'bad_stage_{verdict.failing_stage}'] += 1
            print('UNSAFE', n, 'length', len(current), 'stage', verdict.failing_stage,
                  'witness', verdict.witness_digit,
                  'terminal_power', verdict.terminal_power_exponent)
        nxt = chain(OFFSETS, current)
        if nxt is None:
            print('MODELED_HALT', n, 'stack', current)
            return
        if len(nxt) > len(current):
            counts['length_expansions'] += 1
            print('EXPANSION', n, len(current), 'to', len(nxt))
        current = nxt
    print('FULL_SCAN', steps, 'final_length', len(current), 'counts', dict(counts))


if __name__ == '__main__':
    scan()
