"""Replay the exact partial search; no Lean acceptance is asserted."""
from collections import Counter
from pathlib import Path
import json, sys
here = Path(__file__).resolve().parent
sys.path[:0] = [str(here.parent / 'agent48-raw139-f1-oneLA'), str(here.parent / 'agent48-raw139-f1-oneRA')]
from scan import tree, scan, far
from blockcert import generate

s = json.loads((here / 'spec.json').read_text())
c = Counter(); opens = []
tree(s['parent'], c, opens, s['limit'], s['maxd'])
assert dict(c) == s['counts'], c
seen = set()
for params, indices in s['block_groups']:
    w, cap, mod, runs, flip, phase = params
    for i in indices:
        assert i not in seen
        assert generate(opens[i], w, cap, mod, runs, flip, phase=phase) is not None, i
        seen.add(i)
for i, (rev, dfa) in s['far'].items():
    i = int(i); assert i not in seen and far(opens[i], rev, dfa) is not None, i
    seen.add(i)
for i, args in s['late'].items():
    i = int(i); assert i not in seen and opens[i].count(24) == 1
    assert scan(opens[i], args[0]) == ('hole', *args), i
    assert args[0] + 6 <= s['bound']
    seen.add(i)
for i, p in s['open'].items():
    i = int(i); assert i not in seen and opens[i] == p and p.count(24) == 1
    seen.add(i)
assert seen == set(range(len(opens)))
print(dict(c), 'replayed block/FAR/late recipes:', len(seen)-len(s['open']), 'unresolved:', s['open'])
