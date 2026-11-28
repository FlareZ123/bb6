"""Locate the earliest certified F197 blank-run entrance into the
smaller Lean self-embedding cylinder, using the existing exact root trace.
This is a *computational scouting diagnostic*, not an independent proof.
"""
from verify_nonhalt import root_trace, HEAD, LB

D = root_trace()
rows = D['trace']
hits = []
types = {}
max_prefix = (-1, -1)
def test(i, n, w, where):
    global max_prefix
    if int(n) != 72 or not w.startswith(HEAD):
        return
    r = w[len(HEAD):]
    cnt = 0
    while r.startswith(LB):
        cnt += 1
        r = r[len(LB):]
    max_prefix = max(max_prefix, (cnt, i))
    if cnt >= 35:
        hits.append((i, where, cnt, len(w)))

for i, x in enumerate(rows):
    op = x.get('op', {})
    k = op.get('kind') or x.get('kind') or x.get('rule', {}).get('type') or 'unknown'
    types[k] = types.get(k, 0) + 1
    test(i, x['n'], x.get('w', x.get('before', '')), 'before')
    test(i, x['n2'] if 'n2' in x else x['n'],
         x.get('w2', x.get('after', '')), 'after')

assert hits, 'No 35-block cylinder reached'
assert rows[-1].get('n2', rows[-1]['n']) == '72'
assert hits[0][0] <= len(rows)
print('ROOT SCOUT total trace entries', len(rows))
print('ROOT SCOUT row-type census', sorted(types.items()))
print('ROOT SCOUT earliest 35-block candidate', hits[0])
print('ROOT SCOUT first 12 hits', hits[:12])
print('ROOT SCOUT max visible LB head prefix', max_prefix)
print('ROOT SCOUT retained 80-block target', D['end']['n'],
      D['end']['w'].startswith(HEAD + LB * 80))
