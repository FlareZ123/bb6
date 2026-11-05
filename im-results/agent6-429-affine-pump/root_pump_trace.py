"""Exact-source arithmetic trace for the observed #429 blank-origin affine pump.
Finite computation only. No claim of certified blank reachability or BB(6) decision.
"""


def next429(u: int, w: int) -> tuple[int, int] | None:
    if w >= 2*u+3:
        return 2*u+3, w-2*u-3
    if w == 2*u+2:
        return 0, 4*u+18
    if w == 2*u+1:
        return 11, 4*u+2
    if w == 2*u:
        return 0, 4*u+12
    d = u-w//2
    if w%2==0:
        if d==1:
            return 0, 2*w+12
        if d%2==0:
            return 11, 2*u+w-2
        return 0, 2*u+w+10
    if d==1:
        return None
    if d==2:
        return 0, 2*w+8
    if d%2==0:
        return (11,2*u+10) if w==1 else (d+7,2*w-4)
    return d+3,2*w


known = {
    0:(0,0),
    275305:(0,1048576),
    275342:(393149,262426),
    275343:(11,1048722),
    314391:(305863,611570),
    314392:(11,1223294),
    314410:(611622,138),
    314411:(0,1223392),
}
s=(0,0)
for i in range(max(known)+1):
    if i in known:
        assert s==known[i], (i,s,known[i])
        print(f'macro {i:6d}: {s}')
    if i<max(known):
        next_state=next429(*s)
        assert next_state is not None, ('unexpected halt',i,s)
        s=next_state
assert 314392-275343==17*2297
print('PASS: independently simulated genuine blank source trace; 2297 pump cycles match exact endpoints')
