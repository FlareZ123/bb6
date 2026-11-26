"""Exact candidate F421 frontier map and independent primitive replay."""
TABLE = "1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---"
RULES = {'10':'01','110':'011','010':'101'}

def advance(u):
    u = u.rstrip('0') + '000'
    i, out = 0, []
    while True:
        x = '10' if u.startswith('10', i) else u[i:i+3]
        if x in RULES:
            out.append(RULES[x])
            i += len(x)
        elif x == '111':
            return None
        elif x.startswith('00'):
            i += 2
            term = 0
            break
        elif x == '011':
            i += 3
            term = 1
            break
        else:
            raise AssertionError((u, i, x))
    X = '1' + ''.join(out) + ('10' if term else '1')
    assert len(X) == i
    odd = len(X) % 2
    P = [X[j:j+2] for j in range(odd, len(X), 2)]
    assert P[-1] == ('10' if term else '11')
    assert all(p != '00' for p in P)
    cost = i + sum(6 if p == '01' else 2 for p in P) + 2
    v = ('0' if odd else '1') + '0' + ''.join('00' if p == '11' else p for p in P[:-1]) + ('10' if term else '01') + u[i:]
    return v.rstrip('0'), cost, 1 if odd else 2

def replay(n=1000):
    import itertools
    transitions = dict(zip(itertools.product('ABCDEF','01'),
                           (x[i:i+3] for x in TABLE.split('_') for i in (0,3))))
    q, h, tape, time = 'A', 0, set(), 0
    def step():
        nonlocal q, h, time
        w,d,nq = transitions[q, str(int(h in tape))]
        assert nq != '-'
        if w == '1': tape.add(h)
        else: tape.discard(h)
        h += 1 if d == 'R' else -1
        q = nq
        time += 1
    for _ in range(3): step()
    u = '11'
    for k in range(n+1):
        assert q == 'D'
        assert {x for x in tape if x > h} == {h+1}
        assert ''.join(str(int(x in tape)) for x in range(h, min(tape)-1, -1)).rstrip('0') == u
        if k == n: break
        v,cost,dx = advance(u)
        old = h
        for _ in range(cost): step()
        assert h == old + dx
        u = v
    print(f'{n} returns matched; steps={time}; head={h}')
if __name__ == '__main__':
    replay()
