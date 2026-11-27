"""Conditional finite-state return parser for exact Raw42/0RA leaf 1659."""
T = {}
for a in [3, 4, 5]:
    T['A'+str(a)] = {'1': ('A'+str(a), '0'), '0': ('E', '0'*(a-2)+'1')}
T.update(E={'0': ('copy', '0101'), '1': ('C', '')},
         C={'0': ('Z', '')}, Z={'0': ('A5', ''), '1': ('Y', '')},
         Y={'0': ('A4', '01'), '1': ('X', '')}, X={'1': ('A3', '0101')},
         copy={'0': ('copy', '0'), '1': ('copy', '1')})
for i, b in enumerate('0001'):
    T['I'+str(i)] = {b: ('I'+str(i+1) if i < 3 else 'A3', '' if i < 3 else '00')}

def run(w):
    q = 'I0'
    out = []
    for b in w + '000000':
        if b not in T[q]:
            return None
        q, s = T[q][b]
        out.append(s)
    assert q == 'copy', q
    return ''.join(out).rstrip('0')

def primitive(w, limit=1000000):
    m = '1RB1RE_1RC0RA_0RD---_1LD0LB_1LF0RC_0LA0LF'.replace('_', '')
    t = {i for i, c in enumerate(w) if c == '1'}
    q = x = 0
    for i in range(limit):
        if i and q == 0 and x == -2:
            assert not any(j < x for j in t)
            return ''.join('1' if j in t else '0' for j in range(x, max(t, default=x)+1)).rstrip('0')
        a = m[6*q+3*(x in t):6*q+3*(x in t)+3]
        if a == '---':
            return None
        if a[0] == '1':
            t.add(x)
        else:
            t.discard(x)
        x += 1 if a[1] == 'R' else -1
        q = ord(a[2])-65
    raise RuntimeError('primitive replay cutoff')

if __name__ == '__main__':
    w = '000101'
    for i in range(10000):
        v = run(w)
        assert v is not None, (i, w)
        if i < 100:
            assert v == primitive(w), (i, w, v)
        w = v
    print('10000 returns; final word length', len(w))
