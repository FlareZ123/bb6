"""Independent exact replay of the raw104 candidate certificate, without Lean.
The C++ search is only a certificate producer. No time cutoff is accepted.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PARENT = '1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1LF'
WITNESS = '1RB0RB_1RC1LF_0RDHHH_1LD1RE_1RA0LB_0RE1LF'
MOVES = [''.join(x) for x in product('01', 'LR', 'ABCDEF')]
B = 78

def parse(code):
    s = code.replace('_', '')
    assert len(s) == 36
    return tuple(s[i:i+3] for i in range(0, 36, 3))

def trace(p, n):
    q = h = 0
    ones = set()
    out = []
    for i in range(n + 1):
        out.append((q, h, frozenset(ones)))
        if i == n:
            return out
        a = p[2*q + (h in ones)]
        assert a in MOVES, (i, a, p)
        if a[0] == '1':
            ones.add(h)
        else:
            ones.discard(h)
        h += 1 if a[1] == 'R' else -1
        q = ord(a[2]) - 65
    raise AssertionError('unreachable')

def query(p, n, s):
    q, h, ones = trace(p, n)[-1]
    assert 2*q + (h in ones) == s and p[s] == '---'
    halted = p[:s] + ('HHH',) + p[s+1:]
    def delay(q, visited):
        return max([0] + [1 + delay(j, visited | {j}) for j in range(6)
            if j not in visited and (halted[2*j] == '---' or
                (halted[2*j] in MOVES and halted[2*j][0] == '0' and
                 ord(halted[2*j][2])-65 == q))])
    return n + 1 + delay(0, {0})

def cycle(p, entry, period, right, b):
    assert period > 0
    t = trace(p, entry+period)
    q,h,o = t[entry]
    q2,h2,o2 = t[-1]
    delta = h2-h
    side = (lambda x:x>=b) if right else (lambda x:x<=b)
    assert q == q2 and (delta>=0 if right else delta<=0)
    assert all(side(x[1]) for x in t[entry:-1])
    assert {x for x in o if side(x)} == {x-delta for x in o2 if side(x-delta)}

def far(p, data):
    rev = int(data[0]); dfa = list(map(int, data[1:])); d = len(dfa)//2
    assert rev in (0,1) and len(dfa)==2*d and dfa[0]==0 and all(0<=x<d for x in dfa)
    H=6*d; N=H+1
    E=[[set() for _ in range(N)] for _ in range(2)]
    E[0][H].add(H); E[1][H].add(H)
    rules=[]
    for l,q,a in product(range(d),range(6),range(2)):
        v=p[2*q+a]; src=6*l+q
        if v=='---':
            E[a][src].add(H)
        else:
            assert v in MOVES
            w=int(v[0]); q2=ord(v[2])-65
            if (v[1]=='R') != bool(rev):
                E[a][src].add(6*dfa[2*l+w]+q2)
            else:
                for j,b in product(range(d),range(2)):
                    if dfa[2*j+b]==l:
                        rules.append((a,src,b,6*j+q2,w))
    while True:
        changed=False
        for a,s,b,t,w in rules:
            new=set().union(*(E[w][v] for v in E[b][t]))
            if not new<=E[a][s]:
                E[a][s].update(new);changed=True
        if not changed: break
    Z={H}
    while True:
        z=Z|{s for s in range(N) if E[0][s]&Z}
        if z==Z: break
        Z=z
    # Check the finite logical conditions of FAR.Certificate, separately from saturation.
    assert H in Z and 0 not in Z
    assert all(H in E[a][H] for a in range(2))
    assert all((s in Z)==bool(E[0][s]&Z) for s in range(N))
    for l,q,a in product(range(d),range(6),range(2)):
        v=p[2*q+a]; s=6*l+q
        if v=='---':
            assert H in E[a][s]
        else:
            w=int(v[0]);q2=ord(v[2])-65
            if (v[1]=='R') != bool(rev):
                assert 6*dfa[2*l+w]+q2 in E[a][s]
            else:
                for j,b in product(range(d),range(2)):
                    if dfa[2*j+b]==l:
                        assert all(E[w][v]<=E[a][s] for v in E[b][6*j+q2])

raw=(ROOT/'open.txt').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='9f7ea936ec2710ed5d4909338c31a74e0c5f0a71574e69d1f9d88b4f5dd62f17'
opens=raw.decode().splitlines()
assert len(opens)==len(set(opens))==126
dfas=['00102030400']*126
for row in (ROOT/'dfa.txt').read_text().split():
    a,indices=row.split(':')
    for i in indices.split(','):
        dfas[int(i)]=a
certs={parse(p):a for p,a in zip(opens,dfas)}
used=set(); counts=Counter(); maximum=0

def verify(p,t):
    global maximum
    kind,*v=t; counts[kind]+=1
    holes=p.count('---')
    if kind=='cycle':
        cycle(p,*v)
        return 25**holes
    if kind=='open':
        assert parse(v[0])==p and p not in used
        far(p,certs[p]);used.add(p)
        return 25**holes
    assert kind in ('last','split')
    n,s=v[:2];score=query(p,n,s);maximum=max(maximum,score)
    assert score<=B,(score,p)
    if kind=='last':
        assert holes==1
        return 25
    kids=v[2];assert holes>1 and len(kids)==len(MOVES)
    mass=25**(holes-1)
    for a,k in zip(MOVES,kids):
        mass+=verify(p[:s]+(a,)+p[s+1:],k)
    assert mass==25**holes
    return mass

mass=verify(parse(PARENT),json.loads((ROOT/'tree.json').read_text()))
assert mass==25**4 and used==set(certs) and maximum==B
assert counts==Counter(split=116,last=578,cycle=1965,open=126)
p=parse(PARENT);m=parse(WITNESS)
assert all(a=='---' or a==b for a,b in zip(p,m))
q,h,o=trace(m,77)[-1];assert m[2*q+(h in o)]=='HHH'
print('Exact replay passed:',dict(counts),'mass',mass,'weighted maximum',maximum,'attaining ordinary steps',77)
