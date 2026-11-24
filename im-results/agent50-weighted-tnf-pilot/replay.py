"""Replay the complete ten-row weighted-TNF pilot, using only Python stdlib."""
from itertools import product
from collections import Counter

PARENT = "1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_0LE0LA"
PATH = [(1,2,"1RC"),(2,4,"0RD"),(3,6,"1LD"),(5,7,"1RE"),
        (6,9,"0LB"),(7,3,"1LF"),(8,11,"0LA"),(11,5,"0RB"),(21,10,"0LE")]
WITNESSES = [
    ("0LA","last",36,None),("0LB","last",40,None),
    ("0LC","ray",33,None),("0LD","ray",32,None),
    ("0LE","last",32,None),("0LF","last",33,None),
    ("0RA","lasso",40,20),("0RB","lasso",52,20),
    ("0RC","last",34,None),("0RD","ray",32,None),
    ("0RE","last",32,None),("0RF","last",33,None),
    ("1LA","last",83,None),("1LB","last",68,None),
    ("1LC","last",34,None),("1LD","ray",32,None),
    ("1LE","last",32,None),("1LF","last",33,None),
    ("1RA","lasso",33,29),("1RB","lasso",36,20),
    ("1RC","last",34,None),("1RD","last",37,None),
    ("1RE","last",32,None),("1RF","last",42,None),
]

def parse(s):
    s = s.replace("_", "")
    assert len(s) == 36
    return [s[i:i+3] for i in range(0,36,3)]

def trace(p,n):
    q = h = 0
    ones = set()
    for i in range(n):
        a = p[2*q + int(h in ones)]
        assert a not in ("---","HHH"), ("early hole",i)
        if a[0] == "1": ones.add(h)
        else: ones.discard(h)
        h += 1 if a[1] == "R" else -1
        q = ord(a[2])-65
    return q,h,frozenset(ones)

def slot(c):
    q,h,ones = c
    return 2*q + int(h in ones)

def delays(p):
    # Enumerate simple incoming zero-writing paths ending at state A.
    def can(s,t):
        a=p[2*s]
        return a=="---" or (a[0]=="0" and ord(a[2])-65==t)
    result={0}
    def walk(t,seen):
        for s in range(6):
            if s not in seen and can(s,t):
                result.add(len(seen))
                walk(s, seen|{s})
    walk(0,{0})
    return sorted(result)

def main():
    p=["---"]*12
    p[0]="1RB"
    cut=2
    for n,s,a in PATH:
        assert slot(trace(p,n)) == s and p[s] == "---"
        q=ord(a[2])-65
        assert s//2 < cut and q<=cut
        cut=max(cut,q+1)
        p[s]=a
    assert p==parse(PARENT) and cut==6
    assert slot(trace(p,31))==1 and p[1]=="---"
    assert trace(p,31)==(0,-1,frozenset({-1,1,3,4,6}))
    h=p.copy()
    h[1]="HHH"
    assert delays(h)==[0,1,2]
    max_weight=32+max(delays(h))
    counts=Counter()
    moves={w+d+q for w,d,q in product("01","LR","ABCDEF")}
    assert len(WITNESSES)==24 and {a for a,*_ in WITNESSES}==moves
    for a,kind,n,k in WITNESSES:
        ch=p.copy()
        ch[1]=a
        c=trace(ch,n)
        counts[kind]+=1
        if kind=="last":
            assert slot(c)==8 and ch[8]=="---" and ch.count("---")==1
            ch[8]="HHH"
            assert delays(ch)==[0]
            max_weight=max(max_weight,n+1)
        elif kind=="ray":
            q,h,ones=c
            assert q==3 and all(x>h for x in ones) and ch[6]=="1LD"
        elif kind=="lasso":
            assert k<n and trace(ch,k)==c
        else:
            raise AssertionError(kind)
    assert counts=={"last":16,"ray":4,"lasso":4}
    assert max_weight==84
    print("Path verified; cut=6; all 24 ordinary children accepted.")
    print("Verdicts:",dict(counts),"max weighted score:",max_weight)
    print("Raw completions: 625; halt: 41; nonhalt: 584; residual: 0")

if __name__=="__main__":
    main()
