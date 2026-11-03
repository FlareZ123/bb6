"""Independent literal six-state, two-symbol primitive interpreter for E(10)^q111 sections."""
from itertools import product
from random import Random

TABLE=(('1RB','0RE'),('1LC','0RA'),('1LA','1LD'),('1LC','1LF'),('0LC','0LB'),('1LE','---'))
RULES=tuple(tuple(None if entry=='---' else (int(entry[0]), 1 if entry[1]=='R' else -1, ord(entry[2])-ord('A')) for entry in row) for row in TABLE)


def check(k,q,tail):
    # I_(3k+4): F/0 with blank physical tape left, right 1^(3k+4) 0 (10)^q 111 tail.
    word=[1]*(3*k+4)+[0]+[v for _ in range(q) for v in (1,0)]+[1,1,1]+list(tail)
    tape={i+1 for i,b in enumerate(word) if b}
    x=0; state=5
    expected=12*k*k+49*k+58+6*q
    for t in range(1,expected+1):
        symbol=int(x in tape)
        rule=RULES[state][symbol]
        if rule is None: raise AssertionError(('premature-halt',k,q,tail,t-1))
        bit,move,state=rule
        if bit:tape.add(x)
        else:tape.discard(x)
        x+=move
        if state==5 and x not in tape and all(p>=x for p in tape):
            if t!=expected: raise AssertionError(('premature-physical-return',k,q,tail,t,expected))
    if state!=5 or x in tape or any(p<x for p in tape):
        raise AssertionError(('missing-endpoint',k,q,tail,expected,x,state))
    # Physical return normalizes head to 0; next unary1 length must be 8k+9, suffix (01)^(q+2) 0 tail.
    ones=8*k+9
    outcome=[int(i in tape) for i in range(x+1, x+1+ones+2*(q+2)+1+len(tail))]
    want=[1]*ones+[v for _ in range(q+2) for v in (0,1)]+[0]+list(tail)
    if outcome!=want:raise AssertionError(('wrong-endpoint',k,q,tail,expected,x,outcome,want))
    return expected

if __name__=='__main__':
    sample=0;steps=0
    for k in range(8):
        for q in range(9):
            for n in range(7):
                for tail in product((0,1),repeat=n):
                    steps+=check(k,q,tail);sample+=1
    rng=Random(20261103)
    for _ in range(300):
        k=rng.randrange(0,24);q=rng.randrange(0,32);n=rng.randrange(0,80)
        tail=[rng.randrange(2) for _ in range(n)]
        steps+=check(k,q,tail);sample+=1
    print('PASS',sample,'literal full-tape exact-time/no-earlier-physical-return cases;',steps,'primitive transitions')
