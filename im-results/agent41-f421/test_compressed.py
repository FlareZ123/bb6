"""Compare compressed principal macros with independent existing bit-string map."""
from frontier_map import advance, RULES
from subprocess import run
import random

def parse(u):
    p=u.rstrip('0')+'000';i=0;out=[]
    while True:
        x='10' if p.startswith('10',i) else p[i:i+3]
        if x=='111':return i+3,3,0
        if x in RULES:
            out.append(RULES[x]);i+=len(x);continue
        d=x.startswith('00');assert d or x=='011'
        i+=2 if d else 3
        X='1'+''.join(out)+('1' if d else '10')
        assert len(X)==i
        b=sum(X[j:j+2]=='01' for j in range(i%2,i,2))
        return i,1 if d else 2,b

def ref(u):
    L,t,b=parse(u);r=advance(u)
    if r is None:
        assert t==3
        return f'BAD {L} {L-1}'
    v,cost,dx=r
    L2,t2,b2=parse(v);v2,cost2,dx2=advance(v)
    assert L2%2==0 and t2==1 and b2==0 and dx2==2
    assert cost==L+2*(L//2)+4*b+2 and cost2==2*L2+2
    return f'{v2} {L} {t} {b} {L2} {cost+cost2} {dx+dx2}'

if __name__=='__main__':
    rng=random.Random(421)
    words=['10'*rng.randint(1,20)+'01'+''.join(rng.choices('01',k=rng.randrange(0,200))) for _ in range(10000)]
    u='10010101'
    for i in range(2000):
        words.append(u);u=advance(advance(u)[0])[0]
    p=run(['./compressed','--one'],input='\n'.join(words)+'\n',text=True,capture_output=True,check=True)
    rows=p.stdout.splitlines();assert len(rows)==len(words)
    for i,(w,actual) in enumerate(zip(words,rows)):
        expected=ref(w)
        assert actual==expected,(i,w,expected,actual)
    print(f'{len(words)} compressed macros matched: exact word, consumed length, terminal type, bounce count, second sweep length, primitive cost and displacement')
