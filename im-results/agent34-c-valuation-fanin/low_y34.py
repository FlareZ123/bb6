"""Exact original-source predecessor regression at y=3,4."""
from collections import defaultdict
from valuation_fanin import section,v2

def low_parents(x,y):
    assert y in (3,4)
    out=set()
    if y==3:
        if x==2:out.add((1,1))
        q=x+6;v=v2(q)
        if q.bit_count()==1 and v>=4:
            n=v-4;c=x-3-3*n
            if c>=8 and c%2==0:out.add((1,c//2))
        for n in range(v):
            f=2**(n+1)
            if q%f:continue
            a=q//f-3;c=x+1-a-3*n
            if a>=3 and a%2 and c>0 and c%2==0 and a<c:out.add((a,c//2))
    else:
        out.add((x+2,1))
        if x==0:out.add((0,1))
        q=x+4;v=v2(q)
        if q.bit_count()==1 and v>=3:
            n=v-3;c=x-1-3*n
            if c>=4 and c%2==0:out.add((0,c//2))
        for n in range(v):
            f=2**(n+1)
            if q%f:continue
            a=q//f-2;c=x+1-a-3*n
            if a>=2 and a%2==0 and c>0 and c%2==0 and a<c:out.add((a,c//2))
    return {p for p in out if section(*p)==(x,y)}

def test():
    forward=defaultdict(set)
    for a in range(350):
        for k in range(350):
            o=section(a,k)
            if o and o[1] in (3,4):forward[o].add((a,k))
    for (x,y),ps in forward.items():assert ps<=low_parents(x,y),(x,y,ps)
    print("Forward y3/y4 edges checked:",sum(map(len,forward.values())))
    for x in range(100000):
        d3=len(low_parents(x,3));v3=v2(x+6)
        assert d3<=v3//2,(x,3,d3,v3)
        d4=len(low_parents(x,4))
        q4=x+4 if x%2==0 else x+5
        assert d4<=v2(q4)//2+1,(x,4,d4,q4)
    print("Boundary targets checked:",200000)
    for v in range(2,19):
        x=3*2**v-6
        assert len(low_parents(x,3))==v//2
        q=2**v if v%2==0 else 3*2**v
        assert len(low_parents(q-4,4))==v//2+1
    print("PASS: all low-output bounds and unbounded sharpness families")

if __name__=="__main__":
    test()
