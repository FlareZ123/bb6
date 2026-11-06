"""Source-shaped Machine C first-return and valuation fibre tester."""
def bounce(k,c):
    while c>=4:
        if k%2:
            if c<=2*k+6:return 2*k+6-c,c
            c,k=c-(2*k+3),2*k+3
        else:
            if c==4:return 2*k+2,3
            if c==5:return None
            if c<=2*k+8:return 2*k+8-c,c-1
            c,k=c-(2*k+5),2*k+4
    return None

def section(a,k):
    if a==0:return None if k==0 else ((0,4) if k==1 else bounce(1,2*k+1))
    if a==1:return [(5,1),(2,3),(2,5),(0,7)][k] if k<=3 else bounce(4,2*k-3)
    if k==0:return a-2,2
    if 2*k<=a:return a-2*k,2*k+2
    return bounce(a-1,2*k-a+3)

def v2(z):return (z&-z).bit_length()-1

def candidates(x,y):
    assert x>=0 and y>=5
    s=x+y;q=s if s%2==0 else s+1
    mass=x+2*y;v=v2(q);out=set()
    if y%2==0:out.add((s-2,(y-2)//2))
    if (x,y)==(2,5):out.add((1,2))
    if (x,y)==(0,7):out.add((1,3))
    if s%2==0:
        if s.bit_count()==1 and v>=3:
            n=v-3;cost=mass-9-3*n
            if cost>=4 and cost%2==0:out.add((0,cost//2))
        for n in range(v-1):
            if (n+1)%2!=x%2:continue
            a=s//2**(n+1)-2;cost=mass-a-7-3*n
            if a>=2 and cost>0 and cost%2==0 and a<cost:out.add((a,cost//2))
    else:
        if q.bit_count()==1 and v>=4:
            n=v-4;cost=mass-11-3*n
            if cost>=8 and cost%2==0:out.add((1,cost//2))
        for n in range(v-1):
            if n%2!=x%2:continue
            a=q//2**(n+1)-3;cost=mass-a-7-3*n
            if a>=3 and cost>0 and cost%2==0 and a<cost:out.add((a,cost//2))
    return out

def parents(x,y):return {p for p in candidates(x,y) if section(*p)==(x,y)}

def test():
    from collections import defaultdict
    forward=defaultdict(set)
    for a in range(225):
        for k in range(225):
            p=section(a,k)
            if p and p[1]>=5:forward[p].add((a,k))
    for (x,y),ps in forward.items():
        assert ps<=parents(x,y),(x,y,ps-parents(x,y))
    print("Forward source pairs:",225*225,"verified edges:",sum(map(len,forward.values())))
    count=0
    for s in range(5,1250):
        for y in range(5,s+1):
            x=s-y
            q=s if s%2==0 else s+1
            ps=parents(x,y)
            assert len(ps)<=v2(q)//2+1,(x,y,ps)
            count+=1
    print("Valuation-checked targets:",count)
    for v in range(3,25):
        x,y=(2**v-5,5) if v%2 else (2**v-6,6)
        ps=parents(x,y)
        assert len(ps)==v//2+1,(v,ps)
        print("Sharp witness valuation",v,"target",(x,y),"degree",len(ps))
    print("PASS: source-shaped inverse and sharpness regression")

if __name__=="__main__":
    test()
