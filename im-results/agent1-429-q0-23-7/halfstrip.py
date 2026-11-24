"""Exact binary two-row strip exploration; witness validation by direct graph replay.
Negative results at a finite scale are not a uniform theorem.
"""
L=((5,9),(1,3))
C=((0,12),(0,4))
D=(0,1)

def nextrow(a,ph,q,e):
    if q%2 != ph:
        return
    for d in D:
        for r in D:
            if ph==0 and (a*r+e)%2:
                continue
            n=e+a*r+d*q+C[ph][d]
            if n%4==0:
                yield r,d,q+L[ph][d],n//4

def test(a,b,k):
    ph=b%2
    ph1=ph^(k%2)
    M=4**k
    hits=[]
    for e0 in range((a+b+2)//3+1):
        states={(b,e0)}
        for i in range(k):
            states={(Q,F) for q,e in states
                    for _,_,Q,F in nextrow(a,ph^(i%2),q,e)}
        for q1,e1 in states:
            def dfs(i,q,e,Q,f,w,v,z):
                if i==k:
                    if (q,e)!=(q1,e1):
                        return
                    p0=ph^(k%2)
                    l=sum(L[p0^(j%2)][r] for j,r in enumerate(w))
                    rem=l
                    B=0
                    power=1
                    for j,r in enumerate(w):
                        P=p0^(j%2)
                        B+=(b*r+C[P][r]-r*rem)*power
                        power*=4
                        rem-=L[P][r]
                    y=M*e0-B
                    p=a*M+b-l
                    if 0<3*y<p and p%2==p0 and (p0==1 or y%2==0):
                        hits.append((e0,q1,e1,w,v,z,y,p))
                    return
                p=ph^(i%2)
                P=ph1^(i%2)
                for r,d,q2,e2 in nextrow(a,p,q,e):
                    if P==0 and (a*d+f)%2:
                        continue
                    for t in D:
                        n=f+a*d+t*Q+C[P][t]
                        if n%4==0:
                            dfs(i+1,q2,e2,Q+L[P][t],n//4,w+(r,),v+(d,),z+(t,))
            dfs(0,b,e0,q1,e1,(),(),())
    return hits

def replay(p,y,ph,word):
    for d in word:
        assert p%2==ph and (ph or y%2==0)
        n=y+d*p+C[ph][d]
        assert n%4==0
        p,y=p+L[ph][d],n//4
        assert 0<3*y<p
        ph^=1
    return p,y,ph

if __name__=='__main__':
    import sys
    limit=int(sys.argv[1]) if len(sys.argv)>1 else 56
    for k in range(4,limit+1):
        for a in (1,2):
            for b in range(9):
                for e0,q1,e1,w,v,z,y,p in test(a,b,k):
                    print('crossing',a,b,k,p,y,w,v,z,flush=True)
                    start=(p,y)
                    ph=(b%2)^(k%2)
                    p,y,ph=replay(p,y,ph,w)
                    assert p==a*4**k+b
                    p,y,ph=replay(p,y,ph,v+z)
                    states={(p,y)}
                    extra=0
                    while states:
                        states={(q+L[ph][d],(e+d*q+C[ph][d])//4)
                                for q,e in states for d in D
                                if (e+d*q+C[ph][d])%4==0}
                        ph^=1
                        if states:
                            extra+=1
                    print('start',start,'extra',extra,flush=True)
