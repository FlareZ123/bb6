import random
from time import perf_counter

def valuation(w, r):
    return min(r, (w & -w).bit_length()-1) if w else r

def predicted_content(weights,r):
    m=[0]*(r+1)
    for w in weights:m[valuation(w,r)]+=1
    v=m[r]; t=r-1
    while t>=0 and m[t]:
        v+=m[t]-1;t-=1
    if t>=0:v+=max(0,(sum(m[i]<<i for i in range(t))>>t)-1)
    return v,t+1

def exact_counts(weights,r):
    M=1<<r;c=[1]+[0]*(M-1)
    for w in weights:c=[c[i]+c[(i-w)%M] for i in range(M)]
    return c

def strip(weights,r):
    weights=list(weights)
    while r:
        M=1<<r
        idx=next((i for i,w in enumerate(weights) if w%M==M//2),None)
        if idx is None:break
        weights.pop(idx);r-=1
    return weights,r

def support(weights,r,Y):
    M=1<<r;seen=bytearray(M);a=[Y%M];seen[a[0]]=1
    for w in weights:
        for i in range(len(a)):
            z=(a[i]-w)%M
            if not seen[z]:a.append(z);seen[z]=1
    return seen

def main():
    rng=random.Random(23)
    for _ in range(10000):
        r=rng.randrange(1,9);ws=[rng.randrange(-4096,4096) for _ in range(rng.randrange(40))]
        c=exact_counts(ws,r);v,p=predicted_content(ws,r)
        assert min((x&-x).bit_length()-1 for x in c if x)==v
        assert all(c[i]==c[i%(1<<p)] for i in range(len(c)))
        assert p==0 or any(c[i]!=c[i%(1<<(p-1))] for i in range(len(c)))
    print('10000 random arbitrary-weight count/content/least-period comparisons passed')
    for F,r in [(1000024,22),(1310744,24)]:
        ws=[(F-r+i)<<i for i in range(r)]
        a,k=strip(ws,r)
        t=perf_counter();full=support(ws,r,12345);t1=perf_counter()-t
        t=perf_counter();small=support(a,k,12345);t2=perf_counter()-t
        assert full==small*((1<<r)//len(small))
        print(f'F={F}, r={r}, reduced={k}, bitmap ratio={2**(r-k)}, full={t1:.3f}s, reduced={t2:.3f}s, speedup={t1/t2:.1f}')

if __name__=='__main__':main()
