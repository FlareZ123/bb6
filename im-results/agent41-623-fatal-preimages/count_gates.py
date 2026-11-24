"""Exact number of even exponents in each necessary gate up to X.
Uses monotone index bounds and ordinary ternary prefix digit DP.
"""
def digits(t,m):
    out=[]
    for _ in range(m):
        t,d=divmod(t,3);out.append(d)
    assert t==0
    return out[::-1]

def upper(f,x,lo,hi):
    # Last index t with f(t)<=x, or lo-1.
    while lo<=hi:
        mid=(lo+hi)//2
        if f(mid)<=x:lo=mid+1
        else:hi=mid-1
    return hi

def count_prefix(T,m,weights,mod,goal):
    if T<0:return 0
    ds=digits(T,m)
    zero=(0,)*len(mod)
    def add(a,b):return tuple((x+y)%q for x,y,q in zip(a,b,mod))
    dp=[{zero:1}]
    for _ in range(m):
        row={}
        for a,v in dp[-1].items():
            for w in weights:
                b=add(a,w);row[b]=row.get(b,0)+v
        dp.append(row)
    cur=zero;ans=0
    for i,d in enumerate(ds):
        for j in range(d):
            v=add(cur,weights[j]);need=tuple((g-z)%q for g,z,q in zip(goal,v,mod))
            ans+=dp[m-i-1].get(need,0)
        cur=add(cur,weights[d])
    return ans+(cur==goal)

def gate_counts(X):
    assert X>=8
    m=0;Q=1
    while Q<=2*(X+1):Q*=3;m+=1
    tau=(Q-1)//2
    def L(t):return 3*t-1-sum((0,2,1)[d] for d in digits(t,m))
    def R(t):return L(t+tau)-3*tau+2*m+2
    llo=upper(L,7,0,X+1);lhi=upper(L,X,0,X+1)
    rlo=upper(R,23,0,X);rhi=upper(R,3*X,0,X)
    lc=lambda T:count_prefix(T,m,((0,),(1,),(1,)),(2,),(1,))
    rc=lambda T:count_prefix(T+tau,m,((2,1),(0,0),(1,0)),(3,2),(2,1))
    a=lc(lhi)-lc(llo);b=rc(rhi)-rc(rlo);total=X//2-3
    return total,a,b,max(0,total-a-b)

if __name__=='__main__':
    for X in (8,10,30,100,1000,2000,10**6,10**18,10**100):
        print(X,gate_counts(X))
