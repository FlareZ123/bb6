"""Exact finite carry-set comparison. Set deduplication preserves emptiness."""
for n in range(14,10001,2):
    cs={(n+2)//2}
    for K in range(1,n+1):
        if n+K>=12*2**(n-K):
            print("survives wider test",n,K,len(cs))
            break
        if not cs:
            if 2*K+28>n:
                print("additional vs old criterion",n,K)
            break
        a=n+K+3
        cs={v//2 for c in cs for v in (c,c+a) if v%2==0}
