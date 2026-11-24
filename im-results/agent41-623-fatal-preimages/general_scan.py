"""Exact symbolic search over ten normalized leading coefficients."""
from fitfamilies import cert, match
from near_power import initial, stats
from symbolic_exclusion import verify

def search():
    successes=[]
    for A in range(2,32,2):
        if A%3==0:
            continue
        count=0
        deepest=(0,0,0)
        for R in (30,31):
            for off in range(-100,102,2):
                try:
                    cs=[cert(initial(A*3**r+off)) for r in (R,R+2,R+4)]
                    if any(c is None for c in cs):
                        continue
                    t=match(cs,R,coeff=A)
                    if t is None:
                        continue
                    nodes,dep=verify(t,R,off,coeff=A)
                except (AssertionError,RecursionError):
                    continue
                count+=1
                successes.append((A,R,off,nodes,dep,t))
                deepest=max(deepest,(dep,nodes,off))
        print(A,count,deepest,flush=True)
        stats.cache_clear()
    print('TOTAL',len(successes),sum(x[3] for x in successes))
    print('MAX',max((x[:5] for x in successes),key=lambda x:x[4]))
    return successes

if __name__=='__main__':
    search()
