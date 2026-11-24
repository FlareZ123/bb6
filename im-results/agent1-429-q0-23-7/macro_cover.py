from collections import Counter
from time import perf_counter
import sys
D = [(0,3,0),(1,5,6),(4,4,18),(5,6,32)]

def dead(k,p,y):
    if not k:
        return False
    for d,l,c in D:
        q = y+d*p+c
        if q%16 == 0 and not dead(k-1,p+l,q//16):
            return False
    return True

def cover(N,cap=100):
    st = [(0,0)]
    leaves = Counter()
    nodes = maxe = 0
    bad = []
    while st:
        e,r = st.pop()
        nodes += 1
        maxe = max(maxe,e)
        if r >= N:
            leaves["empty"] += 1
            continue
        if (e%4 == 3 or e == cap) and dead(min((e+1)//4,8*r+5),24*r+22,6*r+4):
            leaves["cut"] += 1
            continue
        if e == cap:
            bad.append(r)
            continue
        st.append((e+1,r+2**e))
        st.append((e+1,r))
    return nodes,maxe,leaves,len(bad),bad[:10]

if __name__ == "__main__":
    for a in sys.argv[1:]:
        N = int(a)
        t = perf_counter()
        print(N,cover(N),perf_counter()-t,flush=True)
