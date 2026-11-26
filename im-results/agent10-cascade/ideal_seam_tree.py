#!/usr/bin/env python3
from collections import Counter,defaultdict
from fractions import Fraction
import sys,time

def ideal(g):
    # Root upper seam at offset 0. Omit the infinite self-even loop.
    stack=[(Fraction(8),0,0,True)]
    cnt=Counter(); mass=defaultdict(Fraction); maxa=0
    while stack:
        x,D,A,root=stack.pop()
        if not root:
            cnt[D]+=1;mass[D]+=Fraction(1,2*3**(A-1));maxa=max(maxa,A)
        for delta in range(0,g-D+1):
            for a in range(0 if delta==0 or delta==1 and not root else 1,2*delta+1):
                if root and a==0:continue
                y=Fraction(1<<(a+delta+1),3**a)*x-8
                if 4<y<8:
                    stack.append((y,D+delta,A+a,False))
    return cnt,mass,maxa

if __name__=='__main__':
    for g in map(int,sys.argv[1:] or [8,12,16]):
        t=time.perf_counter();cnt,mass,a=ideal(g)
        print('g',g,'nodes',sum(cnt.values()),'maxA',a,'sum mass',sum(mass.values()),'decimal',float(sum(mass.values())),'sec',time.perf_counter()-t)
        print([(i,cnt[i],str(mass[i])) for i in range(1,g+1)])
