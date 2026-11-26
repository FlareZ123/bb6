"""Reproduce the entire 301-leaf frontier without a parameter search.
Run box17.py and box17_ngram.py first. Generator outputs are untrusted.
"""
import json
from lag_rle import run
from box17_ngram import check
from box17 import DOM
# Keys are A1,D1,F0,F1; values are lag, cap, modulus, retained runs.
PARAMS={
(10,-1,20,3):(1,2,4,3),(24,-1,20,2):(1,1,4,2),(4,-1,19,17):(1,1,1,2),
(-1,22,16,3):(1,4,1,5),(-1,22,16,2):(1,2,1,2),
(22,-1,3,13):(1,2,4,3),(22,-1,3,5):(1,2,4,3),(20,-1,3,10):(1,3,4,3),
(10,-1,3,24):(1,2,4,3),(10,-1,3,22):(1,2,4,4),(10,-1,3,21):(1,2,4,4),
(10,-1,3,19):(1,3,4,3),(10,-1,3,18):(1,2,4,3),(10,-1,3,17):(1,2,4,4),
(10,-1,3,15):(1,2,4,4),(10,-1,3,13):(1,2,4,3),(10,-1,3,11):(1,1,4,3),
(10,-1,3,10):(1,3,4,3),(10,-1,3,9):(1,2,4,4),(10,-1,3,8):(1,2,4,4),
(10,-1,3,7):(1,2,4,4),(10,-1,3,6):(1,2,4,4),(10,-1,3,5):(1,2,4,3),
(10,-1,3,4):(1,2,4,3),(10,-1,3,3):(1,2,4,3),(10,-1,3,2):(1,2,4,4),
(1,19,3,-1):(1,4,1,7),(1,2,3,-1):(1,8,3,8),(1,10,3,-1):(1,8,3,8),
(9,-1,3,6):(6,3,4,5),(9,-1,3,22):(6,3,4,5),
(21,-1,3,5):(4,4,3,7),(21,-1,3,13):(4,4,3,7)
}
HALTS={(5,21,3,-1):(11,323),(9,-1,3,10):(7,7011),(9,-1,3,21):(7,3209),(4,-1,19,5):(7,538)}
R1=(9,-1,3,23)
def first_hole(t,limit):
    L=R=q=0
    for n in range(limit+1):
        s=2*q+(R&1);v=t[s]
        if v<=0:return s,n
        v-=1;w=v//2%2
        if v%2:L=(L<<1)|w;R>>=1
        else:R=(((R>>1)<<1)|w)<<1|(L&1);L>>=1
        q=v//4
    return None
def main():
    data=json.load(open('ngram.json'));certs=[];late=[];r1=None
    for t in data['fail']:
        key=tuple(t[i] for i in (1,7,10,11))
        if key in PARAMS:
            p=PARAMS[key];c=run(t,(p,p),35000)
            assert c is not None,(t,p)
            certs.append([t,c])
        elif key in HALTS:
            s,n=HALTS[key];assert t.count(-1)==1 and first_hole(t,n)==(s,n)
            late.append([t,s,n])
        elif key==R1:r1=t
        else:
            assert key==(21,-1,3,9)
            c=check(t,18,20000);assert c is not None
            data['certs'].append([t,c])
    assert len(certs)==33 and len(data['certs'])==263 and len(late)==4 and r1
    json.dump({'rle':certs,'ngram':data['certs'],'late':late,'r1':r1},open('finished.json','w'))
    print('33 RLE + 263 ngram + 4 late last-hole branches + r1 = 301')
if __name__=='__main__':main()
