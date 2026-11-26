import json,itertools
from box16 import DOM
from lag_rle import run

def trace(t,limit=20000):
    if all(v>0 for v in t):return ('total',)
    L=R=q=h=0
    for n in range(limit+1):
        s=2*q+(R&1);v=t[s]
        if v<=0:return ('hole' if v<0 else 'halt',n,s)
        if n==limit:return ('open',n,L.bit_length(),R.bit_length(),h)
        v-=1;w=v//2%2
        if v%2:L=(L<<1)|w;R>>=1;h+=1
        else:R=(((R>>1)<<1)|w)<<1|(L&1);L>>=1;h-=1
        q=v//4

def main():
    ng=json.load(open('ngram16.json'));stack=[tuple(t) for t in ng['fail']];certs=[];leaves=[];failed=[]
    options=sorted(itertools.product([0,1,2,3,4,5,6],[1,2,3,4],[1,2,3,4],[2,3,4,5,6]),key=lambda x:(x[1]+x[2])*x[3]+2*x[0])
    while stack:
        t=stack.pop();r=trace(t)
        if r[0]=='hole' and t.count(-1)>1:
            s=r[2];stack.extend(t[:s]+(v,)+t[s+1:] for v in DOM[s]);continue
        if r[0] in ('hole','halt','total'):leaves.append([t,r]);continue
        for p in options:
            c=run(t,(p,p),12000)
            if c is not None:certs.append([t,c]);break
        else:failed.append(t)
    assert not failed and len(certs)==38 and len(leaves)==6
    json.dump({'leaves':leaves,'certs':certs,'fail':failed,'pending':stack},open('finish16.json','w'))
    print('DONE',len(leaves),len(certs),len(failed))
if __name__=='__main__':main()
