"""Incidence quotient adapted from Agent4's quotient.py.
Also turn a bit-window certificate into the same general stack format.
"""
import json
def valid(t,c):
    S={tuple(x) for x in c['states']}; E=c['edges']; P=c['pushes']
    assert (0,0,0) in S and all((0,0) in map(tuple,e[0]) for e in E)
    for s,l,r in S:
        v=t[s]-1;assert v>=0;w=v//2%2;d=1-v%2;z=[l,r];u=z[d];j=P[d][u][w];assert (w,u) in map(tuple,E[d][j])
        for b,k in E[1-d][z[1-d]]:
            ns=z[:];ns[d]=j;ns[1-d]=k;assert (2*(v//4)+b,*ns) in S
def compress(t,c):
    valid(t,c);S={tuple(x) for x in c['states']};E=[[set(map(tuple,es)) for es in side] for side in c['edges']];P=[list(map(list,side)) for side in c['pushes']]
    while True:
        prev=tuple(map(len,E))
        for d in (0,1):
            inc=[set() for _ in E[d]]
            for s,l,r in S:
                z=(l,r);inc[z[d]].add((s,z[1-d]))
            groups={};phi=[];reps=[]
            for i,x in enumerate(inc):
                key=frozenset(x)
                if key not in groups:groups[key]=len(reps);reps.append(i)
                phi.append(groups[key])
            if len(reps)==len(phi):continue
            es=[set() for _ in reps]
            for i,e in enumerate(E[d]):
                for b,j in e:es[phi[i]].add((b,phi[j]))
            E[d]=es;P[d]=[[phi[j] for j in P[d][i]] for i in reps];S={(s,phi[l] if d==0 else l,phi[r] if d==1 else r) for s,l,r in S}
        if prev==tuple(map(len,E)):break
    c={**c,'edges':[[sorted(es) for es in side] for side in E],'pushes':P,'states':sorted(S)};valid(t,c);return c
def convert(t,c):
    ks=[c.get('kl',c.get('k')),c.get('kr',c.get('k'))];S=[tuple(x) for x in c['states']];E=[];P=[];maps=[]
    for d in (0,1):
        k=ks[d];mask=(1<<k)-1;ed=dict(c['left' if d==0 else 'right']);nodes={0}|{x[d+1] for x in S}|set(ed)
        for x in list(nodes):
            for b in (0,1):
                if ed.get(x,0)&(1<<b):nodes.add((x>>1)|(b<<(k-1)))
        nodes=sorted(nodes);ids={x:i for i,x in enumerate(nodes)};maps.append(ids)
        E.append([[(x&1,ids[(x>>1)|(b<<(k-1))]) for b in (0,1) if ed.get(x,0)&(1<<b)] for x in nodes]);P.append([[ids.get(((x<<1)|w)&mask,0) for w in (0,1)] for x in nodes])
    ret={'edges':E,'pushes':P,'states':[(s,maps[0][l],maps[1][r]) for s,l,r in S]};valid(t,ret);return ret
def main():
    data=json.load(open('finished.json'));cs=data['rle']+[[t,convert(t,c)] for t,c in data['ngram']];out=[]
    for i,(t,c) in enumerate(cs):
        d=compress(t,c);out.append([t,d]);print(i,len(c['states']),len(d['states']),len(d['edges'][0]),len(d['edges'][1]),flush=True)
    json.dump(out,open('compressed.json','w'))
if __name__=='__main__':main()
