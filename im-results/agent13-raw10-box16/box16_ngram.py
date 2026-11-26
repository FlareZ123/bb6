from collections import defaultdict, Counter
import json
def check(t,k,cap=20000):
    mask=(1<<k)-1; shift=k-1
    todo=[(0,0,0)]; seen=set(todo); edges=[{0:1},{0:1}]; waiting=[defaultdict(list),defaultdict(list)]
    def add(s,l,r):
        x=(s,l,r)
        if x not in seen:
            if t[s]<=0:raise ValueError
            if len(seen)>=cap:raise OverflowError
            seen.add(x);todo.append(x)
    def pop(x,e):
        s,l,r=x;v=t[s]-1;q=v//4;w=v//2%2
        if v%2:add(2*q+(r&1),((l<<1)|w)&mask,(r>>1)|(e<<shift))
        else:add(2*q+(l&1),(l>>1)|(e<<shift),((r<<1)|w)&mask)
    def edge(d,x,e):
        old=edges[d].get(x,0)
        if old&(1<<e):return
        edges[d][x]=old|(1<<e)
        for y in waiting[d][x]:pop(y,e)
    try:
        for x in todo:
            s,l,r=x;v=t[s]-1
            if v<0:return None
            w=v//2%2;d=v%2;u,y=(l,r) if d else (r,l)
            edge(1-d,((u<<1)|w)&mask,u>>shift)
            waiting[d][y].append(x)
            bits=edges[d].get(y,0)
            for e in (0,1):
                if bits&(1<<e):pop(x,e)
    except (ValueError,OverflowError):return None
    return {'k':k,'left':sorted(edges[0].items()),'right':sorted(edges[1].items()),'states':sorted(seen)}
def main():
    src=json.load(open('box16.json'));opened=[t for t,res in src['leaves'] if res[0]=='open'];certs=[];fail=[]
    for t in opened:
        for k in range(1,17):
            c=check(t,k)
            if c is not None:certs.append([t,c]);break
        else:fail.append(t)
    print('solved',len(certs),'failed',len(fail),'k',Counter(c['k'] for t,c in certs))
    json.dump({'certs':certs,'fail':fail},open('ngram16.json','w'))
if __name__=='__main__':main()
