import json
from pathlib import Path
from collections import defaultdict

def parse(table):
    return [None if c=='---' else (int(c[0]),1 if c[1]=='R' else -1,ord(c[2])-65) for r in table.split('_') for c in (r[:3],r[3:])]

def replay(tr,t,h,q,n):
    t=set(t); edges=defaultdict(list); count=defaultdict(int)
    for _ in range(n):
        move=tr[2*q+(h in t)]; assert move is not None
        b,d,q=move
        if b:t.add(h)
        else:t.discard(h)
        count[h]+=1;edges[min(h,h+d)].append((d,q));h+=d
    return t,h,q,edges,count

def right_word(t,h):
    assert all(x>h for x in t)
    return ''.join('1' if x in t else '0' for x in range(h+1,max(t,default=h)+1))

def normalize(w,cuts,h,extra):
    result=[]; fixed=''; p=0
    for a,b in cuts:
        a-=h;b-=h
        assert 0<=p<=a<b<=len(w)
        block=w[a:b];fixed+=w[p:a]+block*(1+extra);tail=''
        while fixed and fixed[-1]==block[-1]:
            x=fixed[-1];fixed=fixed[:-1];tail=x+tail;block=x+block[:-1]
        result.extend((fixed,block));fixed=tail;p=b
    result.append(fixed+w[p:]);return result

def check(v):
    tr=parse(v['table']);t,h,q,_,_=replay(tr,set(),0,0,v['entry'])
    assert (h,q)==(v['entryHead'],0); w=right_word(t,h)
    t={x-h for x in t};u,d,q,edges,cnt=replay(tr,t,0,0,v['period'])
    assert (d,q)==(v['shift'],0);f=right_word(u,d)
    cuts=v['cuts'];assert cuts and max(0,d)<cuts[0][0]
    assert all(a<b for a,b in cuts) and all(b<=c for (_,b),(c,_) in zip(cuts,cuts[1:]))
    assert all(edges[a]==edges[b] for a,b in cuts)
    assert normalize(w,cuts,0,1)==normalize(f,cuts,d,0)
    assert sum(cnt[x] for a,b in cuts for x in range(a+1,b+1))==v['increment']

if __name__=='__main__':
    data=json.loads(Path(__file__).with_name('bank.json').read_text())
    for k,v in data.items():check(v);print(k,'PASS')
    print(len(data),'finite-premise certificates passed')
