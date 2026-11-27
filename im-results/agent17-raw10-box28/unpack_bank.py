#!/usr/bin/env python3
"""Replay compact selected bank seeds and exact late witnesses, not discovery."""
import base64,gzip,struct,sys,json
from pathlib import Path
from cuts import fixed_for,targets_for
src,out=Path(sys.argv[1]),Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
a=gzip.decompress(base64.b64decode(src.read_text()));pos=0
def get(fmt):
    global pos
    z=struct.unpack_from('<'+fmt,a,pos);pos+=struct.calcsize('<'+fmt)
    return z[0] if len(z)==1 else z
assert a[:4]==b'B28\x01';pos=4
d,v=get('BB');fixed=fixed_for(d,v);free=targets_for(d)
def row():
    p=get('I');t=fixed[:]
    for k,i in enumerate(free):t[i]=((p>>(5*k))&31)-1
    assert p>>30==0 and all(-1<=x<=24 for x in t) and t.count(0)==1
    return t
seeds=[]
for j in range(get('I')):
    t=row();k=chr(get('B'))
    if k=='n':p=[k,get('B')]
    elif k=='r':
        ps=[]
        for i in range(2):
            b,c=get('BB');ps.append([b>>4,b&15,c>>4,c&15])
        p=[k,ps,get('H')]
    elif k=='m':
        ps=[]
        for i in range(2):
            z=get('H');ps.append([z&31,(z>>5)&31,z>>10])
        p=[k,ps]
    else:raise ValueError(k)
    seeds.append([t,p])
summary={}
for t in free:
    long=[];mx=(0,None)
    for i in range(get('I')):
        r=row();assert r[t]==0
        k=get('B')
        if k==0:
            n,s=get('HB');z=['halt',n,s]
            if n+1>mx[0]:mx=(n+1,r)
        elif k==1:z=['hole',get('H')]
        else:
            assert k in (2,3)
            n,p,direction,b=get('HH?h');z=['cycle' if k==2 else 'side',n,p,direction,b]
        long.append([r,z])
    (out/f'late{t}.json').write_text(json.dumps(long))
    (out/f'rle{t}.txt').write_text('')
    res=[row() for i in range(get('I'))]
    assert all(r[t]==0 for r in res)
    summary[t]={'open_rows':res,'open_count':len(res),'late_max_halt':mx}
assert pos==len(a)
(out/'summary.json').write_text(json.dumps(summary,indent=2))
(out/'seeds.json').write_text(json.dumps(seeds))
print('cut',d,v,'selected seeds',len(seeds),'residual leaves',sum(s['open_count'] for s in summary.values()),flush=True)
