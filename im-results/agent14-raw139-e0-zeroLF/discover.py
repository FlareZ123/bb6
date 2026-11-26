"""Witness discovery; import the existing Agent48 blockcert implementation."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent48-raw139-f1-oneRA'))
from blockcert import generate
from multiprocessing import Pool
from itertools import product
import json, collections, subprocess, hashlib
PARAMS = [
 (2,1,1,1,False,False),(3,1,1,1,False,False),
 (2,1,1,2,False,True),(2,1,2,1,False,False),
 (2,1,1,2,False,False),(2,1,3,2,False,False),
 (3,1,2,2,False,False),(2,1,3,1,False,False),
 (2,1,5,2,False,False),(2,1,2,2,False,False),
 (2,1,3,4,False,False),(3,1,1,2,False,False),
 (2,1,3,3,False,True),
]
HARD=[]
def add(p):
    if p not in HARD:HARD.append(p)
for flip in [True,False]:
    for w in [2,3]:
        for phase,mod,runs in [(False,1,1),(False,1,2),(True,1,2),(False,2,1),(False,3,1),(False,2,2),(False,3,2),(True,2,2),(True,3,2),(False,5,1),(False,5,2),(True,1,3),(True,2,3),(True,3,3),(False,1,3),(False,2,3),(False,3,3),(False,1,4),(False,2,4),(False,3,4),(False,5,3),(True,1,4),(True,2,4),(True,3,4),(True,5,3),(True,5,4)]:
            add((w,1,mod,runs,flip,phase))
for w,cap,mod,runs,flip,phase in product([2,3],[1,2],[1,2,3,4,5,7],[1,2,3,4,5],[False,True],[False,True]):
    if phase and cap!=1:continue
    if w==3 and runs>=4 and mod>=4:continue
    add((w,cap,mod,runs,flip,phase))
def late(t,limit):
    q=h=0; ones=set()
    for n in range(limit+1):
        v=t[2*q+(h in ones)]
        if v==24:return n,2*q+(h in ones)
        if v&2:ones.add(h)
        else:ones.discard(h)
        q=v>>2;h+=1 if v&1 else -1
    return None
def block(i,t,params,limit):
    for p in params:
        try:c=generate(t,*p[:-1],phase=p[-1],event_limit=limit)
        except (AssertionError, KeyError, ValueError):continue
        if c:return [i,'block',list(p),c['left_states'],c['right_nodes']]
def first(item):
    i,t=item
    if t.count(24)==1:
        a=late(t,2000)
        if a:return [i,'late',*a]
    b=block(i,t,PARAMS,10000)
    if b:return b
    a=late(t,20000)
    if a:return [i,'late' if t.count(24)==1 else 'split',*a]
    return [i,'open']
def second(item):
    i,t=item
    return block(i,t,HARD,20000) or [i,'open']
def write(name,records):
    Path(name).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in sorted(records)))
    print(name,collections.Counter(r[1] for r in records))
def main():
    workers=int(sys.argv[1]) if len(sys.argv)>1 else 4
    src=Path(__file__).with_name('census.cpp')
    subprocess.run(['g++','-O3','-std=c++17',str(src),'-o','census'],check=True)
    subprocess.run(['g++','-O3','-std=c++17','-DEXTENDED',str(src),'-o','extended'],check=True)
    raw=subprocess.check_output([str(Path('census').resolve()),'20'])
    Path('zeroLF.txt').write_bytes(raw)
    print(raw.splitlines()[0].decode(),hashlib.sha256(raw).hexdigest())
    tables=[tuple(map(int,l.split(','))) for l in raw.decode().splitlines()[1:]]
    with Pool(workers) as pool:
        rec=list(pool.imap_unordered(first,enumerate(tables),chunksize=8))
    write('recipes.jsonl',rec)
    jobs={r[0]:tables[r[0]] for r in rec if r[1]=='open'}
    child_info={}
    for i,_,n,s in sorted(r for r in rec if r[1]=='split'):
        for v in range(24):
            child=list(tables[i]);child[s]=v
            j=len(tables)+len(child_info)
            child_info[j]=(i,n,s,v);jobs[j]=tuple(child)
    Path('children.json').write_text(json.dumps(child_info,sort_keys=True))
    inp=''.join(str(i)+' '+' '.join(map(str,t))+'\n' for i,t in sorted(jobs.items()))
    out=subprocess.run([str(Path('extended').resolve())],input=inp,text=True,capture_output=True,check=True).stdout
    Path('extended.txt').write_text(out)
    ext={int(line.split()[0]):line.split()[1:] for line in out.splitlines()}
    # In the observed census every late query here is a last-hole query.
    for i,r in ext.items():
        if r[0]=='hole':assert jobs[i].count(24)==1,(i,r)
    pending=[(i,jobs[i]) for i,r in ext.items() if r[0]=='open']
    print('extended',collections.Counter(r[0] for r in ext.values()))
    with Pool(workers) as pool:
        hard=list(pool.imap_unordered(second,pending,chunksize=1))
    write('hard.jsonl',hard)
    for i,kind,*_ in sorted(hard):
        if kind=='open':print(i,jobs[i])
if __name__=='__main__':main()
