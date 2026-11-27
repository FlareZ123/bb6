"""Candidate discovery only; independent kernel checking is required."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
from collections import Counter
from multiprocessing import Pool
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'im-results/agent6-raw139-e0-zeroRC'))
from reproduce import basic, hard
PARENT=[7,24,11,24,14,24,24,16,22,11,24,24]
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
def partition(work):
    work.mkdir(parents=True,exist_ok=True)
    s=(ROOT/'im-results/agent48-raw139-e0-0re/replay.cpp').read_text()
    s=s.replace('for(int i=t-1;i>=0;i--)','for(int i=t-1;i>=max(0,t-120);i--)')
    for c in ('<','>'):
        s=s.replace('if((a.b[C/64]^b.b[C/64]) && i'+c+'C/64)return false;','')
    cpp=work/'partition.cpp';cpp.write_text(s)
    exe=work/'partition';subprocess.run(['g++','-O3','-std=c++17',str(cpp),'-o',str(exe)],check=True)
    out=work/'partition.json'
    with out.open('wb') as f:
        subprocess.run([str(exe),'250','2',*map(str,PARENT)],stdout=f,check=True)
    p=json.loads(out.read_text());t=p['tree']
    assert t[:3]==['split',8,10] and len(t[3])==24
    assert p['counts']['open']==len(p['open'])
    assert sum(p['counts'][x] for x in ('cycle','last','far','open'))==23*p['counts']['split']+1
    def count(t):
        c=Counter([t[0]])
        if t[0]=='split':
            for child in t[3]:c.update(count(child))
        return c
    print('Partition:',p['counts'],'SHA256:',hashlib.sha256(out.read_bytes()).hexdigest(),flush=True)
    print('F0=0LA:',dict(count(t[3][0])),flush=True)
    (work/'open.json').write_text(json.dumps(p['open']))
    cpp.unlink();exe.unlink()
def ngram(t,exe):
    s=''.join('---' if a==24 else str((a>>1)&1)+('R' if a&1 else 'L')+chr(65+(a>>2)) for a in t)
    for k in (6,10,14,18,21,24,28):
        try:
            r=subprocess.run([str(exe),str(k)],input='0 '+s+'\n',text=True,capture_output=True,timeout=12)
        except subprocess.TimeoutExpired:
            continue
        if r.returncode==0:
            fields=r.stdout.split()
            assert int(fields[1])==k and len(fields)==6
            return ['ngram',k,int(fields[2]),r.stdout.strip()]
    return ['open']
def candidate(job):
    i,t,exe=job
    _,r=basic((i,t))
    if r[0]=='open':_,r=hard((i,t))
    if r[0]=='open':r=ngram(t,exe)
    if r[0]=='late':
        n,s=r[1:];assert t[s]==24
        if t.count(24)==1:return ['last',n,s]
        kids=[]
        for a in ORDER:
            u=t.copy();u[s]=a
            kids.append(candidate((i,u,exe)))
        return ['split',n,s,kids]
    if r[0]=='open':return ['open',t]
    return r
def solve_job(j):
    return j[0],candidate(j)
def shard(work,group,groups):
    ts=json.loads((work/'open.json').read_text())
    out=work/f'group-{group:02d}';out.mkdir(parents=True,exist_ok=True)
    exe=out/'ngram'
    subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'im-results/agent47-raw111-cut/ngram_sparse.cpp'),'-o',str(exe)],check=True)
    jobs=[(i,t,exe) for i,t in enumerate(ts) if i%groups==group]
    with Pool(2) as pool,(out/'recipes.jsonl').open('w') as f:
        for n,(i,r) in enumerate(pool.imap_unordered(solve_job,jobs,chunksize=1),1):
            f.write(json.dumps([i,r],separators=(',',':'))+'\n');f.flush()
            if n%100==0:print(group,n,'/',len(jobs),flush=True)
    exe.unlink()
    print('Group complete:',group,len(jobs),flush=True)
def aggregate(work,groups):
    ts=json.loads((work/'open.json').read_text())
    records={}
    for group in range(groups):
        for line in (work/f'group-{group:02d}'/'recipes.jsonl').read_text().splitlines():
            i,r=json.loads(line);assert i%groups==group and i not in records
            records[i]=r
    assert set(records)==set(range(len(ts)))
    counts=Counter();unresolved=[];maxquery=0
    def walk(i,t,r,path=()):
        nonlocal maxquery
        counts[r[0]]+=1
        if r[0] in ('last','split'):
            n,s=r[1:3];assert t[s]==24
            maxquery=max(maxquery,n)
            if r[0]=='last':assert t.count(24)==1
            else:
                assert len(r[3])==24
                for a,ch in zip(ORDER,r[3]):
                    u=t.copy();u[s]=a;walk(i,u,ch,path+((s,a),))
        if r[0]=='open':
            assert r[1]==t;unresolved.append({'id':i,'path':path,'table':t})
    for i,r in sorted(records.items()):walk(i,ts[i],r)
    p=json.loads((work/'partition.json').read_text())
    summary={'counts':dict(counts),'unresolved':unresolved,'max_observed_weighted_query_bound':max(maxquery,p['counts']['maxquery'])+6,'initial_counts':p['counts']}
    (work/'summary.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('mode',choices=['partition','shard','aggregate']);a.add_argument('work',type=Path);a.add_argument('--group',type=int,default=0);a.add_argument('--groups',type=int,default=12);args=a.parse_args()
    if args.mode=='partition':partition(args.work)
    elif args.mode=='shard':shard(args.work,args.group,args.groups)
    else:aggregate(args.work,args.groups)
