"""Reproduce the candidate partition; no output of this search is a Lean Cover."""
import json, hashlib, pathlib, subprocess, sys
from collections import Counter
from multiprocessing import Pool
ROOT=pathlib.Path(__file__).resolve().parents[2]
WORK=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(WORK.parent/'agent6-raw139-e0-zeroRC'))
from reproduce import basic, hard, child
PARENT=[7,24,11,24,14,24,24,16,15,11,24,24]
def check(name,hash):
    assert hashlib.sha256((WORK/name).read_bytes()).hexdigest()==hash
def dump(name,records):
    (WORK/name).write_text(''.join(json.dumps([i,r])+'\n' for i,r in sorted(records.items())))
def partition():
    s=(ROOT/'im-results/agent48-raw139-e0-0re/replay.cpp').read_text()
    s=s.replace('for(int i=t-1;i>=0;i--)','for(int i=t-1;i>=max(0,t-120);i--)')
    s=s.replace('if((a.b[C/64]^b.b[C/64]) && i<C/64)return false;','')
    s=s.replace('if((a.b[C/64]^b.b[C/64]) && i>C/64)return false;','')
    cpp=WORK/'partition.cpp';cpp.write_text(s)
    exe=WORK/'partition';subprocess.run(['g++','-O3','-std=c++17',str(cpp),'-o',str(exe)],check=True)
    with (WORK/'partition.json').open('wb') as f:
        subprocess.run([str(exe),'250','2',*map(str,PARENT)],stdout=f,check=True)
    check('partition.json','fa1996190fa9418d2026a0aae7a421a0d7ff5d09c6198db498ffe65409231e8e')
    p=json.loads((WORK/'partition.json').read_text())
    assert p['counts']==dict(cycle=429405,last=128403,split=26980,far=55075,open=7658,maxquery=250)
    return p
def run():
    p=partition();ts=p['open']
    with Pool(4) as pool:
        recipes=dict(pool.imap_unordered(basic,enumerate(ts),chunksize=16))
        dump('basic.jsonl',recipes)
        for i,r in pool.imap_unordered(hard,[(i,ts[i]) for i,r in recipes.items() if r[0]=='open']):
            recipes[i]=r
        assert Counter(r[0] for r in recipes.values())==dict(block=7592,late=54,cycle=10,open=2)
        assert sorted(i for i,r in recipes.items() if r[0]=='open')==[2959,4267]
        dump('recipes.jsonl',recipes)
        check('recipes.jsonl','20694e71bf4e1623839e2657976ea25f5092378e4d9daf599b1cc8a10124cceb')
        jobs=[]
        for i,v in sorted(recipes.items()):
            if v[0]=='late' and ts[i].count(24)>1:
                for a in range(24):
                    u=ts[i].copy();u[v[2]]=a;jobs.append(((i,a),u))
        assert len(jobs)==24
        children=dict(pool.imap_unordered(child,jobs))
        assert Counter(r[0] for r in children.values())==dict(block=22,late=2)
        dump('children.jsonl',children)
        check('children.jsonl','bb1ba4adfd969cc2619e3add87e6ea647711c439a9aad4c5323446721de7ac92')
if __name__=='__main__':run()
