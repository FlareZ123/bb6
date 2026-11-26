"""Reproduce broad residual candidates using the census plus exact exception recipes.
Run in a scratch directory with broad_census output; use Python path to this dossier.
This is witness generation, not a formal certificate."""
from search import search_case
from blockcert import generate
from pathlib import Path
from multiprocessing import Pool
import json,sys
from collections import Counter
# Keyed by exact table, not by traversal order.
HARD={}
for line in (Path(__file__).parent/'hard-witnesses.md').read_text().splitlines():
    parts=[x.strip() for x in line.split('|')]
    if len(parts)!=6 or not parts[2].isdigit():continue
    tab=tuple(map(int,parts[3].split(',')))
    a=parts[4].split()
    HARD[tab]=[a[0],*[{'false':False,'true':True}.get(x,int(x) if x.lstrip('-').isdigit() else x) for x in a[1:]]]
assert len(HARD)==29
def task(job):
    name,i,p=job
    if tuple(p) in HARD:return name,i,p,HARD[tuple(p)]
    _,_,r=search_case(job)
    return name,i,p,r
def main():
    jobs=[]
    for path in sorted(Path('.').glob('raw139_e0_0LC_*_leaves.txt')):
        name=path.name.split('_')[3]
        if name=='0RC' or len(path.name.split('_'))!=5:continue
        for i,line in enumerate(path.read_text().splitlines()):
            _,_,_,t=line.split();jobs.append((name,i,list(map(int,t.split(',')))))
    assert len(jobs)==13323,len(jobs)
    counts=Counter();late=[]
    with open('broad_recipes.jsonl','w') as f,Pool(int(sys.argv[1]) if len(sys.argv)>1 else 4) as pool:
        for name,i,p,r in pool.imap_unordered(task,jobs):
            assert r[0]!='open',(name,i,p)
            if r[0]=='late' and p.count(24)>1:late.append((name,i,p,r))
            counts[r[0]]+=1;f.write(json.dumps([name,i,p,r])+'\n')
    assert len(late)==2
    Path('late_branch_recipes.jsonl').write_text('')
    for name,i,p,r in late:
        assert p[r[2]]==24
        for code in range(24):
            child=p.copy();child[r[2]]=code
            n=f'{name}_{i}'
            if n=='0LA_312' and code==9:
                c=generate(child,3,1,3,5,False,150000)
                assert c
                witness=['block',3,1,3,5,c['left_states'],c['right_nodes']]
            else:_,_,witness=search_case((n,code,child))
            assert witness[0]!='open',(n,code,child)
            assert witness[0]!='late' or child.count(24)==1
            with open('late_branch_recipes.jsonl','a') as f:f.write(json.dumps([n,code,child,witness])+'\n')
    print(counts,'two late expansions')
if __name__=='__main__':main()
