#!/usr/bin/env python3
"""Discovery (not a proof) of the ten remaining canonical first-hole branches.
Reuses existing exact side-scan, FAR and ngram/run closure algorithms.
No re-enumeration of 0RA/0RB. The eventual Lean proof must check every witness.
"""
import sys,subprocess,json,time
from pathlib import Path
from itertools import product
repo,branch,out=Path(sys.argv[1]).resolve(),sys.argv[2],Path(sys.argv[3]).resolve()
raw=repo/'im-results/agent32-raw42'
sys.path.insert(0,str(raw))
from run42 import discover
out.mkdir(parents=True,exist_ok=True)
assert branch in ('0LA','0LE','0RE','1LA','1LB','1LC','1LE','1RA','1RB','1RE')
def cmd(args,inp=None,stdout=None,stderr=None,timeout=None):
    return subprocess.run([str(x) for x in args],input=inp,text=True,cwd=out,
                          stdout=stdout,stderr=stderr,timeout=timeout,check=True)
for name,path in [
    ('enumerate',repo/'im-results/agent32-linear-side-cycle/enumerate_tnf.cpp'),
    ('farbank',repo/'im-results/agent19-raw40-cut/farbank.cpp'),
    ('ngram',raw/'search42_ngram.cpp'),('late',raw/'search42_late.cpp')]:
    cmd(['g++','-O3','-std=c++20',path,'-o',out/name])
parent='1RB---_1RC'+branch+'_0RD---_1LD0LB_------_------'
cmd([out/'enumerate',parent,500])
opens=[x.replace('_','') for x in (out/'open.txt').read_text().splitlines()]
assert len(set(opens))==len(opens)
known={}
def mv(i):return str(i//12)+('R' if i%12>=6 else 'L')+chr(65+i%6)
for row in json.loads((raw/'wide_growth_recipes.json').read_text()):
    p=''.join('---' if x<0 else mv(x) for x in row['table'])
    known[p]='Wide:'+row['id']
base='1RB---1RC---0RD---1LD0LB------------'
for b,v,name in [('1LB','0LD','OneLBZeroLD'),('1LB','0RD','OneLBZeroRD'),('1LC','1LC','OneLCOneLC')]:
    p=base[:9]+b+base[12:15]+v+base[18:]
    known[p]='Nested:'+name
rem=set(range(len(opens)))
def remaining_input():
    return ''.join(f'{i} {opens[i]}\n' for i in sorted(rem))
def stage(name,exe,extra=(),timeout=180):
    try:
        with (out/(name+'.txt')).open('w') as f, (out/(name+'.log')).open('w') as log:
            cmd([out/exe,*extra],remaining_input(),f,log,timeout)
    except subprocess.TimeoutExpired:
        print(name,'time cap reached; retaining completed witnesses',flush=True)
    rows=(out/(name+'.txt')).read_text().splitlines()
    found={int(row.split()[0]) for row in rows if row.strip()}
    assert found<=rem
    rem.difference_update(found)
    print(name,len(found),'remain',len(rem),flush=True)
    return len(found)
with (out/'known.txt').open('w') as f:
    for i in sorted(rem):
        if opens[i] in known:print(i,known[opens[i]],file=f)
    ids={i for i in rem if opens[i] in known}
rem-=ids
stats={'known':len(ids)}
print('branch',branch,'open',len(opens),'known',len(ids),flush=True)
stats['far5']=stage('far5','farbank',[5],240)
stats['late']=stage('late','late',[100000],60)
stats['ngram']=stage('ngram','ngram',[],120)
# Cheap run/block summaries first; bounded per-branch budget.
params=[]
for k,t,m in product(range(1,5),range(1,4),range(1,5)):
    params.append(('run',(k,t,t,m,m)))
for k,width,t,m in product(range(1,3),range(2,7),range(1,4),range(1,4)):
    for align in range(width):params.append(('block',(k,width,t,m,align)))
params.sort(key=lambda x:(x[1][0]*x[1][1]*(x[1][2]+x[1][3]),len(x[1]),x[1]))
solved=set()
deadline=time.monotonic()+100
with (out/'run.txt').open('w') as f:
    for i in sorted(rem):
        if time.monotonic()>deadline:break
        for kind,p in params:
            if time.monotonic()>deadline:break
            try:_,n,_,_=discover(opens[i],kind,p,3000)
            except ValueError:continue
            print(i,opens[i],kind,*p,file=f,flush=True)
            solved.add(i);break
rem-=solved
stats['run']=len(solved)
print('run',len(solved),'remain',len(rem),flush=True)
# Size-six exhaustive FAR is useful only on the small hard tail; time bounded.
stats['far6']=stage('far6','farbank',[6],120) if rem and len(rem)<=40 else 0
if not (out/'far6.txt').exists():(out/'far6.txt').write_text('')
(out/'hard.txt').write_text(remaining_input())
stats['hard']=len(rem)
assert sum(stats.values())==len(opens)
(out/'summary.json').write_text(json.dumps({'branch':branch,'open':len(opens),'partition':stats},indent=2)+'\n')
print('SUMMARY',json.dumps({'branch':branch,'open':len(opens),'partition':stats}),flush=True)
for i in sorted(rem)[:200]:print('HARD',branch,i,opens[i],flush=True)
