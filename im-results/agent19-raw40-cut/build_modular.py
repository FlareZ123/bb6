#!/usr/bin/env python3
"""Compile a generated DAG with bounded concurrent Lean processes, resuming existing oleans."""
import os,sys,subprocess,json,pathlib,concurrent.futures,time
root=pathlib.Path(__file__).resolve().parent
lean=os.environ.get('LEAN','lean')
workers=int(os.environ.get('WORKERS','2'))
rounds=list(map(int,sys.argv[1:]));jobs={};finished=set();roots={};exact={}
for n in rounds:
    path=root/f'round{n}'/'shards-input'/'shards'
    for m,deps in json.loads((path/'manifest.json').read_text()):
        jobs[(n,m)]=(path,{(n,d) for d in deps});roots[n]=m
    p=f'Raw40Round{n}Pump';env=dict(os.environ,LEAN_PATH=f'{root}:{root}/deps')
    if not (root/f'{p}.olean').exists():subprocess.run([lean,'-j1','-o',p+'.olean',p+'.lean'],cwd=root,env=env,check=True)
    exact[(n,f'Raw40Round{n}Exact')]=(root,{(n,roots[n])})
    jobs.update(exact)
for key,(path,deps) in jobs.items():
    if (path/(key[1]+'.olean')).exists():finished.add(key)

def check(key):
    n,m=key;path,_=jobs[key];env=dict(os.environ,LEAN_PATH=f'{root}:{root}/deps:{root}/round{n}/shards-input/shards')
    start=time.monotonic();p=subprocess.run([lean,'-j1','-o',m+'.olean',m+'.lean'],cwd=path,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    print(f'{n} {m} {p.returncode} {time.monotonic()-start:.2f}s',flush=True)
    if p.stdout:print(p.stdout,flush=True)
    if p.returncode:raise RuntimeError((n,m,p.returncode))
    if 'sorryAx' in p.stdout:raise RuntimeError((n,m,'sorryAx'))
    return key
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    pending=set(jobs)-finished;running={}
    while pending or running:
        ready=sorted((k for k in pending if jobs[k][1]<=finished),key=lambda x:(rounds.index(x[0]),x[1]))
        for k in ready[:max(0,workers-len(running))]:
            pending.remove(k);running[pool.submit(check,k)]=k
        if not running:raise RuntimeError('DAG stalled')
        done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for f in done:
            k=running.pop(f);finished.add(f.result())
            if k in exact:print('ROUND',k[0],'DONE',flush=True)
print('ALL DONE',flush=True)
