#!/usr/bin/env python3
"""Build canonical audit manifests in parallel, checking each generated module."""
import concurrent.futures, json, os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
dirs=[pathlib.Path(x).resolve() for x in sys.argv[1:]]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[root,pathlib.Path(os.environ['LEAN_DEPS']),*dirs])))
lean=os.environ.get('LEAN','lean')
workers=int(os.environ.get('WORKERS','4'))
jobs={}
for d in dirs:
    for m,deps in json.loads((d/'manifest.json').read_text()):
        assert m not in jobs,m
        jobs[m]=(d,set(deps))
def check(m):
    d,_=jobs[m]
    p=subprocess.run([lean,'-j1','-o',str(d/(m+'.olean')),str(d/(m+'.lean'))],cwd=d,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (d/(m+'.log')).write_text(p.stdout)
    print(m,p.returncode,p.stdout,flush=True)
    if p.returncode or 'sorryAx' in p.stdout:raise RuntimeError(m)
    return m
done=set()
running={}
pending=set(jobs)
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
    while pending or running:
        ready=[m for m in jobs if m in pending and jobs[m][1]<=done]
        for m in ready[:max(0,workers-len(running))]:
            pending.remove(m)
            running[pool.submit(check,m)]=m
        if not running:raise RuntimeError('manifest DAG stalled')
        fs,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
        for f in fs:
            done.add(f.result())
            del running[f]
print('All',len(done),'audit modules compiled.')
