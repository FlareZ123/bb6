from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import subprocess,json,sys,os,time,re
build=Path(os.environ.get('A3_BUILD','generated')).resolve();work=Path(__file__).resolve().parent;logs=work/'compile-logs';logs.mkdir(exist_ok=True)
lean=os.environ.get('LEAN','lean');env=dict(os.environ,LEAN_PATH=str(build));tasks={}
for b in sys.argv[2:]:
 for name,deps in json.load(open(work/f'modules{b}.json')):tasks[name]=set(deps)
done={n for n in tasks if (build/(n+'.olean')).exists() and (build/(n+'.olean')).stat().st_mtime >= (build/(n+'.lean')).stat().st_mtime}
start=time.monotonic();failed=[]
def run(n):
 t=time.monotonic();path=logs/(n+'.log')
 with path.open('w') as f:
  p=subprocess.run([lean,'-o',n+'.olean',n+'.lean'],cwd=build,env=env,stdout=f,stderr=subprocess.STDOUT)
 data=path.read_text();ok=p.returncode==0 and not re.search(r'\bsorryAx\b|\bnative_decide\b|\bLean\.ofReduceBool\b',data)
 return n,ok,time.monotonic()-t
with ThreadPoolExecutor(max_workers=int(sys.argv[1])) as pool:
 pending={}
 while len(done)<len(tasks):
  ready=[n for n,d in tasks.items() if n not in done and n not in pending.values() and n not in failed and all(x in done or (x not in tasks and (build/(x+'.olean')).exists()) for x in d)]
  for n in ready[:int(sys.argv[1])-len(pending)]:pending[pool.submit(run,n)]=n
  if not pending:break
  for f in wait(pending,return_when=FIRST_COMPLETED)[0]:
   n,ok,dt=f.result();pending.pop(f)
   if ok:done.add(n)
   else:failed.append(n);print((logs/(n+'.log')).read_text()[-4000:],flush=True)
   print('OK' if ok else 'FAIL',n,round(dt,2),len(done),'/',len(tasks),flush=True)
print('FINISHED',len(done),'/',len(tasks),'failed',failed,'elapsed',time.monotonic()-start,flush=True)
sys.exit(len(done)!=len(tasks))
