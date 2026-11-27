"""Compile a dependency-closed Lean module set against the accepted shared core."""
import os,re,subprocess,sys,pathlib,time
src=pathlib.Path(sys.argv[1]).resolve();core=pathlib.Path(sys.argv[2]).resolve();lean=sys.argv[3];logs=src.parent/'logs';logs.mkdir(exist_ok=True)
files={p.stem:p for p in src.glob('*.lean')}
deps={k:set(re.findall(r'^import ([\w.]+)\s*$',p.read_text(),re.M))&files.keys() for k,p in files.items()}
env=dict(os.environ,LEAN_PATH=f'{core}:{src}')
done=set();pending=set(files);t0=time.time()
while pending:
 ready=sorted((k for k in pending if deps[k]<=done),key=lambda k:('Block' not in k,files[k].stat().st_size,k))
 if not ready:raise RuntimeError('dependency cycle')
 for k in ready:
  path=src/(k+'.olean');log=logs/(k+'.log')
  if path.exists() and path.stat().st_mtime>=files[k].stat().st_mtime and all(path.stat().st_mtime>=(src/(d+'.olean')).stat().st_mtime for d in deps[k]):
   done.add(k);pending.remove(k);continue
  start=time.time()
  with log.open('w') as f:
   proc=subprocess.run([lean,'-j','1','-o',str(path),files[k].name],cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT)
  if proc.returncode:
   print('FAIL',k,proc.returncode,log.read_text()[-10000:],flush=True);sys.exit(proc.returncode)
  done.add(k);pending.remove(k)
  print('OK',len(done),len(files),k,round(time.time()-start,2),round(time.time()-t0,2),flush=True)
print('COMPLETE',len(done),round(time.time()-t0,2),flush=True)
