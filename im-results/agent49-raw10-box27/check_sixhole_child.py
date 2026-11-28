"""Generate and check a complete six-hole child, using existing original-source Lean modules.
Requires the existing dependency closure compiled on LEAN_PATH.
Usage: python check_sixhole_child.py 12 7 2 BUILD_DIR --jobs 3
"""
import argparse,hashlib,os,subprocess,sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from generate_sixhole_child import discover,emit
from compact_join import compact
def check(d,s,v,out,jobs):
    out=Path(out).resolve();out.mkdir(parents=True,exist_ok=True)
    tree,B=discover(d,s,v);emit(d,s,v,tree,B,out)
    prefix=f'Box27Child{d:02d}V{v:02d}'
    source=out/(prefix+'Source.lean');compact(source)
    env=dict(os.environ);env['LEAN_PATH']=str(out)+os.pathsep+env.get('LEAN_PATH','.')
    def build(f):
        r=subprocess.run(['lean','-o',str(f.with_suffix('.olean')),str(f)],cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode or 'sorryAx' in r.stdout:raise RuntimeError(str(f)+'\n'+r.stdout)
        print(f.name,r.stdout.strip(),flush=True)
    build(out/(prefix+'Core.lean'))
    with ThreadPoolExecutor(max_workers=jobs) as pool:list(pool.map(build,sorted(out.glob(prefix+'Part*.lean'))))
    build(source)
    files=sorted(out.glob(prefix+'*.lean'))
    print('source SHA256',hashlib.sha256(b''.join(f.name.encode()+b'\0'+f.read_bytes() for f in files)).hexdigest())
if __name__=='__main__':
    ap=argparse.ArgumentParser()
    for k in ('d','s','v'):ap.add_argument(k,type=int)
    ap.add_argument('out');ap.add_argument('--jobs',type=int,default=3)
    a=ap.parse_args();check(a.d,a.s,a.v,a.out,a.jobs)
