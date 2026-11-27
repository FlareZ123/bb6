#!/usr/bin/env python3
"""Source-checked per-E0 deltas and exact all-E0 consumer for Raw56 pilot.
The trusted base is accepted artifact 15160313745. All new Lean modules are
compiled from source; merge uses exact identity and source/object hashes.
"""
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
from emit_root_aggregate_join import emit as emit_join
from prepare_root_aggregate import prepare,BOUND

ALLOWED={'propext','Classical.choice','Quot.sound'}
CHILDREN={'E10RD':[0,1,5,6,7,8,11,12,13,17,18,19,20,23],
          'E11LC':[0,1,5,6,7,8,11,12,13,17,18,19,20,22,23]}
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(p.read_text())
def write(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def axiom_gate(log,theorem):
    a=re.findall(r"'"+re.escape(theorem)+r"' depends on axioms: \[([^\]]*)\]",log)
    if a:
        assert len(a)==1 and set(x.strip() for x in a[0].split(',') if x.strip())<=ALLOWED,(theorem,a)
    else:assert f"'{theorem}' does not depend on any axioms" in log,theorem

def check_base(base,lean):
    m=read(base/'manifest.json');assert m['module_count']==747 and m['claim']['theorem']=='BB6.Agent1Raw56Root.sound19_closed'
    assert sha(lean)==m['lean_binary']['sha256']=='db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00'
    for item in m['modules']:assert sha(base/item['olean_path'])==item['olean_sha256'],item
    return sha(base/'manifest.json'),{p.stem for p in base.glob('*.olean')}

def compile_new(targets,paths,base,lean,out,done,jobs):
    sources={}
    for d in paths:
        for p in sorted(d.glob('*.lean')):
            assert p.stem not in sources or sha(p)==sha(sources[p.stem]),p
            sources[p.stem]=p
    def deps(p):return [l.split()[1] for l in p.read_text().splitlines() if l.startswith('import ')]
    pending=set()
    def visit(name):
        if name in done or name in pending:return
        pending.add(name)
        for dep in deps(sources[name]):visit(dep)
    for t in targets:visit(t)
    env={**os.environ,'LEAN_PATH':os.pathsep.join([str(out),str(base)])}
    records={}
    def build(name):
        src=sources[name];dst=out/(name+'.olean');start=time.monotonic()
        r=subprocess.run([str(lean),'-j1','-o',str(dst),src.name],cwd=src.parent,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (out/(name+'.log')).write_text(r.stdout)
        if r.returncode or 'sorryAx' in r.stdout or 'native_decide' in r.stdout:raise RuntimeError(f'{name}: {r.returncode}\n{r.stdout}')
        shutil.copyfile(src,out/(name+'.lean'))
        print(name,round(time.monotonic()-start,2),flush=True)
        if name in targets:print(r.stdout,flush=True)
        return name,{'source_sha256':sha(src),'olean_sha256':sha(dst),'imports':deps(src)}
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        active={}
        while pending or active:
            for name in sorted(pending):
                if len(active)>=jobs:break
                if set(deps(sources[name]))<=done:
                    active[pool.submit(build,name)]=name;pending.remove(name)
            if not active:raise RuntimeError(f'unsatisfied import graph {pending}')
            for f in concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED).done:
                name,r=f.result();del active[f];done.add(name);records[name]=r
    return records

def main():
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['shard','assemble']);ap.add_argument('--tag',choices=CHILDREN,required=True);ap.add_argument('--child',type=int);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--base',type=Path,required=True);ap.add_argument('--generated',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--inputs',type=Path);ap.add_argument('--lean',default='lean');ap.add_argument('--jobs',type=int,default=1);a=ap.parse_args()
    root,base,gen,out=map(Path.resolve,(a.root,a.base,a.generated,a.out));lean=Path(shutil.which(a.lean)).resolve();gen.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
    bsha,done=check_base(base,lean);meta={'tag':a.tag,'bound':BOUND,'base_manifest_sha256':bsha,'lean_sha256':sha(lean)}
    assert not list(out.glob('*.olean')),'output must be a fresh directory'
    if a.mode=='shard':
        assert a.child in CHILDREN[a.tag]
        prepare(a.tag,a.child,root,gen);name=f'{a.tag}C{a.child:02}';target='Raw56'+name+'All'
        records=compile_new([target],[gen/name,root,root/'rootgrowth'],base,lean,out,done,a.jobs)
        theorem=f'BB6.Agent4Raw56.{name}.all_quotient';axiom_gate((out/(target+'.log')).read_text(),theorem)
        write(out/'manifest.json',{**meta,'child':a.child,'theorem':theorem,'modules':records})
    else:
        assert a.inputs is not None;seen=set();records={}
        for d in sorted(a.inputs.resolve().iterdir()):
            m=read(d/'manifest.json');assert all(m[k]==v for k,v in meta.items()),d
            child=m['child'];assert child in CHILDREN[a.tag] and child not in seen,d;seen.add(child)
            name=f'{a.tag}C{child:02}';target='Raw56'+name+'All';theorem=f'BB6.Agent4Raw56.{name}.all_quotient'
            assert m['theorem']==theorem and target in m['modules'];axiom_gate((d/(target+'.log')).read_text(),theorem)
            for mod,item in m['modules'].items():
                assert mod not in done or mod in records,mod
                for ext,key in [('lean','source_sha256'),('olean','olean_sha256')]:
                    p=d/(mod+'.'+ext);assert sha(p)==item[key],p
                    q=out/p.name
                    if q.exists():assert sha(q)==item[key],q
                    else:shutil.copyfile(p,q)
                if mod in records:assert records[mod]==item,mod
                records[mod]=item
            done.update(m['modules']);shutil.copyfile(d/(target+'.log'),out/(target+'.log'))
        assert seen==set(CHILDREN[a.tag]),seen
        emit_join(a.tag,root,gen);target=f'Raw56Pilot{a.tag}All';records.update(compile_new([target],[gen],base,lean,out,done,a.jobs))
        theorem=f'BB6.Agent4Raw56Pilot{a.tag}.all_quotient';axiom_gate((out/(target+'.log')).read_text(),theorem)
        write(out/'manifest.json',{**meta,'children':sorted(seen),'theorem':theorem,'modules':records})
if __name__=='__main__':main()
