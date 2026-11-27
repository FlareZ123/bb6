"""Merge independently compiled exact-root artifacts and check the parent theorem."""
import hashlib, json, pathlib, shutil, subprocess, sys
work=pathlib.Path(sys.argv[1]).resolve()
out=work/'parent'; build=out/'build';build.mkdir(parents=True,exist_ok=True)
digest=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
core=json.loads((work/'core.json').read_text())
modules={}
for root in range(24):
    shard=work/'shards'/f'raw139-e0-oneLF-root{root:02d}-certified'
    m=json.loads((shard/'manifest.json').read_text())
    assert m['proof_source_revision']==core['proof_source_revision']
    assert m['lean_version']==core['lean_version']
    assert m['lean_binary']['sha256']==core['lean_binary']['sha256']
    assert m['claim']['theorem']==f'BB6.Agent6E0OneLF.cOLFRoot{root:02d}'
    assert m['claim']['weighted_bound']==90794
    for e in m['modules']:
        name=e['module'];src=shard/'build'/e['olean_path']
        assert digest(src)==e['olean_sha256'],name
        if name in modules:
            assert modules[name]['module_identity_sha256']==e['module_identity_sha256'],name
            continue
        modules[name]=e
        dst=build/e['olean_path'];dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(src,dst)
manifest=dict(core,modules=list(modules.values()),module_count=len(modules))
merged=out/'merged.json';merged.write_text(json.dumps(manifest,indent=2))
cmd=['python3','tools/lean_compile_closure.py',str(work/'imports/E0OneLFCover.lean'),
     '--source-root',str(work/'imports'),'--precompiled-manifest',str(merged),
     '--precompiled-dir',str(build),'--workdir','/tmp/a6-oneLF-parent',
     '--jobs','2','--manifest',str(out/'manifest.json'),'--label','raw139-e0-oneLF-parent',
     '--theorem','BB6.Agent6E0OneLF.weighted','--parent-table','[7,24,11,24,14,24,24,16,22,11,24,24]',
     '--weighted-bound','90794','--artifact-name','raw139-e0-oneLF-parent-certified']
with (out/'log').open('w') as f:
    p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    for line in p.stdout:
        print(line,end='',flush=True);f.write(line)
    assert p.wait()==0
log=(out/'log').read_text()
assert 'sorryAx' not in log and 'ofReduceBool' not in log
assert "'BB6.Agent6E0OneLF.weighted' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for f in pathlib.Path('/tmp/a6-oneLF-parent').rglob('*.olean'):
    dst=build/f.relative_to('/tmp/a6-oneLF-parent')
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dst)
print('Exact parent Cover compiled; merged',len(modules),'dependency modules')
