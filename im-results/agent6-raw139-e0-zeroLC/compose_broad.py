"""Compose accepted broad root cuts and the independently accepted exact D0RC child."""
import hashlib,json,pathlib,shutil,subprocess,sys
work=pathlib.Path(sys.argv[1]).resolve()
run=sys.argv[2]
recovery=sys.argv[3] if len(sys.argv)>3 else ''
recovered_codes={0,1,3,7} if recovery else set()
out=work/'parent';build=out/'build';imports=work/'imports'
build.mkdir(parents=True,exist_ok=True);imports.mkdir(parents=True,exist_ok=True)
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules={};base=None
codes=[0,1,2,3,5,6,7,11,20,21,22,23]
cuts=[]
for c in codes:
 root=work/'shards'/f'raw139-zeroLC-branch-{c}-certified'
 src=work/'sources'/f'raw139-zeroLC-branch-{c}-sources'/'imports'
 cuts.append((root,src,f'BB6.Agent6ZeroLCBroad.C{c:02d}.cZLCBroadRoot{c:02d}',80377,recovery if c in recovered_codes else run))
cuts.append((work/'child9',work/'child9'/'imports','BB6.Agent6E0ZeroLCD0RC.cRaw139E0ZeroLCD0RC',616,'45942651816'))
for root,src,theorem,bound,expected_run in cuts:
 m=json.loads((root/'manifest.json').read_text())
 assert str(m['workflow']['run_id'])==expected_run,(root,m['workflow'])
 assert m['claim']['theorem']==theorem and m['claim']['weighted_bound']==bound,(root,m['claim'])
 if base is None:base=m
 assert m['lean_version']==base['lean_version'] and m['lean_binary']['sha256']==base['lean_binary']['sha256']
 for e in m['modules']:
  name=e['module'];obj=root/'build'/e['olean_path']
  assert digest(obj)==e['olean_sha256'],name
  if name in modules:assert modules[name]['module_identity_sha256']==e['module_identity_sha256'],name
  else:
   modules[name]=e;dst=build/e['olean_path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(obj,dst)
  source=src/f'{name}.lean'
  if source.exists():
   assert digest(source)==e['source_sha256'],name
   dst=imports/source.name
   if dst.exists():assert digest(dst)==e['source_sha256'],name
   else:shutil.copy2(source,dst)
for name,e in modules.items():assert all(dep in modules for dep in e['project_imports']),name
merged=out/'merged.json'
merged.write_text(json.dumps(dict(base,modules=list(modules.values()),module_count=len(modules)),indent=2))
subprocess.run(['python3','im-results/agent6-raw139-e0-zeroLC/broad_exact.py','final',str(imports)],check=True)
cmd=['python3','tools/lean_compile_closure.py',str(imports/'E0ZeroLCCover.lean'),
     '--source-root',str(imports),'--precompiled-manifest',str(merged),'--precompiled-dir',str(build),
     '--workdir','/tmp/a6-zeroLC-parent','--jobs','2','--manifest',str(out/'manifest.json'),
     '--label','raw139-e0-zeroLC-parent','--theorem','BB6.Agent6E0ZeroLCExact.weighted',
     '--parent-table','[7,24,11,24,14,24,24,16,8,11,24,24]','--weighted-bound','80377',
     '--artifact-name','raw139-e0-zeroLC-parent-certified']
with (out/'log').open('w') as f:
 p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 for line in p.stdout:print(line,end='',flush=True);f.write(line)
 assert p.wait()==0
log=(out/'log').read_text()
assert 'sorryAx' not in log and 'ofReduceBool' not in log
assert "'BB6.Agent6E0ZeroLCExact.weighted' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for f in pathlib.Path('/tmp/a6-zeroLC-parent').rglob('*.olean'):
 dst=build/f.relative_to('/tmp/a6-zeroLC-parent');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dst)
print('Exact parent compiled; reused',len(modules),'dependency modules')
