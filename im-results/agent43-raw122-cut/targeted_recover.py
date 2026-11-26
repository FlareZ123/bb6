#!/usr/bin/env python3
"""Artifact-backed compilation of only missing raw122 shards."""
from pathlib import Path
import os,re,shutil,subprocess,sys,json,hashlib
from raw122_patch import patch
base=Path(__file__).resolve().parent
work=Path('/tmp/a43-target');work.mkdir(exist_ok=True)
for f in Path('/tmp/a43-core').rglob('*.olean'):
    if f.name.startswith('Raw122') and f.name!='Raw122Base.olean':continue
    dst=work/f.name
    if dst.exists():assert dst.read_bytes()==f.read_bytes(),f
    else:shutil.copy2(f,dst)
for f in Path('/tmp/a43-source').rglob('*.lean'):
    shutil.copy2(f,work/f.name)
shutil.copy2(base/'Raw122TailGrowth.lean',work/'Raw122TailGrowth.lean')
patch(work)
env=dict(os.environ,LEAN_PATH=str(work));built=[]
def compile(m):
    if (work/(m+'.olean')).exists():return
    f=work/(m+'.lean');assert f.exists(),m
    for dep in re.findall(r'^import\s+(\S+)',f.read_text(),re.M):
        if dep.startswith(('Lean.','Std.','Init.')):continue
        compile(dep)
    print('compile',m,flush=True)
    subprocess.run(['lean','-o',m+'.olean',m+'.lean'],cwd=work,env=env,check=True)
    built.append(m)
branch,first,end=map(int,sys.argv[1:4])
for j in range(first,end):
    m=f'Raw122Kid{branch:02}_{j:02}'
    f=work/(m+'.lean')
    # Agent29's literal-table certificates also cover the older planned leaves.
    # Keep the original recovery route available for any unmatched shard.
    patched = False
    if branch in {0,4,5,12,13,16,17,23}:
        sys.path.insert(0,str(base.parent/'agent29-raw122-run'))
        from patch import patch as patch_run
        patched = patch_run(work,branch,j)
    if not patched and (branch,j) in {(12,4),(12,12),(12,13),(12,16),(23,6),(23,12),(23,16)}:
        from patch_planned import patch as patch_planned
        patch_planned(work,branch,j)
    if not (work/(m+'.olean')).exists() and f.stat().st_size>15000 and ' : PartialAudit := .closed (' in f.read_text():
        # Generate independently checked smaller subtrees instead of a single
        # massive reduction. Keep the original exported module and theorem.
        stage=work/(m+'-split');stage.mkdir(exist_ok=True)
        mods=subprocess.check_output([sys.executable,str(base/'split_grouped.py'),str(f),str(stage),'5000'],text=True).splitlines()
        assert mods[-1]==m
        for n in mods:shutil.copy2(stage/(n+'.lean'),work/(n+'.lean'))
    compile(m)
    audit=work/'A43CheckAxioms.lean'
    audit.write_text(f'import {m}\n#print axioms BB6.Agent43Raw122.kid{branch:02}_{j:02}_checked\n')
    text=subprocess.check_output(['lean',audit.name],cwd=work,env=env,text=True)
    print(text,flush=True)
    assert 'sorryAx' not in text and 'native_decide' not in text and 'Lean.ofReduceBool' not in text
out=Path('/tmp/a43-target-out');out.mkdir(exist_ok=True)
for m in built:
    for ext in ('.lean','.olean'):shutil.copy2(work/(m+ext),out/(m+ext))
(out/'metadata.json').write_text(json.dumps({'source_artifact':15043765926,'core_artifact':15012394320,'branch':branch,'first':first,'end':end,'modules':built,'files':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in out.iterdir()}},indent=2))
