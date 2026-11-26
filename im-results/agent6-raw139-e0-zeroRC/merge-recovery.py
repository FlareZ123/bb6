"""Merge exact independent cuts, close missing roots, and invoke original composer."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
work=Path(sys.argv[1]).resolve()
core=json.loads((work/'core.json').read_text())
pool=work/'recovery-pool';pool.mkdir(exist_ok=True)
entries={}
for i in range(16):
    cut=work/'cuts'/f'raw139-zeroRC-cut-{i:02d}'
    m=json.loads((cut/'manifest.json').read_text())
    assert m['proof_source_revision']==core['proof_source_revision']
    assert m['lean_version']==core['lean_version'] and m['lean_binary']['sha256']==core['lean_binary']['sha256']
    for n in (work/'recovery-groups'/f'{i:02d}.txt').read_text().splitlines():
        assert any(e['module']==n for e in m['modules']),n
    for e in m['modules']:
        src=cut/'build'/e['olean_path']
        assert hashlib.sha256(src.read_bytes()).hexdigest()==e['olean_sha256'],e['module']
        if e['module'] in entries:
            assert entries[e['module']]['module_identity_sha256']==e['module_identity_sha256'],e['module']
        else:
            entries[e['module']]=e
            dest=pool/e['olean_path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
manifest=work/'recovery-pool.json'
manifest.write_text(json.dumps(dict(core,modules=list(entries.values()),module_count=len(entries))))
for root in (0,7,12,18):
    name=f'raw139-e0-zeroRC-root{root:02d}-certified'
    shard=work/'shards'/name;shard.mkdir(parents=True,exist_ok=True)
    build=shard/'build'
    theorem=f'BB6.Agent6E0ZeroRC.cZRCRoot{root:02d}'
    cmd=['python3','tools/lean_compile_closure.py',str(work/f'imports/ZRCRoot{root:02d}.lean'),
         '--source-root',str(work/'imports'),'--precompiled-manifest',str(manifest),
         '--precompiled-dir',str(pool),'--workdir',str(build),'--jobs','2',
         '--manifest',str(shard/'manifest.json'),'--label',name,'--theorem',theorem,
         '--weighted-bound','1673363']
    with (shard/'log').open('w') as f:
        p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        for line in p.stdout:print(line,end='',flush=True);f.write(line)
        assert p.wait()==0
    log=(shard/'log').read_text()
    assert 'sorryAx' not in log and 'ofReduceBool' not in log
    assert f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
subprocess.run(['python3','im-results/agent6-raw139-e0-zeroRC/compose.py',str(work)],check=True)
