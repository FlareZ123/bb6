"""Strictly compose the independent source-connected symbolic proof cuts."""
from pathlib import Path
import sys, json, hashlib, shutil
work=Path(sys.argv[1]).resolve()
core=json.loads((work/'core.json').read_text());out=work/'merged';out.mkdir(exist_ok=True)
entries={};groups=json.loads((work/'matrix.json').read_text())['group']
def add(m,folder):
    assert m['proof_source_revision']==core['proof_source_revision']
    assert m['lean_version']==core['lean_version'] and m['lean_binary']['sha256']==core['lean_binary']['sha256']
    for e in m['modules']:
        p=folder/e['olean_path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==e['olean_sha256'],e['module']
        if e['module'] in entries:
            assert entries[e['module']]['module_identity_sha256']==e['module_identity_sha256'],e['module']
        else:
            entries[e['module']]=e
            dest=out/e['olean_path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
add(core,work/'core')
for g in groups:
    path=work/'shards'/('raw139-oneRF-trace-'+g);m=json.loads((path/'manifest.json').read_text())
    for name in (work/'groups'/f'{g}.txt').read_text().splitlines():
        assert any(e['module']==Path(name).stem for e in m['modules']),name
    add(m,path/'build')
manifest=dict(core,modules=list(entries.values()),module_count=len(entries));(work/'merged.json').write_text(json.dumps(manifest))
print('Merged',len(entries),'verified module identities across',len(groups),'trace cuts')
