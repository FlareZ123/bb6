"""Import successful artifact source/objects, preserving exact dependency identities.
Conflicting identities are never silently overwritten; incompatible modules and their
dependents are omitted from the reuse manifest and checked again from source.
"""
from pathlib import Path
import hashlib, json, shutil, sys
out = Path(sys.argv[1]).resolve()
source = out/'imports'
obj = out/'reusable'
source.mkdir(parents=True, exist_ok=True)
obj.mkdir(parents=True, exist_ok=True)
resume = '--resume' in sys.argv[2:]
artifacts = [Path(x).resolve() for x in sys.argv[2:] if x != '--resume']
assert artifacts
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def manifest_at(p):
    paths = list(p.rglob('manifest.json'))
    assert len(paths)==1, paths
    return paths[0]
selected = {}
omitted = []
revisions = set()
base = None
if resume:
    base = json.loads((out/'reusable.json').read_text())
    assert base['schema_version'] == 1
    selected = {m['module']:m for m in base['modules']}
    revisions.update(base.get('source_revisions',[]))
for artifact in artifacts:
    path=manifest_at(artifact)
    root=path.parent
    doc=json.loads(path.read_text())
    assert doc['schema_version']==1
    if base is None: base=doc
    else:
        assert doc['lean_version']==base['lean_version']
        assert doc['lean_binary']['sha256']==base['lean_binary']['sha256']
    revisions.update(doc.get('source_revisions',[]))
    for p in (root/'imports').rglob('*.lean'):
        dst=source/p.relative_to(root/'imports')
        dst.parent.mkdir(parents=True,exist_ok=True)
        if dst.exists(): assert digest(dst)==digest(p), (dst,p)
        else: shutil.copy2(p,dst)
    pending = {m['module']:m for m in doc['modules']}
    for name,m in list(pending.items()):
        p=root/'build'/m['olean_path']
        assert p.is_file() and digest(p)==m['olean_sha256'], p
    # A module may be reused only with the very same imported object identities.
    accepted=set()
    while pending:
        ready=[n for n,m in pending.items() if all(dep not in pending for dep in m['project_imports'])]
        assert ready, 'cyclic import graph'
        for name in ready:
            m=pending.pop(name)
            if name in selected:
                if selected[name]['module_identity_sha256']==m['module_identity_sha256']:
                    accepted.add(name)
                else: omitted.append(name)
                continue
            if any(dep not in accepted for dep in m['project_imports']):
                omitted.append(name)
                continue
            src=root/'build'/m['olean_path']
            dst=obj/m['olean_path']
            dst.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(src,dst)
            selected[name]=m
            accepted.add(name)
base=dict(base)
base['modules']=list(selected.values())
base['source_revisions']=sorted(revisions)
(out/'reusable.json').write_text(json.dumps(base,indent=2)+'\n')
print(f'Reusable objects: {len(selected)}; incompatible artifact entries: {len(omitted)}')
print('Incompatible entries:', sorted(set(omitted)))
