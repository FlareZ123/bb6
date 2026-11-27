#!/usr/bin/env python3
"""Merge already accepted proof artifacts; no new proof is claimed here."""
import hashlib,json,pathlib,shutil,sys
out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
records={};base=None;revisions=set()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for arg in sys.argv[2:]:
    directory=pathlib.Path(arg);m=json.loads((directory/'manifest.json').read_text())
    if base is None:base=m
    else:
        assert m["lean_version"]==base["lean_version"]
        assert m["lean_binary"]["sha256"]==base["lean_binary"]["sha256"]
    revisions.update(m["source_revisions"])
    for row in m["modules"]:
        mod=row["module"];rel=pathlib.Path(row["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        src=directory/"build"/rel
        assert sha(src)==row["olean_sha256"],(directory,mod)
        if mod in records:
            assert row["module_identity_sha256"]==records[mod]["module_identity_sha256"],mod
            continue
        dst=out/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst);records[mod]=row
assert base is not None
base["modules"]=list(records.values());base["module_count"]=len(records)
base["source_revisions"]=sorted(revisions);base["label"]="raw139-oneLA-merged-accepted"
(out/"manifest.json").write_text(json.dumps(base))
print("Accepted dependency-closed objects:",len(records))
