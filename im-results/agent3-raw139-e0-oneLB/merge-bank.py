#!/usr/bin/env python3
"""Consume accepted exact-source proof banks, keeping import identities intact."""
import hashlib,json,pathlib,shutil,sys
out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
imports=pathlib.Path(sys.argv[2]);imports.mkdir(parents=True,exist_ok=True)
records={};sources={};base=None;revisions=set();claims=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for directory in map(pathlib.Path,sys.argv[3:]):
    paths=([directory/"manifest.json"] if (directory/"manifest.json").is_file() else
           [p for p in directory.rglob("manifest.json") if "reuse" not in p.relative_to(directory).parts])
    assert len(paths)==1,paths
    p=paths[0];m=json.loads(p.read_text());assert m["schema_version"]==1
    if base is None:base=m
    else:
        assert m["lean_version"]==base["lean_version"]
        assert m["lean_binary"]["sha256"]==base["lean_binary"]["sha256"]
    revisions.update(m["source_revisions"]);claims.append(m["claim"])
    candidates={}
    for src in directory.rglob("*.lean"):
        candidates.setdefault(src.stem,[]).append(src)
    for row in m["modules"]:
        mod=row["module"];digest=row["source_sha256"]
        if mod in sources:
            assert sources[mod]==digest,("incompatible source",mod)
        else:
            sources[mod]=digest
            srcpath=pathlib.Path(row["source_path"])
            if not (srcpath.is_file() and sha(srcpath)==digest):
                src=next((s for s in candidates.get(mod.split(".")[-1],[]) if sha(s)==digest),None)
                assert src is not None,("missing producer source",mod,srcpath)
                dst=imports/(mod+".lean")
                if dst.exists():assert sha(dst)==digest,("source mismatch",mod)
                else:shutil.copy2(src,dst)
        if mod in records:
            if row["module_identity_sha256"]!=records[mod]["module_identity_sha256"]:
                print("Shared source with different object identity; incompatible descendants recompile:",mod)
            continue
        rel=pathlib.Path(row["olean_path"]);assert not rel.is_absolute() and ".." not in rel.parts
        src=p.parent/"build"/rel
        assert src.is_file() and sha(src)==row["olean_sha256"],("missing/wrong object",mod,src)
        dst=out/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
        records[mod]=row
assert base is not None
base["modules"]=list(records.values());base["module_count"]=len(records)
base["source_revisions"]=sorted(revisions);base["label"]="OneLB accepted producer bank"
(out/"manifest.json").write_text(json.dumps(base))
(out/"claims.json").write_text(json.dumps(claims))
print("Merged",len(records),"accepted object candidates")
