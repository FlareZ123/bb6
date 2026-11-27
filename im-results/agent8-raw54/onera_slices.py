"""Partition oneRA generated dependency closure; merge compatible object manifests.

No theorem is asserted by a slice or merge. The final exact-source closure
checks all reused source/import/object identities and the final Cover.
"""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

def digest(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def plan(directory, out, count, stem='Raw54OneRA', root='Raw54OneRACut'):
    files={p.stem:p for p in directory.glob(stem+"*.lean")}
    graph={m: [d for d in re.findall(r"^import (\S+)$", p.read_text(), re.M) if d in files] for m,p in files.items()}
    memo={}
    def closure(m):
        if m not in memo:
            memo[m]={m}.union(*(closure(d) for d in graph[m]))
        return memo[m]
    # Size-based balancing is a scheduling heuristic only.
    weight={m: int((files[m].stat().st_size+8000)**1.15) for m in files}
    def cost(ms):
        return sum(weight[m] for m in ms)
    full=closure(root)
    target=max(1,cost(full)//(2*count))
    frontier=set()
    def cut(m):
        if m.startswith(stem+"Shard") and graph[m] and cost(closure(m))>target and any(d.startswith(stem+"Shard") for d in graph[m]):
            for d in graph[m]:
                cut(d)
        else:
            frontier.add(m)
    for m in graph[root]:
        cut(m)
    if stem == 'Raw54OneRA':
        # Do not independently compile a root already in another frontier closure.
        frontier={m for m in frontier if not any(m != n and m in closure(n) for n in frontier)}
    bins=[[] for _ in range(count)]
    deps=[set() for _ in bins]
    for m in sorted(frontier,key=lambda m:(-cost(closure(m)),m)):
        i=min(range(count),key=lambda i:(cost(deps[i]|closure(m)),i))
        bins[i].append(m)
        deps[i].update(closure(m))
    assert all(bins), bins
    out.mkdir(parents=True,exist_ok=True)
    for i,roots in enumerate(bins):
        (out/f"{i}.txt").write_text("".join(f"{m}.lean\n" for m in sorted(roots)))
        print(i,len(roots),len(deps[i]),cost(deps[i]),flush=True)

def merge(slices,out,count,artifact='raw54-onera'):
    manifests=[]
    candidates={}
    for i in range(count):
        folder=slices/f"{artifact}-slice-{i}"
        manifest=json.loads((folder/"manifest.json").read_text())
        assert manifest["schema_version"]==1
        manifests.append(manifest)
        for e in manifest["modules"]:
            path=Path(e["olean_path"])
            assert not path.is_absolute() and ".." not in path.parts
            f=folder/path
            assert f.is_file(), f
            assert hashlib.sha256(f.read_bytes()).hexdigest()==e["olean_sha256"], f
            candidates.setdefault(e["module"],[]).append((e,f))
    base=manifests[0]
    for m in manifests:
        assert m["lean_version"]==base["lean_version"]
        assert m["lean_binary"]["sha256"]==base["lean_binary"]["sha256"]
        assert m["proof_source_revision"]==base["proof_source_revision"]
    standard=("Lean","Init","Std","Batteries","Mathlib","Cryptids","BusyBeaver")
    def is_standard(d):
        return any(d==p or d.startswith(p+".") for p in standard)
    chosen={}
    skipped=set()
    unresolved=set(candidates)
    out.mkdir(parents=True,exist_ok=True)
    while unresolved:
        ready=sorted(m for m in unresolved if all(d not in unresolved for d in candidates[m][0][0]["project_imports"] if not is_standard(d)))
        assert ready, sorted(unresolved)
        for m in ready:
            for e,f in candidates[m]:
                graph=e["project_imports"]
                if any(not is_standard(d) and d not in chosen for d in graph):
                    continue
                deps=[{"module":d,"identity":f"standard:{base['lean_version']}:{d}" if is_standard(d) else chosen[d]["module_identity_sha256"]} for d in sorted(graph)]
                if digest(deps)!=e["import_closure_sha256"]:
                    continue
                payload={k:e[k] for k in ("module","source_sha256","project_imports","olean_sha256","import_closure_sha256")}
                if digest(payload)!=e["module_identity_sha256"]:
                    continue
                dst=out/e["olean_path"]
                dst.parent.mkdir(parents=True,exist_ok=True)
                shutil.copy2(f,dst)
                chosen[m]=e
                break
            if m not in chosen:
                skipped.add(m)
        unresolved.difference_update(ready)
    merged=dict(base,modules=[chosen[m] for m in sorted(chosen)],module_count=len(chosen),
                roots=[],claim={"theorem":None,"parent_table":None,"weighted_bound":None},
                artifact_name=None,label=f"{artifact} compatible slice objects",
                source_revisions=sorted({r for x in manifests for r in x["source_revisions"]}))
    (out/"manifest.json").write_text(json.dumps(merged,indent=2,sort_keys=True)+"\n")
    print("compatible objects",len(chosen),"omitted (recompile)",len(skipped))

if __name__=="__main__":
    mode,src,out,count,*extra=sys.argv[1:]
    (plan if mode=="plan" else merge)(Path(src),Path(out),int(count),*extra)
