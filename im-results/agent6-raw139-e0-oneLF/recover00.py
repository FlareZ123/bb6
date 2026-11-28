"""Recover the sole unfinished OneLF root using the original generated sources.

All certificates are checked at the original source revision and Lean version.
The plan changes scheduling only; no machine, proof term or bound is rewritten.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = "OLFRoot00"
THEOREM = "BB6.Agent6E0OneLF.cOLFRoot00"
BOUND = 90794

def read(p):
    return json.loads(p.read_text())

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def write(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2) + "\n")

def entries(m):
    out = {e["module"]: e for e in m["modules"]}
    assert len(out) == len(m["modules"])
    return out

def same_build(a, b):
    for key in ("proof_source_revision", "lean_version"):
        assert a[key] == b[key], key
    assert a["lean_binary"]["sha256"] == b["lean_binary"]["sha256"]

def merge_one(base, pool, dest, mf, build):
    m = read(mf)
    same_build(base, m)
    for name, e in entries(m).items():
        rel = Path(e["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        src = build / rel
        assert digest(src) == e["olean_sha256"], name
        if name in pool:
            assert pool[name]["module_identity_sha256"] == e["module_identity_sha256"], name
        else:
            target = dest / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, target)
            pool[name] = e

def plan(w):
    base = read(w / "core.json")
    core = entries(base)
    files = {p.stem: p for p in (w / "imports").glob("*.lean")}
    graph = {}
    visiting = set()
    def visit(n):
        if n in core or n.split(".")[0] in {"Init", "Lean", "Std"}:
            return
        if n in graph:
            return
        assert n not in visiting and n in files, n
        visiting.add(n)
        deps = []
        for line in files[n].read_text().splitlines():
            if re.match(r"^\s*import\s+", line):
                deps.extend(line.split()[1:])
        for d in deps:
            visit(d)
        graph[n] = set(d for d in deps if d in graph)
        visiting.remove(n)
    visit(ROOT)
    tree = {n for n in graph if n.startswith(ROOT)}
    other = set(graph) - tree
    assert len(graph[ROOT]) == 1
    top = next(iter(graph[ROOT]))
    assert top in tree
    def closure(n, allowed):
        result = set()
        def walk(x):
            if x not in allowed or x in result:
                return
            result.add(x)
            for y in graph[x]:
                walk(y)
        walk(n)
        return result
    def schedule(roots, allowed, k):
        assert roots
        closures = {n: closure(n, allowed) for n in roots}
        sizes = {n: sum(files[x].stat().st_size for x in c) for n,c in closures.items()}
        buckets = [[] for _ in range(min(k,len(roots)))]
        loads = [0] * len(buckets)
        for n in sorted(roots, key=lambda n: (-sizes[n], n)):
            i = min(range(len(buckets)), key=lambda i: (loads[i], i))
            buckets[i].append(n)
            loads[i] += max(1,sizes[n])
        assert all(buckets)
        return buckets
    block_roots = other - set().union(*(graph[n] & other for n in other))
    assert set().union(*(closure(n, other) for n in block_roots)) == other
    tree_roots = graph[top] & tree
    expected = tree - {ROOT,top}
    assert set().union(*(closure(n, tree) for n in tree_roots)) == expected
    assert all(not (graph[n] & tree) for n in other)
    obj = {
        "pin": base["proof_source_revision"],
        "top": top,
        "block": schedule(block_roots, other, 24),
        "tree": schedule(tree_roots, tree, 16),
        "expected_block": sorted(other),
        "expected_tree": sorted(expected),
        "source_sha256": {n: digest(files[n]) for n in graph},
    }
    write(w / "recovery-plan.json",obj)
    print("plan:", len(other), "automata modules;",len(expected),"tree modules")
    if "GITHUB_OUTPUT" in os.environ:
        with open(os.environ["GITHUB_OUTPUT"],"a") as f:
            print("pin="+obj["pin"],file=f)
            for phase in ("block","tree"):
                print(phase+"_matrix="+json.dumps({"group":list(range(len(obj[phase]))))},separators=(",",":")),file=f)

def check_plan(w):
    p = read(w / "recovery-plan.json")
    assert p["pin"] == read(w / "core.json")["proof_source_revision"]
    assert subprocess.check_output(["git","rev-parse","HEAD"], text=True).strip() == p["pin"]
    for n,h in p["source_sha256"].items():
        assert digest(w / "imports" / (n+".lean")) == h, n
    return p

def compile_group(w, phase, group):
    p = check_plan(w)
    dst = w / ("cut-"+phase+"-"+str(group))
    dst.mkdir(parents=True,exist_ok=True)
    if phase == "block":
        roots = p[phase][group]
        mf, build = w/"core.json", w/"core"
    elif phase == "tree":
        roots = p[phase][group]
        mf, build = w/"block-pool.json", w/"block-pool"
    else:
        assert phase == "root" and group == 0
        roots = [ROOT]
        mf, build = w/"tree-pool.json", w/"tree-pool"
        dst = w/"shards"/"raw139-e0-oneLF-root00-certified"
        dst.mkdir(parents=True,exist_ok=True)
    args = [sys.executable,"tools/lean_compile_closure.py",
            *[str(w/"imports"/(n+".lean")) for n in roots],
            "--source-root",str(w/"imports"),"--workdir",str(dst/"build"),
            "--jobs","2","--precompiled-manifest",str(mf),
            "--precompiled-dir",str(build),"--manifest",str(dst/"manifest.json"),
            "--label","OneLF00-"+phase+"-"+str(group)]
    if phase == "root":
        args += ["--theorem",THEOREM,"--weighted-bound",str(BOUND)]
    log = dst/"check.log"
    with log.open("w") as f:
        proc = subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        for line in proc.stdout:
            print(line,end="",flush=True)
            f.write(line)
        assert proc.wait() == 0
    text = log.read_text()
    assert not re.search(r"sorryAx|ofReduceBool",text)
    result = read(dst/"manifest.json")
    same_build(read(w/"core.json"),result)
    assert set(roots) <= entries(result).keys()
    if phase == "root":
        assert THEOREM in text
        assert "propext" in text and "Quot.sound" in text

def merge_phase(w, phase):
    p = check_plan(w)
    base = read(w/"core.json")
    dest = w/(phase+"-pool")
    dest.mkdir(exist_ok=False)
    pool = {}
    if phase == "block":
        merge_one(base,pool,dest,w/"core.json",w/"core")
    else:
        assert phase == "tree"
        merge_one(base,pool,dest,w/"block-pool.json",w/"block-pool")
    cuts = w/("cuts-"+phase)
    expected = {"raw139-oneLF00-"+phase+"-"+str(i) for i in range(len(p[phase]))}
    assert {d.name for d in cuts.iterdir() if d.is_dir()} == expected
    for i,roots in enumerate(p[phase]):
        d = cuts/("raw139-oneLF00-"+phase+"-"+str(i))
        m = read(d/"manifest.json")
        assert set(roots) <= entries(m).keys()
        merge_one(base,pool,dest,d/"manifest.json",d/"build")
    assert set(p["expected_"+phase]) <= pool.keys()
    merged = dict(base)
    merged["modules"] = sorted(pool.values(),key=lambda e:e["module"])
    write(w/(phase+"-pool.json"),merged)
    print("merged",phase,len(pool),"source-checked objects")

if __name__ == "__main__":
    command,w,*args = sys.argv[1:]
    w = Path(w)
    if command == "plan":
        plan(w)
    elif command == "compile":
        compile_group(w,args[0],int(args[1]))
    elif command == "merge":
        merge_phase(w,args[0])
    else:
        raise ValueError(command)
