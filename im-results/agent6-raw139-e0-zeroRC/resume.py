"""Recover only the four unfinished ZeroRC subparts, preserving accepted modules.

The generator changes proof granularity, never the parent table, bound, move
order, or finite audit leaves. Each generated Cover is checked by Hybrid.sound.
Old accepted source/object identities remain untouched. Uncompiled partial
artifacts are quarantined; only a complete exact root/parent audit can accept.
"""
import ast
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

B = 1673363
NS = "BB6.Agent6E0ZeroRC"
ORDER = [4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
FAILED = {(8,0), (10,0), (10,2), (13,0)}
CHUNK = re.compile(r"(?ms)^set_option maxRecDepth 1000000\n.*?^end BB6\.Agent6E0ZeroRC\n")
IMP = re.compile(r"^import ([\w.]+)$", re.M)
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads(p.read_text())

def save(p, x):
    p.write_text(json.dumps(x, indent=2) + "\n")

def merge(core, entries, pool, manifest, build):
    m = load(manifest)
    for key in ("proof_source_revision", "lean_version"):
        assert m[key] == core[key], (manifest, key)
    assert m["lean_binary"]["sha256"] == core["lean_binary"]["sha256"], manifest
    for e in m["modules"]:
        n = e["module"]
        rel = Path(e["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        src = build/rel
        assert digest(src) == e["olean_sha256"], (manifest, n)
        if n in entries:
            assert entries[n]["module_identity_sha256"] == e["module_identity_sha256"], n
        else:
            dest = pool/rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dest)
            entries[n] = e

def split_list(s):
    stack, start, out = [], 0, []
    close = {")":"(", "]":"[", "⟩":"⟨", "}":"{"}
    for i, ch in enumerate(s):
        if ch in close.values():
            stack.append(ch)
        elif ch in close:
            assert stack and stack.pop() == close[ch], (i, s[:80])
        elif ch == "," and not stack:
            out.append(s[start:i].strip())
            start = i+1
    assert not stack
    out.append(s[start:].strip())
    return out

def parse_split(s):
    m = re.fullmatch(r"\.split (\d+) \((\d+),(true|false)\) \(byMove \[(.*)\]\)", s, re.S)
    assert m, s[:160]
    n,q,bit,body = m.groups()
    kids = split_list(body)
    assert len(kids) == 24, len(kids)
    return int(n), 2*int(q)+(bit=="true"), kids

def slot(i):
    return f"({i//2},{str(bool(i%2)).lower()})"

def declaration(head, name, table, term):
    return head + (
        f"def p{name} : PartialMachine := fromCodes {table}\n"
        f"def t{name} : Hybrid {B} := {term}\n"
        f"theorem c{name} : Cover (WeightedBound {B}) p{name} :=\n"
        f"  sound {B} p{name} t{name} (by decide +kernel) "
        f"(fromCodes_nohalt _) (by decide +kernel)\n"
        f"#print axioms c{name}\nend {NS}\n"
    )

def rewrite(out, module, blockmap):
    f = out/(module+".lean")
    source = f.read_text()
    outer = set(IMP.findall(source))
    bare = IMP.sub("", source)
    chunks = CHUNK.findall(bare)
    assert chunks and not CHUNK.sub("", bare).strip(), module
    names, imports = {}, []
    def put(mod, deps, body):
        dest = out/(mod+".lean")
        assert not dest.exists(), dest
        dest.write_text("".join("import "+x+"\n" for x in sorted(deps))+body)
    def blocks(s):
        return {blockmap[x] for x in re.findall(r"BB6\.Agent6E0ZeroRCBlocks\.H(\d+)\.ctr", s)}
    def decompose(head, name, table, audit, mod):
        # Every recursive call is a smaller exact child with a concrete table,
        # so repeated refine/fastCheck reductions no longer sit in one decide.
        if not audit.startswith(".split "):
            return ".closed ("+audit+")", {"Hybrid"}|blocks(audit)
        n,s,kids = parse_split(audit)
        assert table[s] == 24, (name, table, s)
        terms, deps = [], {"Hybrid"}
        for j,kid in enumerate(kids):
            t = table.copy(); t[s] = ORDER[j]
            if kid.startswith(".split "):
                cn = name+f"_cut{j:02d}"
                cm = mod+f"Cut{j:02d}"
                ct,cd = decompose(head, cn, t, kid, cm)
                put(cm, cd, declaration(head, cn, t, ct))
                deps.add(cm)
                terms.append(f".covered p{cn} c{cn}")
            else:
                deps.update(blocks(kid))
                terms.append(".closed ("+kid+")")
        return f".split {n} {slot(s)} (byHybridMove [\n"+",\n".join(terms)+"])", deps
    for i, chunk in enumerate(chunks):
        m = re.search(r"^def p(\w+) : PartialMachine := fromCodes (\[[^\n]+\])$", chunk, re.M)
        assert m, (module, i)
        name, raw = m.groups()
        table = ast.literal_eval(raw)
        assert len(table)==12 and all(isinstance(n,int) and 0<=n<=24 for n in table)
        prefix = f"def t{name} : Hybrid {B} := "
        start = chunk.index(prefix)+len(prefix)
        end = chunk.index(f"\ntheorem c{name}",start)
        term = chunk[start:end]
        head = chunk[:m.start()]
        mod = module+f"Decl{i:03d}"
        deps = outer | {names[x] for x in re.findall(r"\.covered p(\w+) c\1\b",term) if x in names}
        if term.startswith(".closed (.split ") and term.endswith(")"):
            term, deps = decompose(head, name, table, term[len(".closed ("):-1], mod)
            body = declaration(head, name, table, term)
        else:
            body = chunk
        put(mod, deps, body)
        names[name] = mod
        imports.append(mod)
    f.write_text("".join("import "+x+"\n" for x in imports))
    return len(chunks)

def prepare(work):
    out = work/"imports"
    core = load(work/"core.json")
    pool = work/"resume-pool"
    pool.mkdir(exist_ok=False)
    entries = {}
    merge(core,entries,pool,work/"core.json",work/"core")
    for cut in sorted((work/"cuts").iterdir()):
        if (cut/"manifest.json").is_file():
            merge(core,entries,pool,cut/"manifest.json",cut/"build")
    all_roots, expected = [], []
    for i in range(16):
        roots = (work/"recovery-groups"/f"{i:02d}.txt").read_text().splitlines()
        all_roots.extend(roots)
        expected.extend(root for j,root in enumerate(roots) if (i,j%4) in FAILED)
    missing = sorted(set(all_roots)-entries.keys())
    assert set(missing) == set(expected), (missing,expected)
    assert len(all_roots)==63 and len(set(all_roots))==63 and missing
    blockmap = {}
    for f in sorted(out.glob("ZRCBlock*.lean")):
        for x in re.findall(r"^namespace BB6\.Agent6E0ZeroRCBlocks\.H(\d+)$", f.read_text(),re.M):
            assert x not in blockmap
            blockmap[x] = f.stem
    seen = set()
    def visit(n):
        if n in seen or n in entries:
            return
        f = out/(n+".lean")
        if not f.is_file():
            return
        seen.add(n)
        for dep in IMP.findall(f.read_text()):
            visit(dep)
    for n in missing:
        visit(n)
    changed = {}
    for n in sorted(seen):
        if n.startswith("ZRCRecovery") and "Batch" in n:
            assert n not in entries
            changed[n] = rewrite(out,n,blockmap)
    assert changed, missing
    # Independently ensure not one previously accepted generated source changed.
    for n,e in entries.items():
        f = out/(n+".lean")
        if f.is_file():
            assert digest(f)==e["source_sha256"], ("accepted source altered",n)
    save(work/"resume-pool.json",dict(core,modules=list(entries.values()),module_count=len(entries)))
    save(work/"resume-roots.json",missing)
    save(work/"resume-plan.json",{"missing":missing,"rewritten":changed,"reused":len(entries)})
    print("Prior accepted modules:",len(entries),"unclosed exact child roots:",missing,flush=True)
    print("Split",sum(changed.values()),"declarations in",len(changed),"previously unaccepted batches",flush=True)

def collect(work, compiled, dest, complete):
    m = load(dest/"manifest.json")
    pool = load(work/"resume-pool.json")
    if complete:
        relevant = {e["module"] for e in m["modules"]} & {e["module"] for e in pool["modules"]}
        assert relevant <= set(m["precompiled_core"]["reused_modules"]), "accepted module recompiled"
    for e in m["modules"]:
        rel=Path(e["olean_path"]); src=compiled/rel
        assert digest(src)==e["olean_sha256"], e["module"]
        target=dest/"build"/rel; target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(src,target)

def finish(work):
    core=load(work/"core.json")
    pool=work/"resume-pool"
    entries={e["module"]:e for e in load(work/"resume-pool.json")["modules"]}
    for name in load(work/"resume-roots.json"):
        cut=work/"resume-cuts"/("raw139-zeroRC-resume-"+name)
        m=load(cut/"manifest.json")
        assert name in {e["module"] for e in m["modules"]}, name
        merge(core,entries,pool,cut/"manifest.json",cut/"build")
    expected={r for f in (work/"recovery-groups").glob("*.txt") for r in f.read_text().splitlines()}
    assert len(expected)==63 and expected<=entries.keys(), expected-entries.keys()
    manifest=work/"resume-pool.json"
    save(manifest,dict(core,modules=list(entries.values()),module_count=len(entries)))
    for root in (0,7,12,18):
        name=f"raw139-e0-zeroRC-root{root:02d}-certified"
        shard=work/"shards"/name
        assert not shard.exists(), name
        shard.mkdir(parents=True)
        theorem=f"BB6.Agent6E0ZeroRC.cZRCRoot{root:02d}"
        cmd=["python3","tools/lean_compile_closure.py",str(work/f"imports/ZRCRoot{root:02d}.lean"),
             "--source-root",str(work/"imports"),"--precompiled-manifest",str(manifest),
             "--precompiled-dir",str(pool),"--workdir",str(shard/"build"),"--jobs","2",
             "--manifest",str(shard/"manifest.json"),"--label",name,"--theorem",theorem,
             "--weighted-bound",str(B)]
        with (shard/"log").open("w") as f:
            p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            for line in p.stdout:
                print(line,end="",flush=True); f.write(line)
            assert p.wait()==0
        log=(shard/"log").read_text()
        assert "sorryAx" not in log and "ofReduceBool" not in log
        assert f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
    subprocess.run(["python3","im-results/agent6-raw139-e0-zeroRC/compose.py",str(work)],check=True)

if __name__=="__main__":
    mode, work = sys.argv[1],Path(sys.argv[2]).resolve()
    if mode=="prepare": prepare(work)
    elif mode=="collect": collect(work,Path(sys.argv[3]),Path(sys.argv[4]),sys.argv[5]=="true")
    elif mode=="finish": finish(work)
    else: raise ValueError(mode)
