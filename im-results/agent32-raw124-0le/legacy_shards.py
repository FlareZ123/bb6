"""Independent source-closure shards for the archived Raw124 zipper proofs.

The final closure builder verifies every reused object's full import identity.
No generated proof or decision procedure is changed by this scheduler.
"""
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BOUNDS = {
    "0RF":71,"0RD":267,"1LC":102,"1RD":80,"0RC":2759,"1RC":688,
    "0LD":157,"1RA":1029,"0RE":2473,"1LF":290,"1LE":670,"1RB":184,
    "0RA":283,"0LC":145,"1RF":140,"0RB":272,"trivial":7,
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prepare(branch, generated):
    generated.mkdir(parents=True, exist_ok=True)
    if branch == "trivial":
        final = "Raw124Trivial"
        shutil.copy2(HERE / (final + ".lean"), generated)
        roots = [final]
    else:
        subprocess.run([sys.executable, str(HERE/"replay_legacy.py"),
                        "--branch", branch, "--out", str(generated)], check=True)
        final = "Raw124Z" + branch + "Data"
        top = "Raw125Shard_Raw124Z" + branch + "Tree"
        kids = [top + f"_k{i:02}" for i in range(24)]
        imports = [line.split()[1] for line in
                   (generated/(top+".lean")).read_text().splitlines()
                   if line.startswith("import ")]
        # Split only on the exact 24 checked immediate child modules.
        roots = kids if imports == kids else [top]
    groups = [roots[i::min(6,len(roots))] for i in range(min(6,len(roots)))]
    assert sorted(sum(groups,[])) == sorted(roots)
    # Keep only the generated Lean sources and a scheduling manifest.
    for p in generated.iterdir():
        if p.is_file() and p.suffix != ".lean":
            p.unlink()
    (generated/"schedule.json").write_text(json.dumps({
        "branch":branch,"final":final,"groups":groups,
        "sources":{p.name:digest(p) for p in sorted(generated.glob("*.lean"))},
    },indent=2)+"\n")
    print(json.dumps(list(range(len(groups)))))

def schedule(generated):
    s=json.loads((generated/"schedule.json").read_text())
    for name,h in s["sources"].items():
        assert digest(generated/name)==h,name
    return s

def compile_roots(roots, generated, core, work, branch=None):
    args=[sys.executable,str(ROOT/"tools/lean_compile_closure.py"),
          "--source-root",str(core),"--source-root",str(generated),
          "--workdir",str(work),"--jobs","2",
          "--precompiled-manifest",str(core/"manifest.json"),
          "--precompiled-dir",str(core),"--manifest",str(work/"manifest.json")]
    overrides={}
    for base in (core,generated):
        for p in sorted(base.rglob("*.lean")):
            mod=".".join(p.relative_to(base).with_suffix("").parts)
            if mod in overrides:
                assert digest(p)==digest(overrides[mod]),mod
            overrides[mod]=p
    for mod,p in sorted(overrides.items()):
        args += ["--override",f"{mod}={p}"]
    if branch is not None:
        th=("BB6.Agent32Raw124Trivial.bound1LD" if branch=="trivial"
            else f"BB6.Agent32Raw124Z{branch}.bound_all")
        args += ["--theorem",th,"--weighted-bound",str(BOUNDS[branch]),
                 "--parent-table","1RB---_1RC---_0RD---_1LD1RE_---1LF_---"+branch,
                 "--provenance-input",str(HERE/"replay_legacy.py"),
                 "--provenance-input",str(HERE/"legacy_shards.py")]
    subprocess.run(args+[str(generated/(r+".lean")) for r in roots],check=True)

def merge(inputs, merged, generated, prefix=None):
    s=schedule(generated)
    manifests=[]
    entries={}
    merged.mkdir(parents=True,exist_ok=True)
    for i,group in enumerate(s["groups"]):
        folder=inputs/f"{prefix or 'raw124-legacy-' + s['branch']}-shard-{i}"
        m=json.loads((folder/"manifest.json").read_text())
        assert m["schema_version"]==1
        if manifests:
            assert m["lean_version"]==manifests[0]["lean_version"]
            assert m["lean_binary"]["sha256"]==manifests[0]["lean_binary"]["sha256"]
        manifests.append(m)
        mods={e["module"] for e in m["modules"]}
        assert set(group)<=mods,(i,group,mods)
        for e in m["modules"]:
            mod=e["module"]
            rel=Path(*mod.split("."))
            assert not rel.is_absolute() and ".." not in rel.parts
            src=rel.with_suffix(".lean")
            obj=Path(e["olean_path"])
            assert obj==rel.with_suffix(".olean"),e
            assert digest(folder/src)==e["source_sha256"],mod
            assert digest(folder/obj)==e["olean_sha256"],mod
            if src.name in s["sources"] and len(src.parts)==1:
                assert e["source_sha256"]==s["sources"][src.name],mod
            if mod in entries:
                assert entries[mod]["module_identity_sha256"]==e["module_identity_sha256"],mod
                continue
            entries[mod]=e
            for p in (src,obj):
                target=merged/p
                target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copy2(folder/p,target)
    m=dict(manifests[0])
    m["modules"]=[entries[k] for k in sorted(entries)]
    m["module_count"]=len(entries)
    m["source_revisions"]=sorted({r for m in manifests for r in m["source_revisions"]})
    (merged/"manifest.json").write_text(json.dumps(m,indent=2)+"\n")
    print(f"Merged {len(manifests)} independently checked shards; {len(entries)} modules",flush=True)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("action",choices=["prepare","shard","assemble"])
    p.add_argument("--branch",choices=BOUNDS)
    p.add_argument("--generated",type=Path,required=True)
    p.add_argument("--core",type=Path)
    p.add_argument("--work",type=Path)
    p.add_argument("--shard",type=int)
    p.add_argument("--inputs",type=Path)
    p.add_argument("--merged",type=Path)
    a=p.parse_args()
    if a.action=="prepare":
        assert a.branch
        prepare(a.branch,a.generated.resolve())
    elif a.action=="shard":
        s=schedule(a.generated)
        compile_roots(s["groups"][a.shard],a.generated,a.core,a.work)
    else:
        s=schedule(a.generated)
        merge(a.inputs,a.merged,a.generated)
        compile_roots([s["final"]],a.generated,a.merged,a.work,s["branch"])

if __name__=="__main__":
    main()
