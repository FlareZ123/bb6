#!/usr/bin/env python3
"""Merge old and recovered raw122 Lean shards, then compile the parent theorem."""
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys

root=Path.cwd()
cut=root/"im-results/agent43-raw122-cut"
source=Path("/tmp/a43-source")
source_ref=os.environ["SOURCE_REF"]
out=Path("/tmp/a43-audit")
out.mkdir(parents=True,exist_ok=True)
parent_core = os.environ.get("RAW122_PARENT_CORE") == "1"
branch_indices = (
    [1,2,3,4,6,7,8,9,10,11,12,13,14,15,18,19,20,21,22,23]
    if parent_core else list(range(24))
)
root_name = "Raw122CoreAccepted" if parent_core else "Raw122Data"
seen={}
for base in (Path("/tmp/a43-new-shards"),):
    if not base.is_dir(): raise FileNotFoundError(base)
    for shard in sorted(p for p in base.iterdir() if p.is_dir()):
        for src in shard.rglob("*.olean"):
            rel=src.relative_to(shard)
            key=rel.as_posix()
            digest=hashlib.sha256(src.read_bytes()).hexdigest()
            if key in seen and seen[key]!=digest:
                raise RuntimeError(f"conflicting Lean object for {key}")
            if key not in seen:
                dst=out/rel
                dst.parent.mkdir(parents=True,exist_ok=True)
                shutil.copy2(src,dst)
                seen[key]=digest
print(f"merged {len(seen)} distinct Lean objects",flush=True)
for src in source.glob("*.lean"):
    if parent_core and src.name in {"Raw122Branch00.lean","Raw122Branch05.lean","Raw122Branch16.lean","Raw122Branch17.lean"}:
        continue
    shutil.copy2(src,cut/src.name)
    shutil.copy2(src,out/src.name)
if parent_core:
    for name in ("Raw122Branch00.lean","Raw122Branch05.lean","Raw122Branch16.lean","Raw122Branch17.lean"):
        original=cut/name
        if original.exists():
            original.unlink()
            print(f"removed superseded original-source module {original.relative_to(root)}; nested Cover module is authoritative",flush=True)
env=os.environ.copy()
env["LEAN_PATH"]=str(out)
log_path=out/"audit.log"
with log_path.open("w",encoding="utf-8") as log:
    if not parent_core:
        for i in branch_indices:
            name=f"Raw122Branch{i:02}"
            subprocess.run(["lean","-o",f"{name}.olean",f"{name}.lean"],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
        subprocess.run(["lean","-o",f"{root_name}.olean",f"{root_name}.lean"],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
log_text=log_path.read_text(encoding="utf-8")
if "sorryAx" in log_text or "native_decide" in log_text:
    raise RuntimeError("Raw122 core output contains a prohibited axiom or native_decide")
if not parent_core:
    for line in (out/"Raw122Data.lean").read_text(encoding="utf-8").splitlines():
        if "theorem residual_count" in line or "theorem sound" in line:
            print(line,flush=True)
prov=[
"im-results/agent43-raw122-cut/generate.py",
"im-results/agent43-raw122-cut/symbolic.py",
"im-results/agent43-raw122-cut/long-plans.json",
"im-results/agent43-raw122-cut/extra-bank.txt",
"im-results/agent43-raw122-cut/phase27510.py",
"im-results/agent43-raw122-cut/Raw122Immediate.lean",
"im-results/agent43-raw122-cut/Raw122Counter3708.lean",
"im-results/agent43-raw122-cut/Raw122TailGrowth.lean",
"im-results/agent43-raw122-cut/Raw122Base.lean",
"im-results/agent31-three-hole-tnf/generate_four_hole.py",
"im-results/agent31-three-hole-tnf/generate_sweeps.py",
"im-results/agent47-raw114-cut/multi_sweep.py",
"im-results/agent2-tnf-raw99/enumerate.cpp",
"im-results/agent8-tnf-six/bank.cpp",
"im-results/agent1-ngram/ngram.cpp",
"im-results/agent47-raw111-cut/ngram_sparse.cpp",
"im-results/agent8-tnf-raw117/bank117.txt",
"im-results/agent8-tnf-raw117/bank112.txt",
"im-results/agent8-tnf-raw117/bank112extra.txt",
"im-results/agent8-tnf-six/raw115/bank.txt",
"im-results/agent8-tnf-six/raw119/bank.txt",
"im-results/agent47-raw111-cut/far-bank.txt",
"im-results/agent47-raw112-cut/far-bank.txt",
"im-results/agent47-raw112-cut/far-extra.txt",
"im-results/agent47-raw115-cut/far-bank.txt",
"im-results/agent3-tnf-raw120/bank.txt",
"im-results/agent3-tnf-raw120/rb-bank.txt",
"im-results/agent3-tnf-raw120/la-discovery-bank.txt",
"im-results/agent47-raw111-cut/emit_sparse.py",
"im-results/agent1-ngram/emit_ngram.py",
"im-results/agent13-coverage/unpack.py",
"tools/lean_compile_closure.py"]
if parent_core:
    prov.append("im-results/agent43-raw122-cut/Raw122CoreAccepted.lean")
    prov.append("im-results/agent43-raw122-cut/assemble_recovered.py")
subprocess.run(["git","fetch","--no-tags","--depth=1","origin",source_ref],cwd=root,check=True)
checkout=[]
filtered=[]
for p in prov:
    if p=="tools/lean_compile_closure.py":
        filtered.append(p)
        continue
    exists=subprocess.run(["git","cat-file","-e",f"{source_ref}:{p}"],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    if exists.returncode==0:
        filtered.append(p)
        checkout.append(p)
prov=filtered
if checkout:
    subprocess.run(["git","checkout",source_ref,"--",*checkout],cwd=root,check=True)
(out/"source-ref.txt").write_text(source_ref+"\n",encoding="utf-8")
prov.append(str(out/"source-ref.txt"))

def manifest_command(path: Path, label: str) -> list[str]:
    cmd=[sys.executable,"tools/lean_compile_closure.py","--workdir",str(out),"--manifest",str(path),"--manifest-only","--artifact-dir",str(out),"--label",label,"--artifact-name","raw122-parent-core" if parent_core else "raw122-certified-root"]
    if parent_core:
        cmd += ["--allow-missing-objects"]
    else:
        cmd += ["--theorem","BB6.Agent43Raw122.sound","--parent-table","1RB---_1RC---_0RD---_1LD1RE_---0LF_------","--weighted-bound","7014"]
    for p in prov: cmd += ["--provenance-input",p]
    cmd += [str((cut/f"{root_name}.lean").relative_to(root))]
    return cmd

prepin_manifest=out/"manifest-prepin.json"
subprocess.run(manifest_command(prepin_manifest,"raw122-parent-core-prepin" if parent_core else "raw122-partial-audit-prepin"),cwd=root,check=True)
prepin=json.loads(prepin_manifest.read_text(encoding="utf-8"))
checkout_modules=[]
for item in prepin.get("modules",[]):
    if item.get("source_kind")!="tracked":
        continue
    source_path=Path(item["source_path"])
    if source_path.is_absolute():
        try:
            source_path=source_path.resolve().relative_to(root.resolve())
        except ValueError:
            continue
    relative=source_path.as_posix()
    exists=subprocess.run(["git","cat-file","-e",f"{source_ref}:{relative}"],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    if exists.returncode==0:
        checkout_modules.append(relative)
if checkout_modules:
    checkout_modules=sorted(set(checkout_modules))
    subprocess.run(["git","checkout",source_ref,"--",*checkout_modules],cwd=root,check=True)
    print(f"pinned {len(checkout_modules)} tracked modules to the precompiled-object source revision",flush=True)
subprocess.run(manifest_command(out/"manifest.json","raw122-parent-core-pinned" if parent_core else "raw122-partial-audit-pinned"),cwd=root,check=True)
print(f"assembled {'Raw122 parent core' if parent_core else 'raw122 partial audit'} from {len(seen)} source-checked objects and {len(branch_indices)} original branches",flush=True)
