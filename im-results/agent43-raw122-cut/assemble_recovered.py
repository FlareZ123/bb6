#!/usr/bin/env python3
"""Merge old and recovered raw122 Lean shards, then compile the parent theorem."""
from pathlib import Path
import hashlib, os, shutil, subprocess, sys

root=Path.cwd()
cut=root/"im-results/agent43-raw122-cut"
source=Path("/tmp/a43-source")
source_ref=os.environ["SOURCE_REF"]
out=Path("/tmp/a43-audit")
out.mkdir(parents=True,exist_ok=True)
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
    shutil.copy2(src,cut/src.name)
    shutil.copy2(src,out/src.name)
env=os.environ.copy()
env["LEAN_PATH"]=str(out)
log_path=out/"audit.log"
with log_path.open("w",encoding="utf-8") as log:
    for i in range(24):
        name=f"Raw122Branch{i:02}"
        subprocess.run(["lean","-o",f"{name}.olean",f"{name}.lean"],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
    subprocess.run(["lean","-o","Raw122Data.olean","Raw122Data.lean"],cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
log_text=log_path.read_text(encoding="utf-8")
if "sorryAx" in log_text or "native_decide" in log_text:
    raise RuntimeError("root audit output contains a prohibited axiom or native_decide")
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
checkout=[p for p in prov if p!="tools/lean_compile_closure.py"]
subprocess.run(["git","fetch","--no-tags","--depth=1","origin",source_ref],cwd=root,check=True)
subprocess.run(["git","checkout",source_ref,"--",*checkout],cwd=root,check=True)
cmd=[sys.executable,"tools/lean_compile_closure.py","--workdir",str(out),"--manifest",str(out/"manifest.json"),"--manifest-only","--artifact-dir",str(out),"--label","raw122-partial-audit","--theorem","BB6.Agent43Raw122.sound","--parent-table","1RB---_1RC---_0RD---_1LD1RE_---0LF_------","--weighted-bound","7014","--artifact-name","raw122-certified-root"]
for p in prov: cmd += ["--provenance-input",p]
cmd += [str((cut/"Raw122Data.lean").relative_to(root))]
subprocess.run(cmd,cwd=root,check=True)
print(f"assembled raw122 partial audit from {len(seen)} source-checked objects",flush=True)
