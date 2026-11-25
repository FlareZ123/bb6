#!/usr/bin/env python3
from pathlib import Path
import os, shutil, subprocess, sys
root=Path.cwd()
cut=root/"im-results/agent43-raw122-cut"
OLD_SOURCE=Path("/tmp/a43-source-old")
SOURCE=Path("/tmp/a43-source")
for p in OLD_SOURCE.glob("*.lean"): shutil.copy2(p,cut/p.name)
core=Path("/tmp/a43-core")
work=Path("/tmp/a43-recovery")
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
source_ref=os.environ["SOURCE_REF"]
subprocess.run(["git","fetch","--no-tags","--depth=1","origin",source_ref],cwd=root,check=True)
checkout_paths=[]
filtered=[]
for p in prov:
    if p=="tools/lean_compile_closure.py":
        filtered.append(p)
        continue
    exists=subprocess.run(["git","cat-file","-e",f"{source_ref}:{p}"],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
    if exists.returncode==0:
        filtered.append(p)
        checkout_paths.append(p)
prov=filtered
if checkout_paths:
    subprocess.run(["git","checkout",source_ref,"--",*checkout_paths],cwd=root,check=True)
for p in prov:
    if not (root/p).is_file(): raise FileNotFoundError(p)
common=[cut/f"Raw122Kid03_{i:02}.lean" for i in range(6)]
cmd=[sys.executable,"tools/lean_compile_closure.py","--workdir",str(core),"--manifest",str(core/"manifest.json"),"--manifest-only","--artifact-dir",str(core),"--label","raw122-recovery-core"]
for p in prov: cmd += ["--provenance-input",p]
cmd += [str(p.relative_to(root)) for p in common]
subprocess.run(cmd,cwd=root,check=True)
branch=os.environ["BRANCH"]; first=int(os.environ["FIRST"]); end=int(os.environ["END"])
for p in SOURCE.glob("*.lean"): shutil.copy2(p,cut/p.name)
roots=([cut/"Raw122Base.lean"] if branch=="base" else
       [cut/f"Raw122Kid{branch}_{i:02}.lean" for i in range(first,end)])
work.mkdir(parents=True,exist_ok=True)
cmd=[sys.executable,"tools/lean_compile_closure.py","--workdir",str(work),"--jobs","4","--precompiled-dir",str(core),"--precompiled-manifest",str(core/"manifest.json"),"--manifest",str(work/"manifest.json"),"--label",f"raw122-recovery-{branch}-{first}","--artifact-name",f"raw122-recovery-{branch}-{first}","--parent-table","1RB---_1RC---_0RD---_1LD1RE_---0LF_------","--weighted-bound","7014"]
for p in prov: cmd += ["--provenance-input",p]
cmd += [str(p.relative_to(root)) for p in roots]
subprocess.run(cmd,cwd=root,check=True)
