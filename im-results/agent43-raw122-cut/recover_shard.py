#!/usr/bin/env python3
from pathlib import Path
import os, shutil, subprocess, sys
root=Path.cwd()
cut=root/"im-results/agent43-raw122-cut"
for p in Path("/tmp/a43-source").glob("*.lean"): shutil.copy2(p,cut/p.name)
core=Path("/tmp/a43-core")
work=Path("/tmp/a43-recovery")
prov=["im-results/agent43-raw122-cut/generate.py","im-results/agent43-raw122-cut/symbolic.py","im-results/agent43-raw122-cut/long-plans.json","im-results/agent43-raw122-cut/extra-bank.txt","tools/lean_compile_closure.py"]
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
