#!/usr/bin/env python3
"""Source-check only the sharp Root53 proof DAG over three accepted .olean roots.

Original weighted 30,793-node Root53 parent proof, generic sharpened checker,
and literal 203-step halter have already each passed independent original-
source Lean4.36.0-rc2 CI. This script checks *all new sharp theorem sources*.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

assert len(sys.argv) == 4, "usage: script sharp-source-dir accepted-objects-dir output-dir"
src, frozen, out = map(lambda s: Path(s).resolve(),sys.argv[1:])
out.mkdir(parents=True,exist_ok=True)
sources={p.stem:p for p in src.glob("Q0Root53Sharp*.lean")}
assert len(sources)==27,sources.keys()
needs={k:{m for line in p.read_text().splitlines()
          if line.startswith("import ") for m in line.split()[1:]} & sources.keys()
       for k,p in sources.items()}
externals={m for p in sources.values() for line in p.read_text().splitlines()
           if line.startswith("import ") for m in line.split()[1:]
           if m not in sources}
objects=list(frozen.rglob("*.olean"))
mod_to_paths={}
for obj in objects:
    mod_to_paths.setdefault(obj.stem,[]).append(obj)
missing=externals-mod_to_paths.keys()
assert not missing, f"missing accepted external objects: {missing}"
assert {"Q0Root53Parent","OrdinaryQ0Exhaustive","Raw11Q0Root53Halter203"} <= mod_to_paths.keys()

# Absolute object search paths plus this unique new proof-object directory.
paths=[str(out)]
for obj in sorted(objects):
    directory=str(obj.parent)
    if directory not in paths:paths.append(directory)
env=dict(os.environ,LEAN_PATH=os.pathsep.join(paths))
done=set()
report={}
while done!=sources.keys():
    ready=sorted((k for k in sources.keys()-done if needs[k]<=done),
                 key=lambda k:(sources[k].stat().st_size,k))
    assert ready, "cyclic sharp source imports"
    for module in ready:
        output=out/(module+".olean")
        log=out/(module+".log")
        print("sharp module",module,"bytes",sources[module].stat().st_size,flush=True)
        with log.open("w") as handle:
            result=subprocess.run(["lean","-j1","-o",str(output),sources[module].name],
                cwd=src,stdout=handle,stderr=subprocess.STDOUT,env=env)
        content=log.read_text()
        if result.returncode or re.search(r"sorryAx|native_decide",content):
            print(content[-12000:],flush=True)
            raise RuntimeError(f"Lean rejected {module}")
        entry={"source_sha256":hashlib.sha256(sources[module].read_bytes()).hexdigest(),
               "olean_sha256":hashlib.sha256(output.read_bytes()).hexdigest(),
               "axioms":[x for x in content.splitlines() if "depends on axioms:" in x]}
        report[module]=entry
        done.add(module)
        (out/"sharp-source-manifest.json").write_text(
            json.dumps(report,sort_keys=True,indent=2)+"\n")
    print("completed sharp source modules",len(done),flush=True)
last=(out/"Q0Root53SharpWitness.log").read_text()
assert "'Q0Root53SharpWitness.family_exact_203' depends on axioms:" in last
print(last[-2000:],flush=True)
print("SOURCE-CHECKED exact 203 ordinary maximum of five-hole Root53 family",flush=True)
