#!/usr/bin/env python3
"""Compile repaired Extra132 proof DAG reusing unchanged, accepted .olean leaves.

Unlike a fixed bin partition, this joins by cryptographically matching the
actual Lean source hash and accepted object hash *per module*. Sharding changes
only a former oversized source module and its fresh dependencies; seven prior
independent CI leaves can be reused without recompilation. Every unmatched
source module is compiled from the regenerated source and all imports remain
in the same exact proof DAG; no assumed mathematical theorem is inserted.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    if len(sys.argv) != 4:
        raise SystemExit("usage: compile-parent-repair.py SOURCE BASE OUT")
    source, base, out = map(lambda p: Path(p).resolve(), sys.argv[1:])
    out.mkdir(parents=True, exist_ok=True)
    files = {p.stem:p for p in source.glob("*.lean")}
    parent_id = int(os.environ.get('RAW11_REPAIR_ID', '132'))
    assert parent_id in (132,140)
    target_parent = f'Agent5Raw11Extra{parent_id}'
    assert target_parent in files
    raw_imports = {
        k:{m for line in p.read_text().splitlines() if line.startswith("import ")
           for m in line.split()[1:]}
        for k,p in files.items()
    }
    deps = {k:v & files.keys() for k,v in raw_imports.items()}
    for ext in set().union(*raw_imports.values()) - files.keys():
        assert (base / (ext.replace(".","/")+".olean")).is_file(), ext

    accepted = {}
    receipts = sorted(out.glob("receipt-*.json"))
    repair_receipt = out / "repair-receipt.json"
    if repair_receipt.is_file():
        receipts.append(repair_receipt)
    for receipt in receipts:
        for name, obj in json.loads(receipt.read_text()).items():
            if name in accepted:
                assert accepted[name] == obj, "conflicting immutable receipts"
            accepted[name] = obj

    reused = {}
    for name,obj in accepted.items():
        target = out / (name+".olean")
        if (name in files and target.is_file()
            and obj["source"] == sha(files[name])
            and obj["olean"] == sha(target)
            and obj["axioms"]
            and not re.search(r"sorryAx|native_decide", "\n".join(obj["axioms"]))):
            reused[name] = obj

    # Never permit a stale .olean with a changed/newly rewritten source.
    for obj in out.glob("*.olean"):
        if obj.stem not in reused:
            obj.unlink()

    done = set(reused)
    report = dict(reused)
    print("source_modules",len(files),
          "accepted_reused",len(reused),
          "fresh_to_compile",len(files)-len(reused),flush=True)
    print("accepted_sources",sorted(done),flush=True)

    def compile_one(name):
        src = files[name]
        target = out / (name+".olean")
        log = out / (name+".log")
        env = dict(os.environ, LEAN_PATH=os.pathsep.join((str(out),str(base))))
        print("compile",name,"bytes",src.stat().st_size,flush=True)
        with log.open("w") as stream:
            result = subprocess.run(
                ["lean","-j1","-o",str(target),src.name],
                cwd=source,env=env,stdout=stream,stderr=subprocess.STDOUT)
        content = log.read_text()
        if result.returncode != 0 or re.search(r"sorryAx|native_decide",content):
            print(content[-12000:],flush=True)
            raise RuntimeError(f"Lean kernel rejected {name}")
        axioms = [x for x in content.splitlines()
                  if "depends on axioms:" in x or "does not depend on any axioms" in x]
        if not axioms:
            print(content[-12000:],flush=True)
            raise RuntimeError(f"missing theorem axiom report for {name}")
        print(*axioms,sep="\n",flush=True)
        return {"source":sha(src),"olean":sha(target),"axioms":axioms}

    while done != files.keys():
        ready = sorted((k for k in files.keys()-done if deps[k] <= done),
                       key=lambda k:(files[k].stat().st_size,k))
        assert ready, "dependency cycle or unrepresented import"
        for name in ready:
            report[name] = compile_one(name)
            done.add(name)
            (out/"repair-receipt.json").write_text(
                json.dumps(report,sort_keys=True,indent=2)+"\n")
    assert len(report) == len(files)
    assert (out/(target_parent+'.olean')).is_file()
    # Mathematical entry point is source-checked by the whole DAG.
    top = (out/(target_parent+'.log')).read_text()
    assert f"'BB6.{target_parent}.cover' depends on axioms:" in top
    print(f"accepted {parent_id} repaired complete parent",len(report),
          "modules, original accepted modules reused",len(reused),flush=True)


if __name__ == "__main__":
    main()
