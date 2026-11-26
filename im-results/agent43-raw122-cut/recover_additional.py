#!/usr/bin/env python3
"""Check remaining original Raw122 closed children using grouped kernel reduction.

Use pinned original source archive 15043765926 and core artifacts named below.
Already-checked objects are reused, never replaced by unverified new ones.
Usage: python recover_additional.py ARTIFACT_DIRECTORY WORK_DIRECTORY 18 [14]
"""
from pathlib import Path
import hashlib, os, subprocess, sys, zipfile
HERE=Path(__file__).resolve().parent
SOURCE=15043765926
BASE=(15012128172,15012394320)
SHARDS={18:(15014137588,15013838516,15015375008),
        14:(15052854497,15040016426)}

def main():
    artifacts,work=map(lambda p:Path(p).resolve(),sys.argv[1:3])
    ids=tuple(map(int,sys.argv[3:]))
    assert ids and all(i in SHARDS for i in ids)
    work.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LEAN_PATH=str(work))
    def archive(i):
        return zipfile.ZipFile(artifacts/f"github-actions-artifact-{i}.zip")
    for i in (*BASE,*(i for j in ids for i in SHARDS[j])):
        with archive(i) as z:
            for item in z.infolist():
                name=Path(item.filename).name
                if not name.endswith(".olean") or name.startswith(("Raw122Data","Raw122Branch")):
                    continue
                p=work/name
                data=z.read(item)
                if p.exists():
                    if hashlib.sha256(p.read_bytes()).digest()!=hashlib.sha256(data).digest():
                        raise ValueError(f"conflicting object {name}: artifact {i}")
                else:
                    p.write_bytes(data)
    with archive(SOURCE) as z:
        for item in z.infolist():
            name=Path(item.filename).name
            if name.endswith(".lean"):
                (work/name).write_bytes(z.read(item))
    (work/"QuickWeight.lean").write_bytes((HERE/"QuickWeight.lean").read_bytes())
    def compile(name):
        if (work/(name+".olean")).exists():
            return
        p=work/(name+".lean")
        for line in p.read_text().splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]:
                    if (work/(dep+".lean")).exists():
                        compile(dep)
        subprocess.run(["lean","-j","1","-o",name+".olean",p.name],cwd=work,env=env,check=True)
    compile("QuickWeight")
    for i in ids:
        for j in range(24):
            name=f"Raw122Kid{i:02}_{j:02}"
            p=work/(name+".lean")
            if (work/(name+".olean")).exists():
                continue
            assert ".unresolved" not in p.read_text(),name
            if p.stat().st_size>3000:
                modules=subprocess.check_output([sys.executable,str(HERE/"split_grouped.py"),str(p),str(work),"4000"],text=True).splitlines()
                for module in modules:
                    src=work/(module+".lean")
                    s=src.read_text()
                    s="import QuickWeight\n"+s.replace("rw [← partialCheck.eq_2, ← BB6.Agent47Raw111.partialPrefix_eq]","rw [← BB6.Agent43QuickWeight.quickPrefix_eq]").replace("exact ⟨by decide, allMoves_of","exact ⟨by rw [← BB6.Agent43QuickWeight.quickZipQuery_eq]; decide, allMoves_of")
                    src.write_text(s)
                    compile(module)
            else:
                compile(name)
        compile(f"Raw122Branch{i:02}")
        name={14:"Raw122RecoveredLC",18:"Raw122Recovered18"}[i]
        (work/(name+".lean")).write_bytes((HERE/(name+".lean")).read_bytes())
        compile(name)

if __name__=="__main__":
    main()
