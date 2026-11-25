#!/usr/bin/env python3
"""Recompose fourteen fully checked raw122 F1 cylinders from pinned artifacts.
Usage: python recover_fourteen.py ARTIFACT_DIRECTORY WORK_DIRECTORY
Artifact ZIPs are named github-actions-artifact-ID.zip. Lean 4.36.0-rc2
must be on PATH. This reuses original checked objects and checks the branch
and root compositions afresh; it does not rerun the old C++ enumerator.
"""
from pathlib import Path
import hashlib, json, os, subprocess, sys, zipfile

IDS = (1,2,3,6,7,8,9,10,11,15,19,20,21,22)
ROOT = 15012128172
SOURCE = 15043765926
SHARDS = (
    15014140359,15013281090,15014370771,15014000823,
    15012859158,15014041207,15013293367,15014141313,
    15012829167,15013393876,15013229121,15013228724,
    15015286011,15013909733,15014903049,15014019773,
    15013745899,15012533494,15012394320,
    15013938113,15013758854,15013244079,
    15014881390,15015410080,15013814077,
    15053217773,15053066816,15052003626,
    15053280219,15051623902,15054610263,15051839101,
)

def main():
    artifacts, work = map(lambda x: Path(x).resolve(), sys.argv[1:])
    work.mkdir(parents=True, exist_ok=True)
    def archive(i):
        return zipfile.ZipFile(artifacts / f"github-actions-artifact-{i}.zip")
    for i in (ROOT, *SHARDS):
        with archive(i) as z:
            if "metadata.json" in z.namelist():
                m=json.loads(z.read("metadata.json"))
                assert m["source_artifact"]==SOURCE
                assert m["core_artifact"]==15012394320
                for f,h in m["files"].items():
                    assert hashlib.sha256(z.read(f)).hexdigest()==h,(i,f)
            for item in z.infolist():
                name=Path(item.filename).name
                if not name.endswith(".olean") or name.startswith(("Raw122Data","Raw122Branch")):
                    continue
                data=z.read(item)
                dst=work/name
                if dst.exists() and dst.read_bytes()!=data:
                    raise ValueError(f"conflicting object {name}, artifact {i}")
                dst.write_bytes(data)
    with archive(SOURCE) as z:
        for i in IDS:
            name=f"Raw122Branch{i:02}.lean"
            entries=[x for x in z.namelist() if Path(x).name==name]
            assert len(entries)==1,name
            (work/name).write_bytes(z.read(entries[0]))
    env=dict(os.environ,LEAN_PATH=str(work))
    for i in IDS:
        name=f"Raw122Branch{i:02}"
        subprocess.run(["lean","-o",name+".olean",name+".lean"],cwd=work,env=env,check=True)
    name="Raw122Recovered14"
    (work/(name+".lean")).write_bytes(Path(__file__).with_name(name+".lean").read_bytes())
    result=subprocess.run(["lean","-o",name+".olean",name+".lean"],cwd=work,env=env,check=True,text=True,capture_output=True)
    print(result.stdout,end="")
    assert "sorryAx" not in result.stdout and "Lean.ofReduceBool" not in result.stdout
    assert "BB6.Agent43Raw122Recovered14.sound" in result.stdout
    assert "BB6.Agent43Raw122Recovered14.residual_count" in result.stdout

if __name__=="__main__":main()
