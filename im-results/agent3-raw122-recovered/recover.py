"""Reproduce the two closed F1 cylinders from successful targeted shards.

Download the ZIP artifacts listed in pins.json as github-actions-artifact-ID.zip.
Only the branch composition and empty-residual wrapper are newly compiled.
"""
import argparse, hashlib, json, os, subprocess, zipfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
PINS = json.loads((HERE / "pins.json").read_text())
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("artifacts", type=Path)
    ap.add_argument("work", type=Path)
    ap.add_argument("branches", nargs="+", choices=list(PINS["groups"]))
    a = ap.parse_args()
    assert "4.36.0-rc2" in subprocess.check_output(["lean","--version"], text=True)
    def archive(i):
        p = a.artifacts / f"github-actions-artifact-{i}.zip"
        assert hashlib.file_digest(p.open("rb"),"sha256").hexdigest() == PINS["sha256"][str(i)], p
        return zipfile.ZipFile(p)
    for branch in a.branches:
        w = (a.work / f"b{branch}").resolve()
        w.mkdir(parents=True, exist_ok=False)
        with archive(PINS["core"]) as z:
            for n in z.namelist():
                name = Path(n).name
                if name.endswith(".olean") and (not name.startswith("Raw122") or name=="Raw122Base.olean"):
                    (w/name).write_bytes(z.read(n))
        with archive(PINS["source"]) as z:
            for n in z.namelist():
                name = Path(n).name
                if name.endswith(".lean"):
                    (w/name).write_bytes(z.read(n))
        seen = {}
        covered = set()
        for i in PINS["groups"][branch]:
            with archive(i) as z:
                meta = json.loads(z.read("metadata.json"))
                assert meta["source_artifact"] == PINS["source"] and meta["core_artifact"] == PINS["core"]
                assert meta["branch"] == int(branch)
                interval = set(range(meta["first"],meta["end"]))
                assert not (covered & interval)
                covered.update(interval)
                for n in z.namelist():
                    name = Path(n).name
                    if not name.endswith((".lean",".olean")): continue
                    data = z.read(n)
                    h = hashlib.sha256(data).hexdigest()
                    assert h == meta["files"][name], (i,name)
                    assert name not in seen or seen[name] == h, (i,name)
                    if name.endswith(".olean") and (w/name).exists():
                        assert (w/name).read_bytes() == data, (i,name)
                    seen[name] = h
                    (w/name).write_bytes(data)
        assert covered == set(range(24)), covered
        assert all((w/f"Raw122Kid{branch}_{i:02}.olean").exists() for i in range(24))
        wrapper = f"Raw122Recovered{branch}"
        (w/(wrapper+".lean")).write_bytes((HERE/(wrapper+".lean")).read_bytes())
        env = dict(os.environ, LEAN_PATH=str(w))
        for module in [f"Raw122Branch{branch}", wrapper]:
            log = subprocess.check_output(["lean","-o",module+".olean",module+".lean"],cwd=w,env=env,text=True)
            print(log,end="")
            for line in log.splitlines():
                if "depends on axioms:" in line:
                    axioms = line.split("[",1)[1].split("]",1)[0]
                    assert set(axioms.split(", ")) <= {"propext","Classical.choice","Quot.sound"}
        print(f"Accepted {branch}: empty residual list and WeightedBound 7014")
if __name__=="__main__":
    main()
