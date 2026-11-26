"""Replay Raw122 using pinned GitHub Actions archives and kernel compilation.

Run from a checkout with Lean 4.36.0-rc2 on PATH:
    python im-results/agent43-raw122-cut/replay_sharp.py ARCHIVES WORK
ARCHIVES contains github-actions-artifact-ID.zip files. No candidate search
is performed. Missing .olean files are compiled, never asserted.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ARCHIVES, WORK = map(lambda s: Path(s).resolve(), sys.argv[1:3])
WORK.mkdir(parents=True, exist_ok=True)
PINS = json.loads((HERE / "sharp_artifacts.json").read_text())
SEEN = {}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def merge(artifact, fallback=False, branches=False):
    with ZipFile(ARCHIVES / f"github-actions-artifact-{artifact}.zip") as z:
        meta = json.loads(z.read("metadata.json")) if "metadata.json" in z.namelist() else None
        if meta:
            assert meta["source_artifact"] == 15043765926
            assert meta["core_artifact"] == 15012394320
        for name in z.namelist():
            filename = Path(name).name
            if not filename.endswith((".lean", ".olean")):
                continue
            if not branches and filename.startswith(("Raw122Branch", "Raw122Data")):
                continue
            data = z.read(name)
            digest = sha(data)
            if meta and name in meta["files"]:
                assert digest == meta["files"][name], (artifact, name)
            if filename in SEEN:
                if not fallback:
                    assert SEEN[filename] == digest, (artifact, filename)
                continue
            if fallback and (WORK / filename).exists():
                continue
            SEEN[filename] = digest
            (WORK / filename).write_bytes(data)
    print("merged", artifact, len(SEEN), flush=True)

for artifact in PINS["archived_shards"]:
    merge(artifact, branches=artifact in PINS["assembly_artifacts"])
# Later successful targeted and linkable closure artifacts.
for artifact in PINS["late_artifacts"]:
    merge(artifact, branches=True)
# Original generated sources fill holes, but never override factored
# sources actually used to produce accepted objects.
merge(PINS["source"], fallback=True, branches=True)
merge(PINS["source_bundle"], fallback=True, branches=True)

# The canonical original branch source is selected from the source archive,
# except the four special branch modules already imported by the rosters.
with ZipFile(ARCHIVES / f"github-actions-artifact-{PINS['source']}.zip") as z:
    for name in z.namelist():
        filename = Path(name).name
        if re.fullmatch(r"Raw122Branch\d\d\.lean", filename):
            i = int(filename[12:14])
            if i not in (0, 5, 16, 17):
                (WORK / filename).write_bytes(z.read(name))

for filename in ("Raw122Compact11332.lean", "Raw122Symbol11332.lean",
                 "Raw122RootCompose.lean", "Raw122SharpLate.lean",
                 "Raw122SharpWitnesses.lean", "Raw122SharpParent.lean",
                 "Raw122Recovered14.lean", "Raw122Recovered04.lean",
                 "Raw122Recovered13.lean", "Raw122RecoveredLC.lean",
                 "Raw122Recovered18.lean"):
    path = HERE / filename
    if path.is_file():
        shutil.copy2(path, WORK / filename)
for i in (12, 23):
    filename = f"Raw122Recovered{i:02}.lean"
    shutil.copy2(ROOT / "im-results" / "agent3-raw122-recovered" / filename, WORK / filename)

env = dict(os.environ, LEAN_PATH=str(WORK))
def compile_module(m):
    p, o = WORK / (m + ".lean"), WORK / (m + ".olean")
    if o.exists():
        return
    for d in re.findall(r"^import ([\w.]+)", p.read_text(), re.M):
        if (WORK / (d + ".lean")).exists():
            compile_module(d)
    print("compile", m, flush=True)
    subprocess.run(["lean", "-j", "1", "-o", str(o), str(p)],
                   cwd=WORK, env=env, check=True)

def quick(s):
    return ("import QuickWeight\n" +
            s.replace("rw [← partialCheck.eq_2, ← BB6.Agent47Raw111.partialPrefix_eq]",
                      "rw [← BB6.Agent43QuickWeight.quickPrefix_eq]")
             .replace("exact ⟨by decide, allMoves_of",
                      "exact ⟨by rw [← BB6.Agent43QuickWeight.quickZipQuery_eq]; decide, allMoves_of"))

def rebuild_kid(m, fused):
    p = WORK / (m + ".lean")
    if (WORK / (m + ".olean")).exists():
        return
    if p.stat().st_size < 3000:
        compile_module(m)
        return
    original = WORK / "original" / p.name
    original.parent.mkdir(exist_ok=True)
    shutil.copy2(p, original)
    modules = subprocess.check_output([sys.executable, str(HERE / "split_grouped.py"),
                                       str(original), str(WORK), "4000"], text=True).splitlines()
    if fused:
        imports, parts = set(), []
        for name in modules:
            s = quick((WORK / (name + ".lean")).read_text())
            imports.update(re.findall(r"^import ([\w.]+)", s, re.M))
            parts.append(re.sub(r"^import [^\n]+\n", "", s, flags=re.M))
        imports.difference_update(modules)
        p.write_text("".join("import " + i + "\n" for i in sorted(imports)) + "\n".join(parts))
        compile_module(m)
    else:
        for name in modules:
            source = WORK / (name + ".lean")
            source.write_text(quick(source.read_text()))
        for name in modules:
            compile_module(name)

for i in (0, 1):
    rebuild_kid(f"Raw122Kid13_{i:02}", False)
for i in (0, 1, 2, 3, 4, 13, 14, 15, 16, 17):
    rebuild_kid(f"Raw122Kid14_{i:02}", True)
for root in ("Raw122Recovered14", "Raw122Recovered04", "Raw122Recovered12",
             "Raw122Recovered13", "Raw122Recovered18", "Raw122Recovered23",
             "Raw122RecoveredLC", "Raw122SharpParent"):
    compile_module(root)
print("Raw122SharpParent compiled", flush=True)
