"""Resume a pinned root closure using only completed, atomic Lean objects."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

work = Path(sys.argv[1]).resolve()
root = sys.argv[2]
out = work / "resume"
out.mkdir(parents=True, exist_ok=True)
build = out / "build"
build.mkdir(exist_ok=True)
core = json.loads((work / "core.json").read_text())
merged = work / "merged-resume"
merged.mkdir(exist_ok=True)
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
entries = {}
sources = [(core, work / "core")]
prev = work / "previous"
if (prev / "manifest.json").exists():
    old = json.loads((prev / "manifest.json").read_text())
    assert old["proof_source_revision"] == core["proof_source_revision"]
    assert old["lean_binary"]["sha256"] == core["lean_binary"]["sha256"]
    sources.append((old, prev / "build"))
for m, path in sources:
    for e in m["modules"]:
        name = e["module"]
        rel = Path(e["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        src = path / rel
        assert digest(src) == e["olean_sha256"], name
        if name in entries:
            assert entries[name]["module_identity_sha256"] == e["module_identity_sha256"], name
            continue
        entries[name] = e
        dst = merged / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
manifest = dict(core, modules=list(entries.values()), module_count=len(entries))
manifest_path = work / "merged-resume.json"
manifest_path.write_text(json.dumps(manifest))

# An interrupted compiler must never expose a partial .olean under its final name.
wrapper = work / "atomic-lean"
wrapper.write_text("""#!/usr/bin/env python3
import os, subprocess, sys
from pathlib import Path
a = sys.argv[1:]
if '-o' not in a:
    os.execvp('lean', ['lean', *a])
i = a.index('-o') + 1
dest = Path(a[i])
temp = dest.with_name(dest.stem + '.pending.olean')
a[i] = str(temp)
r = subprocess.run(['lean', *a])
if r.returncode == 0:
    os.replace(temp, dest)
else:
    temp.unlink(missing_ok=True)
sys.exit(r.returncode)
""")
wrapper.chmod(0o755)

src = work / "imports" / f"OLCRoot{root}.lean"
theorem = f"BB6.Agent4E0OneLCParent.cOLCRoot{root}"
common = ["python3", "tools/lean_compile_closure.py", str(src),
          "--source-root", str(work / "imports"), "--lean", str(wrapper),
          "--workdir", str(build), "--jobs", "2", "--label", f"raw139-e0-oneLC-root{root}",
          "--weighted-bound", "204890"]
with (out / "log").open("w") as log:
    # End deliberately while the runner is still alive; completed objects remain usable.
    cmd = ["timeout", "-k", "8s", "150s", *common,
           "--precompiled-manifest", str(manifest_path), "--precompiled-dir", str(merged),
           "--manifest", str(out / "manifest.json"), "--theorem", theorem]
    r = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT)
print((out / "log").read_text())
if r.returncode == 0:
    assert f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in (out / "log").read_text()
    certified = True
elif r.returncode in (124, 137, 143):
    certified = False
    # Incomplete proofs carry no theorem claim. Retain only the closed object prefix.
    subprocess.run([*common, "--manifest-only", "--allow-missing-objects",
                    "--artifact-dir", str(build), "--manifest", str(out / "manifest.json")],
                   check=True)
else:
    # Ordinary Lean/source failures are real failures; do not disguise them as timeouts.
    sys.exit(r.returncode)
m = json.loads((out / "manifest.json").read_text())
keep = {e["olean_path"] for e in m["modules"]}
for p in build.rglob("*"):
    if p.is_file() and p.relative_to(build).as_posix() not in keep:
        p.unlink()
print("Completed dependency-closed modules:", len(keep), "root certified:", certified)
with open(os.environ["GITHUB_OUTPUT"], "a") as f:
    print(f"certified={'true' if certified else 'false'}", file=f)
