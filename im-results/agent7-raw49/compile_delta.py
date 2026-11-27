"""Compile only new modules atop the pinned, source-accepted 97-object closure."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json, os, shutil, subprocess, sys
base, generated, work = map(Path, sys.argv[1:4])
children = [int(i) for i in sys.argv[4:]]
repo = Path(__file__).resolve().parent
work.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [work, base])))
def compile_one(src):
    src = Path(src)
    target = work / src.name
    shutil.copyfile(src, target)
    res = subprocess.run(["lean", "-o", str(target.with_suffix(".olean")), target.name],
                         cwd=work, env=env, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)
    print(f"=== {target.name} ===\n{res.stdout}", flush=True)
    res.check_returncode()
    if "sorryAx" in res.stdout or "native_decide" in res.stdout:
        raise RuntimeError(f"forbidden proof dependency: {target.name}")
with ThreadPoolExecutor(max_workers=4) as pool:
    list(pool.map(compile_one, [repo/"Raw49Drift230574.lean", repo/"Raw49Nested261066.lean"]))
    paths = [generated/f"child{i}" for i in children]
    lists = [json.loads((p/"manifest.json").read_text()) for p in paths]
    for remaining in zip(paths, lists):
        if not remaining[1]: raise ValueError("empty manifest")
    pending = {name:(p/f"{name}.lean", deps) for p, rows in zip(paths, lists) for name,deps in rows}
    done = set()
    while pending:
        ready = sorted(name for name,(_,deps) in pending.items() if set(deps)<=done)
        if not ready: raise RuntimeError("cyclic or missing generated dependency")
        list(pool.map(compile_one, [pending[name][0] for name in ready]))
        for name in ready: done.add(name); del pending[name]
compile_one(repo/"Raw49Progress95.lean")
