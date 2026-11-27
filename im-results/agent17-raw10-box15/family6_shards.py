#!/usr/bin/env python3
"""Recover the complete Family6 (Raw10 base34 box15) proof from durable cuts.

This is transport only: the original Family emitter, Lean source checker and
exact source identity are unchanged. A merged artifact is not a proof until
Family6Source itself compiles and its printed axioms pass the final gate.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
D = ROOT / "im-results/agent49-raw10-box-family"
W = D / "work"
G = W / "generated"
OUT = Path("/tmp/family6-out")
PREP = Path("/tmp/family6-prepared")
COMMON = Path("/tmp/family6-common")
SHARDS = Path("/tmp/family6-shards")
N = 10
sys.path.insert(0, str(ROOT / "tools"))
import lean_compile_closure as lc

def read(p):
    return json.loads(p.read_text())

def write(p, x):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(x, indent=2, sort_keys=True) + "\n")

def run(*args, **kwargs):
    subprocess.run([str(a) for a in args], cwd=ROOT, check=True, **kwargs)

def copy(src, dst, expected=None):
    actual = lc.sha256_file(src)
    if expected is not None and actual != expected:
        raise RuntimeError(f"digest mismatch {src}")
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        if lc.sha256_file(dst) != actual:
            raise RuntimeError(f"conflicting file {dst}")
    else:
        shutil.copy2(src, dst)

def unpack_core():
    run(sys.executable, "im-results/agent13-coverage/unpack.py")

def generate():
    unpack_core()
    W.mkdir(parents=True, exist_ok=True)
    for archive in ("source.tar.xz", "proof-source.tar.xz"):
        run("tar", "-xJf", ROOT / "im-results/agent49-raw10-box5" / archive, "-C", W)
    with (W / "family.tar.xz").open("wb") as f:
        for suffix in ("aa", "ab", "ac", "ad"):
            f.write((D / ("family-part-" + suffix)).read_bytes())
    run("tar", "-xJf", W / "family.tar.xz", "-C", W)
    run(sys.executable, D / "extend_family.py", W)
    env = dict(os.environ, PYTHONPATH=str(ROOT / "im-results/agent13-block-far"),
               PYTHONHASHSEED="0")
    run("bash", W / "replay-family.sh", "6", env=env)
    run("tar", "-xJf", D / "late-source.tar.xz", "-C", G)
    (G / "FamilyCore.lean").rename(G / "A49FamilyCore.lean")
    for p in G.glob("Family*.lean"):
        p.write_text(p.read_text().replace("import FamilyCore\n", "import A49FamilyCore\n"))
    # The original target uses the checkout plus generated root. Preserve all
    # generated Lean inputs at their exact repository-relative paths.
    files = set(W.rglob("*.lean"))
    changed = subprocess.check_output(["git", "diff", "--name-only", "-z"], cwd=ROOT)
    for name in changed.decode().split("\0"):
        if name.endswith(".lean"):
            files.add(ROOT / name)
    source_map = {}
    for p in sorted(files):
        rel = p.relative_to(ROOT)
        target = OUT / "prepared" / "repo" / rel
        copy(p, target)
        source_map[str(rel)] = lc.sha256_file(p)
    write(OUT / "prepared" / "sources.json", source_map)
    index = lc.module_index([G])
    seen = {}
    def visit(name, p=None):
        if name in seen:
            return
        p = p or lc.resolve_source(name, index)
        seen[name] = p
        for dep in lc.parse_imports(p):
            visit(dep)
    visit("Family6Source", G / "Family6Source.lean")
    if "Family6External" not in seen:
        raise RuntimeError("original source no longer uses expected external bank")
    roots = sorted((m for m in seen if m.startswith("Family6R_")),
                   key=lambda m: (-seen[m].stat().st_size, m))
    if len(roots) < N:
        raise RuntimeError(f"unexpected partition frontier: {len(roots)}")
    groups = [[] for _ in range(N)]
    weights = [0] * N
    for m in roots:
        i = min(range(N), key=lambda k: (weights[k], k))
        groups[i].append(str(seen[m].relative_to(ROOT)))
        weights[i] += seen[m].stat().st_size
    write(OUT / "prepared" / "plan.json", {"groups": groups,
          "root": str((G / "Family6Source.lean").relative_to(ROOT)),
          "common": str(seen["Family6External"].relative_to(ROOT))})
    print("partition roots:", len(roots), "groups:", [len(g) for g in groups],
          "source bytes:", weights, flush=True)

def restore():
    unpack_core()
    for rel, digest in read(PREP / "sources.json").items():
        p = Path(rel)
        if p.is_absolute() or ".." in p.parts or p.suffix != ".lean":
            raise RuntimeError(f"unsafe source path {p}")
        src, dst = PREP / "repo" / p, ROOT / p
        if lc.sha256_file(src) != digest:
            raise RuntimeError(f"prepared source digest mismatch {p}")
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
    return read(PREP / "plan.json")

def compile_cut(roots, output, base=None):
    output.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(ROOT / "tools/lean_compile_closure.py"),
           "--workdir", str(output / "objects"), "--jobs", "2",
           "--source-root", str(G), "--manifest", str(output / "manifest.json")]
    if base:
        cmd += ["--precompiled-manifest", str(base / "manifest.json"),
                "--precompiled-dir", str(base / "objects")]
    cmd += [str(ROOT / r) for r in roots]
    log = output / "lean.log"
    with log.open("w") as f:
        p = subprocess.Popen(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT)
        for line in p.stdout:
            f.write(line)
            f.flush()
            print(line, end="", flush=True)
        if p.wait():
            raise RuntimeError("Lean source closure failed")
    run(sys.executable, "im-results/agent4-raw109/audit_axioms.py", log)
    return read(output / "manifest.json")

def merge(plan):
    output = Path("/tmp/family6-merged")
    obj = output / "objects"
    base = read(COMMON / "manifest.json")
    modules = {}
    roots = {}
    identity = ("source_sha256", "project_imports", "olean_path", "olean_sha256",
                "import_closure_sha256", "module_identity_sha256")
    def take(bundle, expected=None):
        m = read(bundle / "manifest.json")
        if m["schema_version"] != 1 or m["lean_version"] != base["lean_version"] or \
           m["lean_binary"]["sha256"] != base["lean_binary"]["sha256"] or \
           m["proof_source_revision"] != base["proof_source_revision"]:
            raise RuntimeError(f"compiler or source revision mismatch: {bundle}")
        actual = {r["module"] for r in m["roots"]}
        if expected is not None and actual != expected:
            raise RuntimeError(f"unexpected roots for {bundle}: {actual ^ expected}")
        for r in m["roots"]:
            roots[r["module"]] = r
        for e in m["modules"]:
            name = e["module"]
            if name in modules:
                if any(e[k] != modules[name][k] for k in identity):
                    raise RuntimeError(f"module identity conflict: {name}")
            else:
                modules[name] = e
            rel = Path(e["olean_path"])
            if rel.is_absolute() or ".." in rel.parts:
                raise RuntimeError(f"unsafe object path: {rel}")
            source = bundle / "objects" / rel
            if not source.is_file():
                source = COMMON / "objects" / rel
            copy(source, obj / rel, e["olean_sha256"])
    take(COMMON, {Path(plan["common"]).stem})
    for i, group in enumerate(plan["groups"]):
        take(SHARDS / f"raw10-family6-shard-{i}", {Path(p).stem for p in group})
    for name, e in modules.items():
        if any(d not in modules for d in e["project_imports"]):
            raise RuntimeError(f"incomplete dependency closure {name}")
    merged = dict(base)
    merged.update(modules=[modules[k] for k in sorted(modules)],
                  roots=[roots[k] for k in sorted(roots)],
                  module_count=len(modules), precompiled_core=None,
                  label="Family6 complete partition cut (not parent theorem)")
    write(output / "manifest.json", merged)
    print("merged", len(modules), "dependency-closed modules", flush=True)
    return output

def main():
    mode = sys.argv[1]
    if mode == "prepare":
        generate()
        plan = read(OUT / "prepared" / "plan.json")
        compile_cut([plan["common"]], OUT / "common")
    elif mode == "shard":
        plan = restore()
        i = int(sys.argv[2])
        output = OUT / "shard"
        m = compile_cut(plan["groups"][i], output, COMMON)
        # Upload only objects absent from the common closure. Retain the full
        # manifest, so the final linker independently checks all dependencies.
        base = {x["module"]: x for x in read(COMMON / "manifest.json")["modules"]}
        for e in m["modules"]:
            old = base.get(e["module"])
            if old and e["module_identity_sha256"] == old["module_identity_sha256"]:
                (output / "objects" / e["olean_path"]).unlink()
        for p in (output / "objects").rglob("*.lean"):
            p.unlink()
    elif mode == "final":
        plan = restore()
        merged = merge(plan)
        final = OUT / "final"
        m = compile_cut([plan["root"]], final, merged)
        source = ROOT / plan["root"]
        printed = re.findall(r"^#print axioms ([^\s]+)", source.read_text(), re.M)
        if not printed:
            raise RuntimeError("Family6Source has no explicit theorem axiom audit")
        log = (final / "lean.log").read_text()
        names = set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log))
        for name in printed:
            if not any(n == name or n.endswith("." + name) for n in names):
                raise RuntimeError(f"missing final axiom profile: {name}")
        copy(source, final / "Family6Source.lean")
        print("FINAL SOURCE AXIOM GATE:", printed, flush=True)
    else:
        raise ValueError(mode)

if __name__ == "__main__":
    main()
