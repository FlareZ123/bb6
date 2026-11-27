#!/usr/bin/env python3
"""Compile only the recursive source-import closure of one or more Lean proof modules.

Invoked inside the pinned-Cryptid-original source checkout after restorers
have reconstructed the exact original Boundary, DRegular and agent25 modules.
No generated theorem is trusted: every module is compiled by Lean.
"""
import os, re, subprocess, sys, time
from pathlib import Path

if len(sys.argv) < 2:
    raise SystemExit("usage: reproduce-safe-e.py <ModuleName> ...")

dirs = [Path(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
sources = {}
for d in dirs:
    if not d.is_dir():
        print(f"warning: missing import directory: {d}",flush=True)
        continue
    for p in d.glob("*.lean"):
        sources.setdefault(p.stem, p)

print(f"Discovered {len(sources)} modules in {len(dirs)} Lean import roots",flush=True)
roots = sys.argv[1:]
seen, stack, ordered = set(), set(), []
external_prefixes = ("Lean", "Init", "Std", "Mathlib")
def visit(module):
    if module in seen: return
    if module in stack: raise RuntimeError(f"cyclic Lean import: {module}")
    if module not in sources:
        if module.split(".")[0] in external_prefixes: return
        raise FileNotFoundError(f"Lean source for imported module {module} missing; check LEAN_PATH / restored archives")
    stack.add(module)
    for line in sources[module].read_text().splitlines():
        m = re.match(r"^\s*import\s+(.+?)\s*(?:--.*)?$",line)
        if m:
            for imp in m.group(1).split():
                if imp and not imp.startswith("--"):
                    visit(imp)
    stack.remove(module)
    seen.add(module)
    ordered.append(module)

for root in roots: visit(root)
print(f"Actual source import closure: {len(ordered)} modules",flush=True)
for i,module in enumerate(ordered,1):
    path=sources[module]
    start=time.monotonic()
    print(f"[{i}/{len(ordered)}] Lean {module}: {path}",flush=True)
    proc=subprocess.run(["lean","-DmaxRecDepth=55000","-DmaxHeartbeats=100000000",
          "-o",str(path.with_suffix(".olean")),str(path)],stdout=subprocess.PIPE,
          stderr=subprocess.STDOUT,text=True)
    out=proc.stdout or ""
    if module in roots or proc.returncode:
        print(out[-30000:],flush=True)
    elif "sorryAx" in out or "_native.native_decide" in out:
        print(out[-10000:],flush=True)
    print(f"Status: {proc.returncode}, {time.monotonic()-start:.1f}s",flush=True)
    if proc.returncode or "sorryAx" in out or "_native.native_decide" in out:
        raise SystemExit(f"Lean import closure failed at module {module}")
print("Entire source-import closure compiled; targeted proof #print axioms above",flush=True)
