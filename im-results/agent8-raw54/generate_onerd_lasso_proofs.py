#!/usr/bin/env python3
"""Produce original-source Lean checks for Raw54 1RD lasso candidates.

Discovery TSV is untrusted.  The source code and all claimed cycles are rebuilt
as literal partial machines and checked by BB6.Agent8Raw54.OneRDBankAudit.bankCheck.
This deliberately does not rely on precompiled discovery assertions.
"""
from __future__ import annotations
import argparse
import ast
from pathlib import Path

PARENT = "1RB---_1RC---_0RD---_1LD0LE_---1RD_------"
EXPECTED = 671
EXPECTED_CYCLES = 29

def parse(s: str) -> tuple[str, ...]:
    s = s.replace("_", "")
    if len(s) != 36:
        raise ValueError(s)
    out = tuple(s[i:i+3] for i in range(0,36,3))
    for v in out:
        if v != "---" and (len(v) != 3 or v[0] not in "01"
                or v[1] not in "LR" or v[2] not in "ABCDEF"):
            raise ValueError(v)
    return out

def machine(s: str) -> str:
    p = "(fun _ => (none : Option Transition))"
    for i,v in enumerate(parse(s)):
        if v != "---":
            mv = f"⟨{str(v[0]=='1').lower()},{str(v[1]=='R').lower()},{ord(v[2])-65}⟩"
            p = f"(refine {p} ({i//2},{str(bool(i%2)).lower()}) (some {mv}))"
    return p

def read(path: Path):
    seen = set()
    cycles = []
    lines = [x for x in path.read_text().splitlines() if x.strip()]
    if len(lines) != EXPECTED:
        raise ValueError(f"expected {EXPECTED} records; got {len(lines)}")
    parent = parse(PARENT)
    for line in lines:
        spec, payload = line.split("\t",1)
        a = parse(spec)
        if any(x != "---" and x != a[i] for i,x in enumerate(parent)):
            raise ValueError(f"non-refinement of Raw54 1RD parent: {spec}")
        if spec in seen:
            raise ValueError(f"duplicate {spec}")
        seen.add(spec)
        item = ast.literal_eval(payload)
        if not isinstance(item,list) or not item:
            raise ValueError((spec,item))
        if item[0] == "cycle":
            if len(item) != 5:
                raise ValueError(item)
            _,e,k,r,b = item
            if not (type(e) is int and e >= 0 and
                    type(k) is int and 0 < k and
                    type(r) is bool and type(b) is int):
                raise ValueError(item)
            cycles.append((spec,e,k,r,b))
    if len(cycles) != EXPECTED_CYCLES:
        raise ValueError(f"expected {EXPECTED_CYCLES} candidates; got {len(cycles)}")
    return cycles

def render(i:int, c:tuple) -> str:
    spec,e,k,right,b = c
    return f"""import Raw54OneRDBankAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.OneRDLasso{i:02d}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8Raw54.OneRDBankAudit

/-- Literal original-encoding partial table {spec}. -/
abbrev p : PartialMachine := {machine(spec)}
def t : BankAudit := .cycle {e} {k} {str(right).lower()} ({b})

/-- Kernel computation is the security boundary: C++ discovery is untrusted. -/
theorem checked : bankCheck [] 1006 p t = true := by decide +kernel
theorem firstOne : p initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt p := by decide +kernel

/-- If accepted, every full completion of this literal partial table
    is nonhalting (hence satisfies any weighted bound). -/
theorem cover : Cover (WeightedBound 1006) p := by
  apply bankClose [] 1006 p t firstOne nohalt checked
  intro e he
  simp [bankResiduals,t] at he

#print axioms checked
#print axioms cover
end BB6.Agent8Raw54.OneRDLasso{i:02d}
"""

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("lasso",type=Path)
    ap.add_argument("out",type=Path)
    ap.add_argument("--index",type=int,required=True)
    args=ap.parse_args()
    cycles=read(args.lasso)
    i=args.index
    if not 0 <= i < len(cycles):
        raise ValueError(i)
    args.out.mkdir(parents=True,exist_ok=True)
    path=args.out/f"Raw54OneRDLasso{i:02d}.lean"
    path.write_text(render(i,cycles[i]))
    print(f"index={i} table={cycles[i][0]} entry={cycles[i][1]} period={cycles[i][2]} right={cycles[i][3]} boundary={cycles[i][4]}")
    print(f"wrote={path}")

if __name__=="__main__":
    main()
