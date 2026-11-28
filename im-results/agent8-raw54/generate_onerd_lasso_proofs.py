#!/usr/bin/env python3
"""Replay Raw54 1RD residual cycles or first-unknown halting leaves in Lean.

The C++ TSV is untrusted. Every table is rebuilt as a literal partial machine.
Only Lean kernel-checked bankCheck, plus original-source bankClose, establish
the resulting Cover theorem. Cycle records represent nonhalting families;
lastCandidate records are bounded halting-at-first-hole families.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

PARENT = "1RB---_1RC---_0RD---_1LD0LE_---1RD_------"
EXPECTED = 671
EXPECTED_CYCLES = 29
EXPECTED_LAST = 14

def parse(s: str) -> tuple[str, ...]:
    s = s.replace("_", "")
    if len(s) != 36:
        raise ValueError(s)
    out = tuple(s[i:i+3] for i in range(0,36,3))
    for v in out:
        if v != "---" and (v[0] not in "01"
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

def read(path: Path) -> dict[str,list[tuple]]:
    seen = set()
    cycles = []
    lasts = []
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
        item = json.loads(payload)
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
        elif item[0] == "lastCandidate":
            if len(item) != 3:
                raise ValueError(item)
            _,n,s = item
            if not (type(n) is int and 0 <= n < 39447 and
                    type(s) is int and 0 <= s < 12 and a[s] == "---"):
                raise ValueError(item)
            lasts.append((spec,n,s))
        elif item[0] != "open":
            raise ValueError(item)
    if len(cycles) != EXPECTED_CYCLES or len(lasts) != EXPECTED_LAST:
        raise ValueError(f"expected {EXPECTED_CYCLES}/{EXPECTED_LAST} cycles/last; got {len(cycles)}/{len(lasts)}")
    return {"cycle": cycles, "last": lasts}

def render(i:int, c:tuple, kind:str) -> str:
    if kind == "cycle":
        spec,e,k,right,b = c
        audit = f".cycle {e} {k} {str(right).lower()} ({b})"
        bound = 1006
        ns = f"OneRDLasso{i:02d}"
        desc = "Every compatible machine has an infinite side cycle."
    else:
        spec,n,s = c
        audit = f".last {n} ({s//2},{str(bool(s%2)).lower()})"
        bound = 39447
        ns = f"OneRDLast{i:02d}"
        desc = "Every compatible machine reaches the final unassigned slot before the bound."
    return f"""import Raw54OneRDBankAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace BB6.Agent8Raw54.{ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8Raw54.OneRDBankAudit

/-- Literal original-encoding partial table {spec}. -/
abbrev p : PartialMachine := {machine(spec)}
def t : BankAudit := {audit}

/-- Source-level checker is the security boundary: C++ discovery is untrusted. -/
theorem checked : bankCheck [] {bound} p t = true := by decide +kernel
theorem firstOne : p initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases b <;> decide +kernel

/-- {desc} This proves its Cover at the stated weighted score. -/
theorem cover : Cover (WeightedBound {bound}) p := by
  apply bankClose [] {bound} p t firstOne nohalt checked
  intro e he
  simp [bankResiduals,t] at he

#print axioms checked
#print axioms cover
end BB6.Agent8Raw54.{ns}
"""

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("lasso",type=Path)
    ap.add_argument("out",type=Path)
    ap.add_argument("--kind",choices=["cycle","last"],default="cycle")
    ap.add_argument("--index",type=int,required=True)
    args=ap.parse_args()
    cases=read(args.lasso)[args.kind]
    i=args.index
    if not 0 <= i < len(cases):
        raise ValueError(i)
    args.out.mkdir(parents=True,exist_ok=True)
    ns = "Lasso" if args.kind == "cycle" else "Last"
    path=args.out/f"Raw54OneRD{ns}{i:02d}.lean"
    path.write_text(render(i,cases[i],args.kind))
    print(f"kind={args.kind} index={i} record={cases[i]}")
    print(f"wrote={path}")

if __name__=="__main__":
    main()
