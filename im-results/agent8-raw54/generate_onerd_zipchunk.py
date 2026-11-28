#!/usr/bin/env python3
"""Generate source-only Lean proof of long first-unknown Raw54 E1=1RD runs.

The Python blank-run simulator is untrusted. Every 1000-transition zipper
checkpoint is a literal kernel-decided theorem, and original-source
Agent50Zipper.join composes them into a full precise first-hole proof.
The final Cover theorem comes from original-source certifiedZip soundness.
"""
from __future__ import annotations
import argparse
from itertools import groupby
from pathlib import Path
from far_mask_cert import parse, term as machine

CASES = [
    ("1RB1RF_1RC0RA_0RD1RB_1LD0LE_1LA1RD_---1RC", 69753, 10),
    ("1RB0RF_1RC0RA_0RD1RB_1LD0LE_1LA1RD_---0LA", 87079, 10),
    ("1RB1RF_1RC0RA_0RD1RB_1LD0LE_1LA1RD_---0LC", 87079, 10),
]
CHUNK = 1000
SCORE = 100000

def compact(xs: list[bool]) -> str:
    if not xs:
        return "([] : List Bool)"
    out=[]
    for value, it in groupby(xs):
        n=sum(1 for _ in it)
        v=str(bool(value)).lower()
        out.append(f"[{','.join([v]*n)}]" if n<=2
                   else f"(List.replicate {n} {v})")
    return "(" + " ++ ".join(out) + ")"

def snapshot(code: str, n: int):
    p=parse(code)
    q,h,l,r=0,0,[],[]
    snapshots=[(0,(q,h,l.copy(),r.copy()))]
    for i in range(1,n+1):
        slot=2*q+(int(l[0]) if l else 0)
        m=p[slot]
        if m is None:
            raise ValueError(f"early first unknown at step {i-1}: {slot}")
        w,right,nxt=m
        if right:
            l=[r[0] if r else False, bool(w)]+l[1:]
            r=r[1:]
            h+=1
        else:
            l=l[1:]
            r=[bool(w)]+r
            h-=1
        q=nxt
        if i%CHUNK==0 or i==n:
            snapshots.append((i,(q,h,l.copy(),r.copy())))
    slot=2*q+(int(l[0]) if l else 0)
    if p[slot] is not None:
        raise ValueError("the exact claimed first-unknown slot is still assigned")
    return snapshots,slot

def generate(idx: int) -> str:
    code,n,expected_slot=CASES[idx]
    a,slot=snapshot(code,n)
    if slot!=expected_slot:
        raise ValueError((code,n,slot,expected_slot))
    ns=f"OneRDZipLate{idx}"
    lines=[
        "import Raw54OneRDBankAudit",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "set_option autoImplicit false",
        f"namespace BB6.Agent8Raw54.{ns}",
        "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6.Agent50TNFPilot",
        f"/-- Literal table {code}. Independent snapshots are untrusted input. -/",
        f"abbrev p : PartialMachine := {machine(parse(code))}",
    ]
    for i,(t,(q,h,l,r)) in enumerate(a):
        if i==0:
            continue
        prev="start" if i==1 else f"cfg{i-1}"
        dur=t-a[i-1][0]
        lines.append(f"def cfg{i} : BB6Coverage.Agent50Zipper.Z := ⟨{q},{h},{compact(l)},{compact(r)}⟩")
        lines.append(f"theorem segment{i} : zrun p {dur} {prev} = some cfg{i} := by decide +kernel")
        if i==1:
            lines.append(f"theorem prefix{i} : zrun p {t} start = some cfg{i} := segment{i}")
        else:
            lines.append(f"""theorem prefix{i} : zrun p {t} start = some cfg{i} := by
  have H := BB6Coverage.Agent50Zipper.join prefix{i-1} segment{i}
  simpa only [show {a[i-1][0]}+{dur} = {t} by decide] using H""")
    last=len(a)-1
    s=f"({slot//2},{str(bool(slot%2)).lower()})"
    lines.extend([
        f"""/-- Exact blank-run first query, checked in {last} bounded segments. -/
theorem query : zipQueryOK {SCORE} p {n} {s} = true := by
  unfold zipQueryOK zipRead
  rw [prefix{last}]
  decide +kernel""",
        f"theorem rest : restOK p {s} = true := by decide +kernel",
        "theorem firstOne : p initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel",
        """theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro x
  rcases x with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases b <;> decide +kernel""",
        f"""theorem checked : zipCheck {SCORE} p (.last {n} {s}) = true := by
  exact (Bool.and_eq_true _ _).mpr ⟨query, rest⟩""",
        f"""/-- Every compatible completion has weighted score at most 100000. -/
theorem cover : Cover (WeightedBound {SCORE}) p := by
  apply Cover.leaf
  intro m hm
  exact (certifiedZip {SCORE} p (.last {n} {s}) firstOne nohalt checked).sound m hm""",
        f"#print axioms prefix{last}",
        "#print axioms cover",
        f"end BB6.Agent8Raw54.{ns}"
    ])
    return "\n".join(lines)+"\n"

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--index",type=int,required=True,choices=range(len(CASES)))
    ap.add_argument("--out",type=Path,required=True)
    x=ap.parse_args()
    x.out.parent.mkdir(parents=True,exist_ok=True)
    text=generate(x.index)
    x.out.write_text(text)
    print(f"generated {x.out}: {len(text)} chars, {CASES[x.index][1]} checked blank steps, exactly one hole")

if __name__=="__main__":
    main()
