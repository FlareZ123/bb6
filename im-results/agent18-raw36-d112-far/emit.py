#!/usr/bin/env python3
"""Emit original-source Lean FAR theorems for the exact Raw36 D1=1LA reuse mapping."""
import argparse,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent7-raw36-transfer"))
from emit import masks

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--found",required=True,type=Path)
    ap.add_argument("--out",required=True,type=Path)
    ap.add_argument("--chunk",type=int,default=10)
    ap.add_argument("--max-d",type=int,default=20)
    a=ap.parse_args()
    rows=[tuple(line.split("\t")) for line in a.found.read_text().splitlines() if line.strip()]
    rows=[r for r in rows if (len(r[1])-1)//2<=a.max_d]
    assert len(rows)==len({r[0] for r in rows})
    a.out.mkdir(parents=True,exist_ok=True)
    for j in range(0,len(rows),a.chunk):
        part=rows[j:j+a.chunk]
        mod=f"Raw36D112FAR{j//a.chunk:03d}"
        ns=f"BB6.Agent18Raw36D112FAR{j//a.chunk:03d}"
        lines=["import ThreeHoleAudit","set_option maxRecDepth 100000",
               "set_option maxHeartbeats 0",f"namespace {ns}",
               "open BB6Coverage BB6.Agent31ThreeHole"]
        for local,(table,code) in enumerate(part):
            idx=j+local; rev,n,dfa,t0,t1,z=masks(code,table); raw=table.replace("_","")
            lines += [f"namespace M{idx}",
                      "def table : PartialMachine := fun s =>\n  match s.1.val,s.2 with"]
            for k in range(12):
                mv=raw[3*k:3*k+3]
                if mv!="---":
                    lines.append(
                      f"  | {k//2},{str(bool(k%2)).lower()} => some (some "
                      f"⟨{str(mv[0]=='1').lower()},{str(mv[1]=='R').lower()},{ord(mv[2])-65}⟩)")
            lines += ["  | _,_ => none",
                      f"def cert : FAR.Data {n} := ⟨0,{dfa},{t0},{t1},{z}⟩",
                      "theorem never : ∀ m, compatible table m → NeverHalts m :=",
                      f"  farSound table {str(bool(rev)).lower()} cert (by decide +kernel)",
                      "#print axioms never",f"end M{idx}"]
        lines.append(f"end {ns}")
        (a.out/(mod+".lean")).write_text("\n".join(lines)+"\n")
    print(f"emitted {len(rows)} literal FAR theorems in {(len(rows)+a.chunk-1)//a.chunk} modules")

if __name__=="__main__":
    main()
