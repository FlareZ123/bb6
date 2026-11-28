#!/usr/bin/env python3
"""Emit independent TwoSidedAutomata Lean source for Raw36 D1=1LA structured replays."""
import argparse,json,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent7-raw36-b1le"))
from stack_candidates import generate

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--structured",required=True,type=Path)
    ap.add_argument("--out",required=True,type=Path)
    ap.add_argument("--limit",type=int,default=0,
                    help="emit only the lowest-replay-state records when nonzero")
    a=ap.parse_args()
    rows=json.loads(a.structured.read_text())
    assert len(rows)==1343
    if a.limit:
        rows=sorted(rows,key=lambda x:(x[1][-1],x[0]))[:a.limit]
    mapping=generate(rows,a.out,stem="Raw36D112Struct",
                     ns="BB6.Agent18Raw36D112Struct")
    assert len(mapping)==len(rows)
    print("emitted",len(rows),"structured literals")

if __name__=="__main__":
    main()
