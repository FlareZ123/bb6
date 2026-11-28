#!/usr/bin/env python3
"""Produce a trusted-checkable six-leaf consumer WITHOUT importing the huge parent.

The sole mathematical premise is the authentic six-residual theorem that the
43,348-leaf exhaustive source graph will eventually establish. The table
definitions are extracted literally from that frozen prepared source.
"""
import argparse
import hashlib
from pathlib import Path

HARD=(21049,23706,39232,39234,39233,42763)
PARENT="∀ m : Machine, TNFQuotientCompatible p m → WeightedBound 1000000 m ∨ ∃ q : PartialMachine, q ∈ hardTables ∧ TNFQuotientCompatible q m"

def once(text, old, new):
    n=text.count(old)
    assert n==1,(old[:75],n)
    return text.replace(old,new,1)

def generate(prep: Path, consumer: Path, out: Path):
    reduced=(prep/"E11LB"/"Raw56LBE11LBReduced.lean").read_text()
    src=consumer.read_text()
    definitions=[]
    for i in HARD:
        start=f"def table{i} : PartialMachine :="
        end=f"theorem eq{i} :"
        assert reduced.count(start)==1 and reduced.count(end)==1,i
        a=reduced.index(start)
        b=reduced.index(end,a)
        d=reduced[a:b]
        assert d.count(f"def table{i}")==1
        definitions.append(d)
    tables="\n".join(definitions)+"\n"+(
        "def hardTables : List PartialMachine := ["
        +",".join(f"table{i}" for i in HARD)+"]\n\n"
    )
    src=once(src,"import Raw56LBE11LBReduced","import Raw56LBE11LBBase")
    src=once(src,
       "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier\n\n",
       "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier\n\n"+tables)
    src=once(src,
       "theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) :",
       f"theorem all_quotient (hparent : {PARENT}) (m : Machine) (hm : TNFQuotientCompatible p m) :")
    src=once(src,"rcases reduced_quotient m hm with","rcases hparent m hm with")
    src=once(src,
       "theorem all : Cover (WeightedBound 1000000) p :=",
       f"theorem all (hparent : {PARENT}) : Cover (WeightedBound 1000000) p :=")
    src=once(src,
       "Cover.leaf p (fun m hm => all_quotient m (compatible_quotient hm))",
       "Cover.leaf p (fun m hm => all_quotient hparent m (compatible_quotient hm))")
    assert "import Raw56LBE11LBReduced" not in src
    assert "reduced_quotient m hm" not in src
    assert src.count("theorem all_quotient")==1
    assert src.count("theorem all (hparent")==1
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(src)
    print("CONDITIONAL",out,len(src),hashlib.sha256(src.encode()).hexdigest(),flush=True)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--prep",type=Path,required=True)
    ap.add_argument("--consumer",type=Path,default=Path(__file__).parent/"Raw56LBCompleteHybrid.lean")
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    generate(a.prep,a.consumer,a.out)

if __name__=="__main__":
    main()
