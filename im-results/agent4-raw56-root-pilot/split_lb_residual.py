#!/usr/bin/env python3
"""Split Raw56 parent residual source proof into definition and list algebra.

The huge generated nrtop proof is exactly a definitional change followed
by rewriting 24 kernel-checked child residual equalities. Separating the
obligations reduces simultaneous elaborator state without changing theorem.
"""
import argparse
from pathlib import Path
from split_lb_parent import split_parent, exactly_split, NS

def generate(prep: Path):
    split_parent(prep)
    folder=prep/"E11LB"
    p=folder/"Raw56LBTopResiduals.lean"
    original=p.read_text()
    prefix,rest=exactly_split(original,"theorem nrtop :")
    body,suffix=exactly_split(rest,"\ndef residuals :")
    stmt,proof=exactly_split(body,":= by\n")
    assert "canonicalResiduals ptop 5 ttop" in stmt
    assert stmt.count(" = ")==1
    lhs,rhs=stmt.strip().split(" = ",1)
    lines=[x.strip() for x in proof.strip().splitlines() if x.strip()]
    assert len(lines)==2 and lines[0].startswith("change ") and lines[1].startswith("simp only ["),lines
    change=lines[0][len("change "):]
    assert change.endswith(" = _"),change[-150:]
    intermediate=change[:-len(" = _")]
    ns_end=f"end {NS}\n"
    expand=prefix+f"theorem nrtop_unfold : {lhs} = {intermediate} := by rfl\n#print axioms nrtop_unfold\n"+ns_end
    flatten=prefix+f"theorem nrtop_flat : {intermediate} = {rhs} := by\n  {lines[1]}\n#print axioms nrtop_flat\n"+ns_end
    merged=("import Raw56LBTopResExpand\nimport Raw56LBTopResFlat\n"
            +prefix+f"theorem nrtop : {lhs} = {rhs} := nrtop_unfold.trans nrtop_flat\n"
            +"def residuals :"+suffix)
    output={
      "Raw56LBTopResExpand.lean":expand,
      "Raw56LBTopResFlat.lean":flatten,
      "Raw56LBTopResiduals.lean":merged,
    }
    for name,text in output.items():
        assert text.count(ns_end.strip())==1,name
        (folder/name).write_text(text)
        print("RESIDUAL-SPLIT",name,len(text),flush=True)
    print("DEF-EQ",len(intermediate),"RESULT",len(rhs),"SIMPLIFIER",len(lines[1]),flush=True)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--prep",type=Path,required=True)
    a=ap.parse_args()
    generate(a.prep)

if __name__=="__main__":
    main()
