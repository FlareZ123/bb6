#!/usr/bin/env python3
"""Reconstruct the ten certificate trees from the frozen Box12 source bundle.

Run after the Box12 recovery with --work pointing to its extracted source/
object directory.  This generator is not trusted by the proof: arbitrary
trees are valid inputs to TreeLift.residuals_sound and Box11Lift.source_branch_sound.
"""
import argparse
import re
from pathlib import Path

ES = (0, 3, 4, 12, 18, 20, 21, 22, 23, 24)

def generate(work, e):
    splitdefs = {}
    for fn in sorted(work.glob(f"tree/Box12E{e}S*.lean")):
        txt = fn.read_text()
        for match in re.finditer(r"^theorem node(\d+) [^\n]* := by\n(.*?)(?=^theorem |^def |^end |\Z)", txt, re.M | re.S):
            id, body = match.groups()
            if "apply split_sound" not in body:
                continue
            q, b = re.search(r"apply split_sound[^\n]*?\) \((\d+),(true|false)\)", body).groups()
            ids = re.findall(r"apply node(\d+) m hm", body)
            assert len(ids) == 25
            assert all(int(i) > int(id) for i in ids)
            splitdefs[id] = (q, b, ids)

    def expr(q, b, ids):
        return f".split ({q},{b}) #[" + ",".join("treenode"+i for i in ids) + "]"

    txt = (work / f"tree/Box12E{e}.lean").read_text()
    roots = re.findall(r"apply node(\d+) m hm", txt)
    lines = [f"def treenode{id} : Tree := {expr(q,b,ids)}"
             for id,(q,b,ids) in sorted(splitdefs.items(), key=lambda kv:-int(kv[0]))]
    if roots:
        assert len(roots) == 25
        q,b = re.search(r"apply split_sound[^\n]*?\) \((\d+),(true|false)\)", txt).groups()
        root = expr(q,b,roots)
    else:
        root = "treenode" + re.search(r"def treenode(\d+)",txt)[1]
    source = f"import Box11Lift\nimport Box12E{e}\nnamespace BB6.Agent48Box11Lift\nopen BB6.Agent48Box12\n" + "\n".join(lines) + f"""
def liftedE{e} : Tree := {root}
def residualE{e} : List (Array Nat) := branchResiduals 200 {e} liftedE{e}
#eval (residualE{e}.length, (residualE{e}.map mass).sum)
end BB6.Agent48Box11Lift
"""
    (work / f"LiftE{e}.lean").write_text(source)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--e", type=int, choices=ES)
    args = p.parse_args()
    for e in ES if args.e is None else (args.e,):
        generate(args.work,e)

if __name__ == "__main__":
    main()
