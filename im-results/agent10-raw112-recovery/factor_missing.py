#!/usr/bin/env python3
"""Factor only the five still-missing Raw112 child roots, preserving closed nodes."""
from pathlib import Path
from itertools import product
import re
import sys

MOVES = [f"⟨{str(bool(w)).lower()},{str(bool(r)).lower()},{q}⟩"
         for w,r,q in product(range(2),range(2),range(6))]
LIMIT = 6000

def split_children(text, kind):
    fn = "byPartialMove" if kind == "PartialAudit" else "byMove"
    m = re.fullmatch(r"\.split (\d+) (\(\d+,(?:true|false)\)) \("+fn+r" \[\s*(.*)\]\)", text, re.S)
    if not m:
        return None
    body = m[3]
    stack, children, start = [], [], 0
    close = {")":"(", "]":"[", "⟩":"⟨"}
    for i,c in enumerate(body):
        if c in "([⟨":
            stack.append(c)
        elif c in close:
            assert stack.pop() == close[c]
        elif c == "," and not stack:
            children.append(body[start:i].strip())
            start = i+1
    children.append(body[start:].strip())
    assert not stack and len(children) == 24
    return m[1], m[2], children

def factor(path):
    source = path.read_text()
    m = re.fullmatch(r"(.*?)def (kid\d\d_\d\d) : PartialAudit := (.*?)\ntheorem (\w+) : partialCheck (\d+) (.*?) \2 = true := by\s*rw \[← BB6.Agent47Raw111.partialPrefix_eq\]\s*decide\s*(end [^\n]+)\s*", source, re.S)
    assert m, path
    header, kid, tree, check, bound, parent, end = m.groups()
    assert check == kid+"_checked"
    header = header.replace("maxRecDepth 100000", "maxRecDepth 300000")
    written = []
    def emit(tree, parent, suffix, kind):
        name = kid+suffix
        theorem = name+"_checked"
        mod = path.stem+suffix
        func = "partialCheck" if kind == "PartialAudit" else "zipCheck"
        eq = "BB6.Agent47Raw111.partialPrefix_eq" if kind == "PartialAudit" else "BB6.Agent48PrefixAudit.prefixCheck_eq"
        imports = ""
        if kind == "PartialAudit" and tree.startswith(".closed (") and len(tree)>LIMIT:
            # Keep this a closed node: partialResiduals still reduces to [].
            child = emit(tree[len(".closed ("):-1], parent, suffix+"C", "Audit")
            imports = f"import {child[0]}\n"
            body = f"def {name} : PartialAudit := .closed {child[1]}\ntheorem {theorem} : partialCheck {bound} {parent} {name} = true := by\n  exact {child[2]}\n"
        elif len(tree)>LIMIT and (sp := split_children(tree,kind)) is not None:
            n, slot, children = sp
            kids = [emit(t, f"(refine {parent} {slot} (some {mv}))", suffix+f"P{i:02}", kind)
                    for i,(t,mv) in enumerate(zip(children,MOVES))]
            imports = "".join(f"import {x[0]}\n" for x in kids)
            fn = "byPartialMove" if kind == "PartialAudit" else "byMove"
            branches = name+"Branches"
            body = f"def {branches} : Move → {kind} := {fn} [{','.join(x[1] for x in kids)}]\n"
            body += f"theorem {branches}_checked (mv : Move) : {func} {bound} (refine {parent} {slot} (some mv)) ({branches} mv) = true := by\n  rcases mv with ⟨w,r,q⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n"
            body += "\n".join(f"  · exact {kids[12*w+6*r+q][2]}" for q,w,r in product(range(6),range(2),range(2)))+"\n"
            body += f"def {name} : {kind} := .split {n} {slot} {branches}\n"
            body += f"theorem {theorem} : {func} {bound} {parent} {name} = true := by\n  change (zipQueryOK {bound} {parent} {n} {slot} && allMoves (fun mv => {func} {bound} (refine {parent} {slot} (some mv)) ({branches} mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide, allMoves_of _ {branches}_checked⟩\n"
        else:
            body = f"def {name} : {kind} := {tree}\ntheorem {theorem} : {func} {bound} {parent} {name} = true := by\n  rw [← {eq}]\n  decide\n"
        # All witness modules occur by fully-qualified name in the original tree.
        # The kernel still checks every theorem; unused imports only inflate RAM.
        local_header = "\n".join(l for l in header.splitlines()
            if not l.startswith("import ") or l == "import Raw112Base"
            or re.search(r"\b"+re.escape(l[7:])+r"\b",body))+"\n"
        target = path.with_name(mod+".lean")
        target.write_text(imports+local_header+body+"\n"+end+"\n")
        written.append(target)
        return mod, name, theorem
    emit(tree,parent,"","PartialAudit")
    return written

if __name__ == "__main__":
    for name in sys.argv[1:]:
        paths = factor(Path(name))
        print(name, len(paths), max(p.stat().st_size for p in paths), flush=True)
