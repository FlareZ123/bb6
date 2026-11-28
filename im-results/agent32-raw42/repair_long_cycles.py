#!/usr/bin/env python3
"""Replace the three exact long-replay failures by kernel-checked segmented cycles.

Input is the frozen generated source directory. The Python simulator produces
only witnesses; Lean checks the full table equality, every exact replay
segment, their composition, and the original directional-cycle soundness
theorem. No trusted execution, native_decide or change to the checker.
"""
import re
from pathlib import Path

CASES = {
    "1LB": [("Raw421LBClosedRoot_10_16Small", "pRoot_10_16_05_08", 14, 69825, -67)],
    "1LC": [("Raw421LCClosedRoot_10_11_18", "pRoot_10_11_18_14", 8, 20380, 338),
            ("Raw421LCClosedRoot_10_11Small_08", "pRoot_10_11_08_18", 21, 17246, 320)],
}

def bit(b):
    return str(bool(b)).lower()

def fmt(z):
    q, l, r, h = z
    return f"⟨⟨{q},{l},{r}⟩,({h})⟩"

def repair(g: Path, branch: str, remaining: set[str], accepted: set[str]):
    changes = {}
    for module, root, index, entry, boundary in CASES.get(branch, []):
        if module in accepted:
            continue
        assert module in remaining, (module, "missing exact failing root")
        path = g / (module + ".lean")
        text = path.read_text()
        defs = dict(re.findall(r"^abbrev (\w+) := (.*)$", text, re.M))

        def expand(name):
            if name == "p":
                return "p"
            return re.sub(r"\bpRoot[\d_]+\b", lambda m: "(" + expand(m[0]) + ")", defs[name])

        stem = root[1:]
        pat = r"^def t" + stem + r" : Cut := \.split \d+ \((\d),(true|false)\) \(byMoveCut \[\n(.*?)\]\)"
        m = re.search(pat, text, re.M | re.S)
        assert m, (module, root)
        q, b, body = m.groups()
        children = body.splitlines()
        witness = f".closed (.cycle {entry} 1 false ({boundary}))"
        assert len(children) == 24 and children[index].rstrip(",") == witness
        assert children.count(witness + ",") + children.count(witness) == 1
        w, r, dest = index // 12, index // 6 % 2, index % 6
        expr = f"refine ({expand(root)}) ({q},{b}) (some ⟨{bit(w)},{bit(r)},{dest}⟩)"

        # Raw42 and its chosen B1 child. Every reconstructed entry is checked
        # against the exact refinement in fast_eq below.
        table = [(1,1,1), None, (1,1,2), (1,0,1 if branch == "1LB" else 2),
                 (0,1,3), None, (1,0,3), (0,0,1), None, None, None, None]
        for q,b,w,r,d in re.findall(r"\((\d),(true|false)\) \(some ⟨(true|false),(true|false),(\d)⟩\)", expr):
            table[2*int(q)+(b=="true")] = (int(w=="true"),int(r=="true"),int(d))

        def step(z):
            q,l,r,h = z
            w,rt,d = table[2*q+l%2]
            if rt:
                return d,r%2+2*(w+2*(l//2)),r//2,h+1
            return d,l//2,w+2*r,h-1

        name = f"Chunk{branch}{entry}"
        segmod, joinmod = name+"Seg", name+"Join"
        assert not {segmod, joinmod} & accepted
        header = [
            "set_option maxRecDepth 100000",
            "set_option maxHeartbeats 0",
            "set_option linter.defProp false",
            f"namespace {name}",
            "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent32PartialCut BB6.Agent32PackedClosed BB6.Agent32Raw59QuickWeight BB6.Agent3PackedCycle BB6Coverage.Agent13PackedZipper",
            f"open BB6.Agent32Raw42{branch}.Closed",
        ]
        lines = [f"import Raw42{branch}ClosedBase", *header,
            "theorem runH_add (p : PartialMachine) (n k : Nat) (z : H) : runH p (n+k) z = (runH p n z).bind (runH p k) := by",
            "  induction n generalizing z with",
            "  | zero => simp [runH]",
            "  | succ n ih =>",
            "    rw [show n+1+k=n+k+1 by omega]",
            "    simp only [runH]",
            "    cases stepH p z with",
            "    | none => rfl",
            "    | some t => exact ih t",
            "theorem joinH {p : PartialMachine} {n k : Nat} {a b c : H} (h : runH p n a = some b) (g : runH p k b = some c) : runH p (n+k) a = some c := by",
            "  rw [runH_add,h]; exact g",
            f"abbrev table : PartialMachine := {expr}",
            "def fastTable : PartialMachine := fun s => match s.1.val, s.2 with"]
        for i,v in enumerate(table):
            if v is not None:
                w,r,d = v
                lines.append(f"  | {i//2}, {bit(i%2)} => some (some ⟨{bit(w)},{bit(r)},{d}⟩)")
        lines += ["  | _, _ => none",
            "theorem fast_eq : fastTable = table := by",
            "  funext s",
            "  obtain ⟨⟨q,hq⟩,b⟩ := s",
            "  have h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
            "  rcases h with h|h|h|h|h|h <;> subst q <;> cases b <;> rfl"]
        z, time, segments = (0,0,0,0), 0, []
        while time < entry:
            k = min(2048, entry-time)
            a = z
            for _ in range(k):
                z = step(z)
            segments.append((k,a,z))
            time += k
        for i,(k,a,b) in enumerate(segments):
            lines.append(f"theorem seg{i} : runH fastTable {k} {fmt(a)} = some {fmt(b)} := by decide")
        lines.append(f"end {name}")
        joins = [f"import {segmod}", *header]

        def combine(lo, hi):
            if hi-lo == 1:
                return f"seg{lo}"
            mid = (lo+hi)//2
            a,b = combine(lo,mid),combine(mid,hi)
            j = f"j{lo}_{hi}"
            # Inferred proof type prevents elaboration from unfolding runH
            # on the entire concrete numeral just to solve metavariables.
            joins.append(f"def {j} := joinH {a} {b}")
            return j

        j = combine(0,len(segments))
        joins += [
            "theorem live : ∀ m, compatible table m → NeverHalts m := by",
            f"  apply cycleH_sound table {entry} 1 false ({boundary}) (by decide)",
            "  unfold cycleH",
            f"  rw [← fast_eq, show runH fastTable {entry} startH = some {fmt(z)} from (by simpa only [Nat.reduceAdd, startH, startP] using {j})]",
            "  decide",
            "#print axioms live",
            f"end {name}"]
        children[index] = f".closed (.proven {name}.table {name}.live)" + ("," if children[index].endswith(",") else "")
        start, end = m.span(3)
        revised = f"import {joinmod}\n" + text[:start] + "\n".join(children) + text[end:]
        (g/(segmod+".lean")).write_text("\n".join(lines)+"\n")
        (g/(joinmod+".lean")).write_text("\n".join(joins)+"\n")
        path.write_text(revised)
        changes[module] = [segmod, joinmod]
    return changes
