#!/usr/bin/env python3
"""Attach a sharp ordinary-step proof to the *frozen* exact q0-root53 tree.

No new BB6 search or heuristic trace classification: all ordinary proofs
reuse the same source-checked certificates from Agent5's 30,793-node witness.
Input is the unpacked q0-root53-generated-source artifact (15115810979).
Output may be compiled with lean_compile_closure.py and Lean 4.36.0-rc2.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "im-results/agent5-weighted-tnf-queue"
sys.path.insert(0, str(SOURCE))
from generate_q0_exhaustive_lean import generate, load  # noqa: E402

if len(sys.argv) != 3:
    raise SystemExit("usage: generate-q0-root53-sharp.py FROZEN_SOURCE_DIR OUTPUT_DIR")
src, out = map(Path, sys.argv[1:])
meta, initial, tree = load(src)
assert meta["rootId"] == 53 and meta["bound"] == 208, meta
assert "".join(initial) == "1RB1RD1RC1RE0LA---1LA1LD------------"

generate(src, out, 49)

decl = re.compile(
    r"^theorem safe_(\w+) : Cover \(WeightedBound 208\) (\w+) :=.*?"
    r"(?=^(?:def|theorem|#print|end)\b|\Z)",
    re.M | re.S,
)


def sharpen(text):
    copies = []
    for m in decl.finditer(text):
        s = m.group(0).rstrip()
        assert "longSym" not in s, "source uses long-trace branches"
        s = s.replace("theorem safe_", "theorem sharp_", 1)
        s = s.replace("Cover (WeightedBound 208)", "Cover (OrdinaryBound 203)", 1)
        s = s.replace(
            "check_sound 208", "BB6.Agent47OrdinaryQ0Exhaustive.check_sharp 203"
        )
        s = s.replace("sym_sound", "sym_sharp")
        s = s.replace(
            "split_sound 208", "BB6.Agent47OrdinaryQ0Exhaustive.split_sharp 203"
        )
        s = re.sub(r"\bsafe_(\w+)", r"sharp_\1", s)
        copies.append(s)
    assert text.count("theorem safe_") == len(copies), (
        text.count("theorem safe_"), len(copies)
    )
    header = "import OrdinaryQ0Exhaustive\nopen BB6.Agent5ExactOneHole (OrdinaryBound)\n"
    text = header + text
    if "theorem sym_sound" in text:
        base_sharp = """
theorem sym_sharp (p : PartialMachine) (h : sym p = true) :
    Cover (OrdinaryBound 203) p := by
  have he : p = Root53Coverage.table53 := sameTable_sound h
  subst p
  exact .leaf _ (fun m hm =>
    Or.inr (Root53Coverage.never_compatible m hm))
"""
        assert not copies
        copies.append(base_sharp)
    assert text.count("end Q0Root53") == 1
    text = text.replace(
        "end Q0Root53",
        "\n\n".join(copies)
        + ("\n#print axioms sharp_root\n" if "theorem sharp_root" in "\n".join(copies) else "")
        + "\nend Q0Root53",
    )
    return text, len(copies)


counts = {}
for file in sorted(out.glob("Q0Root53*.lean")):
    text, num = sharpen(file.read_text())
    counts[file.name] = num
    file.write_text(text)
assert counts["Q0Root53Base.lean"] == 1
assert counts["Q0Root53Parent.lean"] == 1
assert len([f for f in counts if re.fullmatch(r"Q0Root53Shard\d+\.lean", f)]) == 24


# An independent exhaustive C++ simulation of the 25^5 full completions
# identified this 203-step halter. The simulation is NOT a trusted proof:
# run202, first_hole202 and extends_parent below are all kernel-decided.
late_literal = "1RB1RD_1RC1RE_0LA0RF_1LA1LD_---0LC_0LA0RB"
late_string = late_literal.replace("_", "")
late_table = tuple(late_string[i:i+3] for i in range(0,36,3))
score,slot = 202,8
assert len(late_table) == 12 and late_table[slot] == "---"

def flag(b):
    return "true" if b else "false"

rows = ["def late : PartialMachine := fun (q,b) => match q.val,b with"]
for i, action in enumerate(late_table):
    if action != "---":
        rows.append(
            f"  | {i//2},{flag(i%2)} => some (some "
            f"⟨{flag(action[0]=='1')},{flag(action[1]=='R')},"
            f"{ord(action[2])-65}⟩)"
        )
rows.append("  | _,_ => none")

witness = """import Q0Root53Parent
import OrdinaryQ0Exhaustive

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q0Root53SharpWitness
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent5ExactOneHole (OrdinaryBound)

""" + "\n".join(rows) + """

def machine : Machine := weightedTNFDefaultCompletion late
def at202 : FinRayCfg := (finitePartialRun late 202 finiteBlank).getD finiteBlank

theorem run202 : finitePartialRun late 202 finiteBlank = some at202 := by decide +kernel
theorem first_hole202 : late (readSlot (embedFinRay at202)) = none := by decide +kernel
theorem no_assigned_halt : weightedTNFNoAssignedHalt late := by decide +kernel

theorem halts202 : HaltsAfter machine 202 := by
  apply (weightedTNF_halt_iff_firstHole late no_assigned_halt 202).mpr
  exact ⟨embedFinRay at202,
    Q0ExhaustiveTree.finite_known late 202 at202 run202,
    first_hole202⟩

theorem extends_parent : compatible Q0Root53.rootParent machine := by decide +kernel

theorem sharp_upper : Cover (OrdinaryBound 203) Q0Root53.rootParent :=
  Q0Root53.sharp_root

/-- Exact maximum 203 ordinary steps for all halting completions of the
five-hole q0-root53 cylinder, attained by the literal machine above. -/
theorem family_exact_203 :
    (∀ m, compatible Q0Root53.rootParent m → OrdinaryBound 203 m) ∧
    (∃ m, compatible Q0Root53.rootParent m ∧ HaltsAfter m 202) :=
  ⟨sharp_upper.sound, ⟨machine, extends_parent, halts202⟩⟩

#print axioms halts202
#print axioms sharp_upper
#print axioms family_exact_203
end Q0Root53SharpWitness
"""
(out / "Q0Root53SharpWitness.lean").write_text(witness)

print("root53 sharp generated modules:", counts)
print("chosen halter: ordinary steps=203, first-hole index=202,"
      " holes_before_assignment=", late_table.count("---"),
      "slot=", slot,
      "partial_table=", "_".join(
          "".join(late_table)[i:i+6] for i in range(0,36,6)
      ))
