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
    text = "import OrdinaryQ0Exhaustive\\n" + text
    text = text.replace(
        "open BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree",
        "open BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree\\n"
        "open BB6.Agent5ExactOneHole (OrdinaryBound)",
    )
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



# The explicit halting machine and 202-step run are independently kernel-checked
# in the tracked Raw11Q0Root53Halter203 module, rather than extracted from the
# generated search tree. Its compatibility with the generated parent is
# checked here by exact equality of all twelve slots.
witness = """import Q0Root53Parent
import Raw11Q0Root53Halter203
import OrdinaryQ0Exhaustive

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Q0Root53SharpWitness
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent5ExactOneHole (OrdinaryBound)

theorem same_parent :
    Q0Root53.rootParent = BB6.Agent47Root53Halter203.parent :=
  Q0ExhaustiveTree.sameTable_sound (by decide +kernel)

theorem witness_compatible :
    compatible Q0Root53.rootParent BB6.Agent47Root53Halter203.machine := by
  rw [same_parent]
  exact BB6.Agent47Root53Halter203.compatible_parent

theorem sharp_upper : Cover (OrdinaryBound 203) Q0Root53.rootParent :=
  Q0Root53.sharp_root

/-- Exact ordinary maximum 203, attained on the literal full machine in
Raw11Q0Root53Halter203. The universality comes only from the source-checked
complete exhaustive tree; the experimental 25^5 scan is not trusted. -/
theorem family_exact_203 :
    (∀ m, compatible Q0Root53.rootParent m → OrdinaryBound 203 m) ∧
    (∃ m, compatible Q0Root53.rootParent m ∧ HaltsAfter m 202) :=
  ⟨sharp_upper.sound, ⟨BB6.Agent47Root53Halter203.machine,
    witness_compatible, BB6.Agent47Root53Halter203.halts202⟩⟩

#print axioms same_parent
#print axioms sharp_upper
#print axioms family_exact_203
end Q0Root53SharpWitness
"""
(out / "Q0Root53SharpWitness.lean").write_text(witness)

print("root53 source-derived sharp modules:", counts)
print("attaining complete table: 1RB1RD_1RC1RE_0LA0RF_1LA1LD_---0LC_0LA0RB")
