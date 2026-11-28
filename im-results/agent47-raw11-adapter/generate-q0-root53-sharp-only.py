#!/usr/bin/env python3
"""Build *only* sharp ordinary proof modules atop accepted weighted .olean objects.

The original q0root53 30,793-node source DAG is independently accepted by
CI46109014135; this script never rechecks or edits that DAG. Every sharp
statement is reproved in the kernel using the original exact Tree cert and
the new source-accepted check_sharp theorem (CI46110753510).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "im-results/agent5-weighted-tnf-queue"))
from generate_q0_exhaustive_lean import generate, load  # noqa: E402

assert len(sys.argv) == 3, "usage: script frozen-dataset output-dir"
src, out = map(Path, sys.argv[1:])
meta, initial, _ = load(src)
assert meta["rootId"] == 53 and meta["bound"] == 208
assert "".join(initial) == "1RB1RD1RC1RE0LA---1LA1LD------------"
original = out / "_source-original"
original.mkdir(parents=True, exist_ok=True)
out.mkdir(parents=True, exist_ok=True)
generate(src, original, 49)
decl = re.compile(
    r"^theorem safe_(\w+) : Cover \(WeightedBound 208\) (\w+) :=.*?"
    r"(?=^(?:def|theorem|#print|end)\b|\Z)",
    re.M | re.S,
)
count = 0
for file in sorted(original.glob("Q0Root53*.lean")):
    mod = file.stem
    content = file.read_text()
    if mod == "Q0Root53Base":
        proofs = ["""theorem sym_sharp (p : PartialMachine) (h : sym p = true) :
    Cover (OrdinaryBound 203) p := by
  have he : p = Root53Coverage.table53 := sameTable_sound h
  subst p
  exact .leaf _ (fun m hm =>
    Or.inr (Root53Coverage.never_compatible m hm))"""]
    else:
        proofs = []
        for mat in decl.finditer(content):
            block = mat.group(0).rstrip()
            block = block.replace("theorem safe_", "theorem sharp_", 1)
            block = block.replace(
                "Cover (WeightedBound 208)", "Cover (OrdinaryBound 203)", 1)
            block = block.replace(
                "check_sound 208", "BB6.Agent47OrdinaryQ0Exhaustive.check_sharp 203")
            block = block.replace(
                "split_sound 208", "BB6.Agent47OrdinaryQ0Exhaustive.split_sharp 203")
            block = block.replace("sym_sound", "sym_sharp")
            block = re.sub(r"\bsafe_(\w+)", r"sharp_\1", block)
            proofs.append(block)
        assert len(proofs) == content.count("theorem safe_"), mod
    assert proofs, mod
    count += len(proofs)
    imports = [f"import {mod}"]
    if mod == "Q0Root53Base":
        imports += ["import OrdinaryQ0Exhaustive"]
    else:
        imports += ["import Q0Root53SharpBase"]
    for imported in re.findall(r"^import (Q0Root53Shard\d+)$", content, re.M):
        imports += [f"import {imported.replace('Q0Root53Shard','Q0Root53SharpShard')}"]
    name = mod.replace("Q0Root53", "Q0Root53Sharp", 1)
    body = "\n".join(dict.fromkeys(imports)) + """

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree
open BB6.Agent5ExactOneHole (OrdinaryBound)
namespace Q0Root53

""" + "\n\n".join(proofs) + ("\n#print axioms sharp_root" if mod=="Q0Root53Parent" else "") + """
end Q0Root53
"""
    (out / f"{name}.lean").write_text(body)

assert count >= 26, count
assert (out/"Q0Root53SharpParent.lean").is_file()
assert len(list(out.glob("Q0Root53SharpShard*.lean"))) == 24
# Source-checked literal upper/lower join. This input does not recompile any
# original weighted proof or accept any unverified machine simulation.
witness = """import Q0Root53SharpParent
import Raw11Q0Root53Halter203

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

theorem family_exact_203 :
    (∀ m, compatible Q0Root53.rootParent m → OrdinaryBound 203 m) ∧
    (∃ m, compatible Q0Root53.rootParent m ∧ HaltsAfter m 202) :=
  ⟨sharp_upper.sound, ⟨BB6.Agent47Root53Halter203.machine,
    witness_compatible, BB6.Agent47Root53Halter203.halts202⟩⟩

#print axioms family_exact_203
end Q0Root53SharpWitness
"""
(out/"Q0Root53SharpWitness.lean").write_text(witness)
print("sharp-only proof modules",len(list(out.glob("Q0Root53Sharp*.lean"))),
      "sharp theorem instances",count,"original source untouched, frozen parent 208")
