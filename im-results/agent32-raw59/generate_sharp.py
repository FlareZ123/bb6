#!/usr/bin/env python3
"""Reweight the accepted 0LB audit, without regenerating or replaying traces.

Pass a directory containing the exact accepted Raw59Upgrade0LBKid*.lean
sources and an output directory. The generated Lean modules are checked
against the accepted original audit definitions, so regex parsing is not
a soundness assumption.
"""
from pathlib import Path
import re
import sys

src = Path(sys.argv[1])
outdir = Path(sys.argv[2])
outdir.mkdir(parents=True, exist_ok=True)
HEADER = """set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59Sharp
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent32AuditReweight BB6.Agent32Raw59Upgrade0LB
"""
END = "end BB6.Agent32Raw59Sharp\n"

def split_proof(p, steps, slot, kids, prefix):
    return f"""  change (quickWeight 4136171 {p} {steps} {slot} && allMoves (fun mv => partialWeights 4136171 (refine {p} {slot} (some mv)) ({kids} mv))) = true
  rw [Bool.and_eq_true]
  refine ⟨by decide, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
""" + "".join(f"  · exact {prefix}{q+a:02}\n" for q in range(6) for a in (0,6,12,18))

for i in range(24):
    mod = f"Raw59Upgrade0LBKid{i:02}"
    s = (src / (mod + ".lean")).read_text()
    out = [f"import AuditReweight\nimport {mod}\n", HEADER]
    matches = list(re.finditer(r"^theorem c_(kid\w+) : partialCheck 4200000 (p_\w+) (t_\w+) = true :=", s, re.M))
    assert matches and matches[-1].group(1) == f"kid{i:02}"
    for m in matches:
        n,p,t = m.groups()
        internal = re.search(rf"^def {t} : PartialAudit := \.split (\d+) (\([^\n]+?\)) k_{n}$", s, re.M)
        out.append(f"theorem w_{n} : partialWeights 4136171 {p} {t} = true := by\n")
        if internal:
            steps,slot = internal.groups()
            out.append(split_proof(p, steps, slot, f"k_{n}", f"w_{n}_"))
        else:
            out.append("  decide\n")
    out.append(f"#print axioms w_kid{i:02}\n")
    (outdir/f"Raw59SharpKid{i:02}.lean").write_text("".join(out)+END)

root = "".join(f"import Raw59SharpKid{i:02}\n" for i in range(24))
root += "import AuditReweight\nimport Raw59Upgrade0LBData\n"+HEADER
root += "theorem weights : partialWeights 4136171 p0LB t_root = true := by\n"
root += split_proof("p0LB",8,"(1,true)","k_root","w_kid")
root += """
theorem checkSharp : partialCheck 4136171 p0LB t_root = true :=
  partial_reweight 4200000 4136171 p0LB t_root c_root weights

theorem sharp_bound : ∀ m, compatible p0LB m → WeightedBound 4136171 m := by
  intro m hm
  rcases partialSound 4136171 p0LB t_root p0LB_root p0LB_nohalt checkSharp m hm with h|⟨e,he,_⟩
  · exact h
  · change e ∈ residuals at he
    simp [residuals_empty] at he
#print axioms sharp_bound
"""
(outdir/"Raw59Sharp0LB.lean").write_text(root+END)
