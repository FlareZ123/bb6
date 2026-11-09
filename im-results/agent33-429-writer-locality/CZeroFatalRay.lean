import BB429Rank
import FirstGateRays
import Lean.Elab.Tactic.Omega

namespace BB429CZeroFatalRay
open BB429 BB429FirstGateRays

/-- An infinite family of synthetic C/0 contiguous-left-block lengths
    whose canonical Junc endpoint falls on the exact first-branch fatal ray. -/
def kRay (n : Nat) : Nat := 12*2^(2*n) - 3*n - 8

/-- The C/0 physical chart's J(0,0,2k) endpoints are exactly the first
    one-step predecessors of Agent30's source-certified u=3 fatal rays. -/
theorem kRay_anc (n : Nat) :
    2*kRay n = 3 + anc 3 (2*n) := by
  have hf := anc_formula 3 (2*n) (by omega)
  have hb := two_pow_ge (2*n)
  unfold kRay
  omega

/-- All these J0 targets halt in the exact 12-branch accelerator, after
    precisely 2n+2 attempted steps. This is a conditional synthetic input:
    no claim that the blank orbit reaches a target is used. -/
theorem junc0_ray_halts (n : Nat) :
    BB429.run (2*n+2) (0, 2*kRay n) = none := by
  have hseed := kRay_anc n
  have hstep : BB429.next (0,3+anc 3 (2*n)) =
      some (3,anc 3 (2*n)) := by
    have hg : 3 ≤ 3+anc 3 (2*n) := by omega
    simp [BB429.next,hg]
  have hrest := ray_halts 3 (2*n) (by omega)
  rw [hseed]
  have ht : 2*n+2 = 1+(2*n+1) := by omega
  rw [ht,BB429.run_add]
  change (BB429.next (0,3+anc 3 (2*n))).bind
    (BB429.run (2*n+1)) = none
  rw [hstep]
  simp only [Option.bind_some]
  exact hrest

/-- The chosen rays are infinite and the parameters strictly increase. -/
theorem kRay_strict (n : Nat) : kRay n < kRay (n+1) := by
  have hpower : 2^(2*(n+1)) = 4*2^(2*n) := by
    rw [show 2*(n+1)=2*n+2 by omega, Nat.pow_add]
    omega
  have hbound := two_pow_ge (2*n)
  unfold kRay
  rw [hpower]
  omega

#print axioms kRay_anc
#print axioms junc0_ray_halts
#print axioms kRay_strict
end BB429CZeroFatalRay
