import BB429InverseKernel
import BB429FiniteAvoidance
import Lean.Elab.Tactic.Omega

/-!
# Additional 29 complete branch-29 q(mod2048) root exclusions

Previously surviving q(mod1024) classes are split into q(mod2048) classes.
Twenty-nine of the sixty new classes have exact infinite symbolic inverse
certificates after shifting the affine parameter by 2048. Of their 29
small representatives, 27 have direct original-source inverse certificates
and the remaining two (63 and 767) are globally excluded by an exact
finite blank-prefix checker and monotone-rank cutoff.

Combining this with Agent18's accepted 38/1024 roster and Agent22's
eight extra 1024-class exclusions leaves 31/2048 possibilities.
This theorem itself certifies the 29 excluded classes, not a halt decision.
-/

namespace BB429Branch29Extra2048
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def extra2048 : List Nat :=
  [63,82,186,202,258,319,386,458,642,767,826,831,911,970,
   1026,1135,1151,1263,1362,1423,1519,1594,1599,1679,1738,
   1874,1903,1919,1978]
private def finiteRoots : List Nat := [63,767]
private def directRoots : List Nat :=
  [82,186,202,258,319,386,458,642,826,831,911,970,
   1026,1135,1151,1263,1362,1423,1519,1594,1599,1679,1738,
   1874,1903,1919,1978]

private theorem extra_partition :
    extra2048.all (fun r => decide (r ∈ directRoots ∨ r ∈ finiteRoots)) = true := by
  decide

private def single (r : Nat) : BB429Kernel.Affine :=
  ⟨0,32*r+29,0,64*r+55⟩
private theorem direct_cert :
    directRoots.all (fun r => BB429Kernel.cert 16 (single r)) = true := by
  decide +kernel

private theorem finite_run :
    BB429.run 23570 (0,0) = some (117,98057) := by
  decide +kernel
private theorem finite_avoid :
    finiteRoots.all (fun r => BB429FiniteAvoidance.avoid
      (32*r+29,64*r+55) 23570 (0,0)) = true := by
  decide +kernel

private theorem small_cut (r : Nat) (hr : r ∈ extra2048) :
    ¬BB429NewResidue.Reach (32*r+29) (64*r+55) := by
  have hpart : r ∈ directRoots ∨ r ∈ finiteRoots :=
    of_decide_eq_true ((List.all_eq_true.mp extra_partition) r hr)
  rcases hpart with hd | hf
  · have hc : BB429Kernel.cert 16 (single r) = true :=
      (List.all_eq_true.mp direct_cert) r hd
    have hnot := BB429Kernel.cert_sound 16 (single r) 0 hc
    simpa only [BB429Kernel.va,BB429Kernel.vb,single,Nat.mul_zero,Nat.zero_add] using hnot
  · have hbound : r ≤ 767 := by
      simp [finiteRoots] at hf
      rcases hf with h|h <;> omega
    have hav : BB429FiniteAvoidance.avoid
        (32*r+29,64*r+55) 23570 (0,0) = true :=
      (List.all_eq_true.mp finite_avoid) r hf
    have hboundrank : BB429.rank (32*r+29,64*r+55) <
        BB429.rank (117,98057) := by
      simp only [BB429.rank]
      omega
    exact BB429FiniteAvoidance.no_reach_of_avoid
      (32*r+29,64*r+55) 23570 (0,0) (117,98057)
      finite_run hav hboundrank

private def shifted (r : Nat) : BB429Kernel.Affine :=
  ⟨65536,32*(2048+r)+29,131072,64*(2048+r)+55⟩

private theorem large_cert :
    extra2048.all (fun r => BB429Kernel.cert 16 (shifted r)) = true := by
  decide +kernel

private theorem large_cut (q r : Nat) (hr : q%2048 = r)
    (hq : 2048 ≤ q) (hmem : r ∈ extra2048) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  let t := q/2048-1
  have hqeq : q = 2048*(t+1)+r := by dsimp [t]; omega
  have hx : BB429Kernel.va (shifted r) t = 32*q+29 := by
    simp only [BB429Kernel.va,shifted]
    omega
  have hy : BB429Kernel.vb (shifted r) t = 64*q+55 := by
    simp only [BB429Kernel.vb,shifted]
    omega
  have hc : BB429Kernel.cert 16 (shifted r) = true :=
    (List.all_eq_true.mp large_cert) r hmem
  intro hroot
  have hs : BB429NewResidue.Reach
      (BB429Kernel.va (shifted r) t) (BB429Kernel.vb (shifted r) t) := by
    simpa only [hx,hy] using hroot
  exact (BB429Kernel.cert_sound 16 (shifted r) t hc) hs

/-- 29 previously surviving mod2048 cylinders are uniformly excluded
from the genuine blank-root accelerator. The range split is exhaustive
for every q and the finite roots use a monotone-rank cutoff. -/
theorem twenty_nine_cylinders_unreachable (q : Nat)
    (hq : q%2048 ∈ extra2048) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  by_cases hsmall : q < 2048
  · have heq : q%2048 = q := Nat.mod_eq_of_lt hsmall
    exact small_cut q (heq ▸ hq)
  · exact large_cut q (q%2048) rfl (by omega) hq

#print axioms twenty_nine_cylinders_unreachable
end BB429Branch29Extra2048
