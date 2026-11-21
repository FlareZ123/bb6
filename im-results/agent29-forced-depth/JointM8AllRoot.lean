/-!
Intermediate integration draft; not yet locally compiled or accepted by source CI.

This module strengthens Agent19Joint.highAllowed with the all-depth
source-normalized M8 parity obstruction from M8FilteredResidual.lean.
It deliberately preserves the infinite existential: it is a tighter
necessary parameterization, not a decision of BB(6).
-/

import JointAllRoot
import M8SharpFamily
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth

private theorem m8ScoreNonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm : 3*m+5 ≤ 3*2^(2*m+2) := by
    induction m with
    | zero => decide
    | succ m ih =>
        have hpos : 0 < (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
        have he : 2*(m+1)+2 = (2*m+2)+2 := by omega
        rw [he,Nat.pow_add]
        have hf : (2:Nat)^2=4 := by decide
        rw [hf]
        have hip : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
        have hij : j ≤ 2^(2*m+2)*j := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hip
        have hi := ih hip hij
        omega
  rw [Nat.mul_add]
  omega

/-- The M8 condition is only relevant on the exact deep second-family
    parity sector; all other high parameters pass this extra clause. -/
def deepM8Condition (j m : Nat) : Prop :=
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  (((BB6.Agent15.affineNormalize (2*j+3) k).2+2)/3)%8=2 ∧
    2*BB6.Agent15.oddDepth k%4=(m+1)%4

/-- Agent19's existing high parameter sieve, strengthened by the
    source-normalized M8 quotient exclusion. -/
def highAllowedM8 (j m : Nat) : Prop :=
  BB6.Agent19Joint.highAllowed j m ∧
    (¬(j%2=0 ∧ m%2=1 ∧ (j+m)%4=3) ∨ ¬deepM8Condition j m)

/-- The explicit dyadic sharp family is rejected by the new M8 clause,
    independently of the older parameter-only high restrictions. -/
theorem m8SharpFamily_not_highAllowedM8 (r : Nat) (hr : 2≤r) :
    ¬ highAllowedM8 (BB6.Agent29Depth.m8SharpJ r)
      (BB6.Agent29Depth.m8SharpM r) := by
  rcases BB6.Agent29Depth.m8SharpFamily_data r hr with
    ⟨hstop,hj,hm,hs,hfirst,hsecond⟩
  have hk :
      BB6.Agent29Depth.m8SharpK r =
        2^(2*BB6.Agent29Depth.m8SharpM r+2)*
          (BB6.Agent29Depth.m8SharpJ r+3)-
          (BB6.Agent29Depth.m8SharpJ r+
            3*BB6.Agent29Depth.m8SharpM r+5) := by
    omega
  have hcond :
      deepM8Condition (BB6.Agent29Depth.m8SharpJ r)
        (BB6.Agent29Depth.m8SharpM r) := by
    dsimp [deepM8Condition]
    rw [← hk]
    exact ⟨hfirst,hsecond⟩
  intro hallowed
  rcases hallowed.2 with hnotDeep | hnotM8
  · exact hnotDeep ⟨hj,hm,hs⟩
  · exact hnotM8 hcond

private theorem deepM8Clause_of_root (j m : Nat)
    (hroot : BB6.Agent3.mixedFastRootDecision (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))=true) :
    (¬(j%2=0 ∧ m%2=1 ∧ (j+m)%4=3)) ∨
      ¬deepM8Condition j m := by
  by_cases hdeep : j%2=0 ∧ m%2=1 ∧ (j+m)%4=3
  · rcases hdeep with ⟨hj,hm,hs⟩
    let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
    have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
      dsimp [k]
      have hc := Nat.sub_add_cancel (m8ScoreNonnegative j m)
      omega
    obtain ⟨time,hr⟩ :=
      (BB6.Agent3.mixedFastRootDecision_iff (2*j+3) k).mp hroot
    have hroot15 : BB6.Agent15.CReach (2*j+3) k := by
      simpa [BB6.Agent3.CReach, BB6.Agent15.CReach] using
        (show BB6.Agent3.CReach (2*j+3) k from ⟨time,hr⟩)
    have hnot := BB6.Agent29Depth.second_deep_root_m8_parity_exclusion
      j m k hstop hj hm hs hroot15
    right
    simpa [deepM8Condition,k] using hnot
  · exact Or.inl hdeep

/-- A source-linked strengthening of the joint parametric stopping
    criterion. The remaining existential is still infinite and undecided. -/
theorem blank_halts_iff_combined_parametric_m8 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent3.jointLowAllowed m ∧
        BB6.Agent3.mixedFastRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedM8 j m ∧
        BB6.Agent3.mixedFastRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent19Joint.blank_halts_iff_combined_parametric]
  constructor
  · rintro (hlow | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,⟨hallowed,deepM8Clause_of_root j m hroot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hallowed,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

#print axioms m8SharpFamily_not_highAllowedM8
#print axioms blank_halts_iff_combined_parametric_m8
end BB6.Agent29Depth
