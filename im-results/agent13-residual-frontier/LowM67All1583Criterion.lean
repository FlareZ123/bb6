import LowM67All1551Criterion
import EvenOddLowStopSecondFanReach
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

/-!
# Lossless Machine C low-stop criterion: 1583 / 4096 excluded z-residues

This adds the disjoint source-authentic cylinder z = 14 (mod 128) to the
previous 1551 / 4096 exclusions.  The new exclusion is proved by the
second-generation high-parent fan, odd/odd low-valuation inverse, and
six-residue even-right inverse, all rooted in the unchanged original
blank section transition relation.

The high-stop family and all remaining low cases stay existential and
unbounded.  This is not a Machine C halting verdict or a BB(6) result.
-/

namespace BB6.Agent13Low1583

def lowAllowedSource1583 (m : Nat) : Prop :=
  BB6.Agent13Low1551.lowAllowedSource1551 m ∧
  m%65536≠7235

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Lossless original-source halting criterion after adding the complete
    z=14 (mod 128) low-stop exclusion. The high-stop branch and all other
    low-stop witnesses are preserved exactly. -/
theorem blank_halts_iff_six_low1583 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource1583 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low1551.blank_halts_iff_six_low1551]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon14 : m%65536≠7235 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%128=14 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13LowSecondFan.low_stop_m67_z14_mod128_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon14⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low1583
end BB6.Agent13Low1583
