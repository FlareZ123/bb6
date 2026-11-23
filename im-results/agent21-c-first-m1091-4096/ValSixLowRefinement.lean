import ValSixJointFull
import Low1091Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent21Low1091

/-- Agent 3's exact low domain, strengthened by the two new original-source
    first-stop exclusions. The existing joint criterion is left unchanged. -/
def lowAllowedValSixRefined (m : Nat) : Prop :=
  BB6.Agent3ValSix.lowAllowedValSixFull m ∧
    (m%4096≠1091 ∧ m%16384≠12355)

private theorem low_bound_refined (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Exact Machine C blank-halting equivalence with the two new low
    first-stop cylinders removed. The remaining low and high parameter
    domains are still unbounded. -/
theorem blank_halts_iff_joint_val_six_refined :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedValSixRefined m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent3ValSix.highAllowedValSixFull j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent3ValSix.blank_halts_iff_joint_val_six_full]
  constructor
  · rintro (⟨m,hlow,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mp hroot
      have hr' : BB6.Agent21Low1091.CReach 1 k := by
        simpa [BB6.Agent3.CReach, BB6.Agent21Low1091.CReach] using hr
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hc := Nat.sub_add_cancel (low_bound_refined m)
        omega
      have hnon1091 : m%4096≠1091 := by
        intro hm
        rcases hr' with ⟨time,hrun⟩
        exact (first_stop_m1091_mod4096 time m k hm hstop) hrun
      have hnon12355 : m%16384≠12355 := by
        intro hm
        rcases hr' with ⟨time,hrun⟩
        exact (first_stop_m12355_mod16384 time m k hm hstop) hrun
      exact Or.inl ⟨m,⟨hlow,⟨hnon1091,hnon12355⟩⟩,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩
  · rintro (⟨m,⟨hlow,_⟩,hroot⟩ | ⟨j,m,hhigh,hroot⟩)
    · exact Or.inl ⟨m,hlow,hroot⟩
    · exact Or.inr ⟨j,m,hhigh,hroot⟩

#print axioms blank_halts_iff_joint_val_six_refined

end BB6.Agent21Low1091
