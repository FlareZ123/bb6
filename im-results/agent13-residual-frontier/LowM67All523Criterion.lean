import LowM67SeventeenCriterion
import LowM67All523Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13Low523Joint

/-- Retain every previously certified Machine C low-stop restriction,
    and remove the two additional authentic source-inaccessible
    valuation-six progressions. -/
def lowAllowedSource523 (m : Nat) : Prop :=
  BB6.Agent13Low17Joint.lowAllowedSource17 m ∧
  m%1048576≠885315 ∧
  m%2097152≠1802819

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Lossless exact original Machine C blank-halting equivalence whose
    low side excludes 523/4096 of the m=512*z+67 subfamily by source-only
    proofs. The high-side existential is preserved unchanged, so this
    theorem does not decide Machine C halting. -/
theorem blank_halts_iff_six_low523 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource523 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low17Joint.blank_halts_iff_six_low17]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon1 : m%1048576≠885315 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%2048=1729 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13D4Second.low_stop_m67_z1729_mod2048_unreachable
          z m k hm hz hstop) hr
      have hnon2 : m%2097152≠1802819 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%4096=3521 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13D4Third.low_stop_m67_z3521_mod4096_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon1,hnon2⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low523
end BB6.Agent13Low523Joint
