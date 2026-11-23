import LowM67HaltingCriterion
import LowM67D4Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13Low17Joint

/-- Exact same root decision, strengthened with a source-verified
    three-parent valuation-six low cylinder. The new forbidden condition
    is m=33347 modulo 262144 (equivalently m=512*z+67, z=65 mod512). -/
def lowAllowedSource17 (m : Nat) : Prop :=
  BB6.Agent13Low16Joint.lowAllowedSource16 m ∧
  m%262144≠33347

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Lossless original-source Machine C exact blank-halting equivalence
    excluding sixty-five classes modulo 512 of the m=67 mod512 low-stop
    ray: the previous 64/512 from the two-parent theorem plus one
    genuinely new valuation-six three-parent class z=65 mod512. -/
theorem blank_halts_iff_six_low17 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource17 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low16Joint.blank_halts_iff_six_low16]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon : m%262144≠33347 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%512=65 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13D4Low.low_stop_m67_z65_mod512_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low17
end BB6.Agent13Low17Joint
