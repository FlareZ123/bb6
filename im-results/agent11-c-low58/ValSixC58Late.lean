import ValSixC58AllDepthBool
import HighThreeLate
import HighThreeLatePrior
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58Late

/-- Previous all-depth certified high predicate, now excluding an
    independent congruence class whose dyadic valuation exceeds the
    original high stopping exponent. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58Boolean.highAllowed j m ∧
  ¬(m=3 ∧ j%512=372)

/-- Lossless authentic Machine C blank-halting equivalence after
    source-combining all previous sieves with the new late-cone family. -/
theorem blank_halts_iff_c58_all_depth_late :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58Boolean.blank_halts_iff_c58_all_depth_boolean]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hreach : BB6.Agent3.CReach (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5)) :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
      have hnew : ¬(m=3 ∧ j%512=372) := by
        rintro ⟨hm3,hjmod⟩
        have hj : j=372+512*(j/512) := by
          have h0 := Nat.mod_add_div j 512
          rw [hjmod] at h0
          omega
        let t := j/512
        have hx : 2*j+3=747+1024*t := by
          dsimp [t]
          rw [hj]
          omega
        have hk :
            2^(2*m+2)*(j+3)-(j+3*m+5)=95614+130560*t := by
          dsimp [t]
          rw [hm3,hj]
          omega
        rw [hx,hk] at hreach
        exact (BB6.Agent11HighThreeLate.late_high_372_family_no_blank t) hreach
      exact Or.inr ⟨j,m,⟨hprior,hnew⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

private theorem late_not_in_old_depth_gate (t r : Nat) :
    ¬BB6.Agent11GateDecision.gate r (372+512*t) 3 := by
  unfold BB6.Agent11GateDecision.gate
  intro h
  have hp : 4∣(2:Nat)^(r+4) := by
    simpa only [show (2:Nat)^2=4 by decide] using
      (Nat.pow_dvd_pow 2 (by omega : 2≤r+4))
  have hpr : 4∣3*(2:Nat)^(r+2) := by
    have hpp : 4∣(2:Nat)^(r+2) := by
      simpa only [show (2:Nat)^2=4 by decide] using
        (Nat.pow_dvd_pow 2 (by omega : 2≤r+2))
    rcases hpp with ⟨v,hv⟩
    refine ⟨3*v,?_⟩
    rw [hv]
    ac_rfl
  have hmod4 : ((372+512*t)+9*3+14)%4=0 := by
    calc
      ((372+512*t)+9*3+14)%4 =
          (((372+512*t)+9*3+14)%2^(r+4))%4 :=
        (Nat.mod_mod_of_dvd _ hp).symm
      _ = (3*2^(r+2))%4 := by rw [h.2.2.2.2]
      _ = 0 := Nat.mod_eq_zero_of_dvd hpr
  omega

/-- Every formerly admitted parameter in this entire infinite class
    passes both the old C58+ValSixFull filter and our NEW all-depth
    dyadic gate, yet fails the new late-depth-seven test. -/
theorem late_high_new_strict_family (t : Nat) :
    BB6.Agent11C58Boolean.highAllowed (372+512*t) 3 ∧
      ¬highAllowed (372+512*t) 3 := by
  have hprior : BB6.Agent11C58ValSix.highAllowed (372+512*t) 3 :=
    BB6.Agent11C58LatePrior.old_sieve_admits_late_high t
  have hboolOld : BB6.Agent11GateDecision.allowedBool (372+512*t) 3=true :=
    (BB6.Agent11GateDecision.allowedBool_iff _ _).mpr
      (by intro r; exact late_not_in_old_depth_gate t r)
  have hbool : BB6.Agent11FastDepthGate.candidateAllowedBool
      (372+512*t) 3=true := by
    rw [BB6.Agent11FastDepthGate.candidate_matches_scan]
    exact hboolOld
  refine ⟨⟨hprior,hbool⟩,?_⟩
  intro h
  exact h.2 ⟨by decide,by omega⟩

#print axioms blank_halts_iff_c58_all_depth_late
#print axioms late_high_new_strict_family
end BB6.Agent11C58Late
