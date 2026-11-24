import FullBoolean
import C70Integration
import ModularConeLowStop
import ModularConeHighStop
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000

namespace BB6.Agent42ModularCone

/-- Full Boolean/phase low predicate, the C70 low rectangle exclusion,
    and the independent modular inverse-cone filter. -/
def lowAllowedFullModular (m : Nat) : Prop :=
  BB6.Agent27FullBool.lowAllowedFullBool m = true ∧
  m%128 ≠ 18 ∧
  lowStopExcluded m = false

/-- Full Boolean/phase high predicate, both C70 high rectangles, and the
    independent modular inverse-cone filter on the unified index J=j+1. -/
def highAllowedFullModular (j m : Nat) : Prop :=
  BB6.Agent27FullBool.highAllowedFullBool j m = true ∧
  ¬((j%128=63 ∧ m%128=82) ∨ (j%128=127 ∧ m%128=18)) ∧
  highStopExcluded (j+1) m = false

private theorem low_stop_bound_full (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hmul : 2*(4*m+4) ≤ 2*2^(2*m+2) :=
    Nat.mul_le_mul_left 2 hp
  have hpow : 2*2^(2*m+2) = 2^(2*m+3) := by
    calc
      2*2^(2*m+2) = 2^(2*m+2)*2 := by omega
      _ = 2^(2*m+3) := by
        simpa [show 2*m+3=(2*m+2)+1 by omega] using
          (Nat.pow_succ 2 (2*m+2)).symm
  omega

private theorem high_stop_bound_full (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp0 : 0 < 2^(2*m+2) := Nat.pow_pos (by decide)
  have hp1 : 1 ≤ 2^(2*m+2) := by omega
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp1
  rw [Nat.mul_add]
  omega

/-- Exact original-source blank-halting equivalence with the full
    phase/Boolean predicate, C70 source rectangles, and both modular
    inverse-cone filters conjoined. The existential parameter ranges
    remain unbounded. -/
theorem blank_halts_iff_full_modular :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedFullModular m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedFullModular j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  constructor
  · intro hhalt
    have hcore := (BB6.Agent27FullBool.blank_halts_iff_full_booleans).mp hhalt
    rcases hcore with hlow | hhigh
    · rcases hlow with ⟨m,hfull,hroot⟩
      let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        have hbound := low_stop_bound_full m
        dsimp [k]
        omega
      have hC70 : m%128 ≠ 18 := by
        intro hm
        exact (BB6.Agent20C70.blank_no_low_depth_18_mod128 m k hm hstop) hr
      have hmod : lowStopExcluded m = false := by
        cases hc : lowStopExcluded m with
        | false => rfl
        | true =>
          have hstop' : k+3*m+4=P (2*m+2)*2 := by
            simpa [P, show 2*m+3=(2*m+2)+1 by omega, Nat.pow_succ] using hstop
          exact False.elim ((low_stop_excluded m k hstop' hc) hr)
      exact Or.inl ⟨m,⟨hfull,hC70,hmod⟩,hroot⟩
    · rcases hhigh with ⟨j,m,hfull,hroot⟩
      let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
      have hr : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
        have hbound := high_stop_bound_full j m
        dsimp [k]
        omega
      have hC70 :
          ¬((j%128=63 ∧ m%128=82) ∨ (j%128=127 ∧ m%128=18)) := by
        intro hres
        exact (BB6.Agent20C70.blank_no_high_63_82_or_127_18 j m k hres hstop) hr
      have hmod : highStopExcluded (j+1) m = false := by
        cases hc : highStopExcluded (j+1) m with
        | false => rfl
        | true =>
          have hstop' :
              k+(j+1)+3*m+4=2^(2*m+2)*((j+1)+2) := by
            calc
              k+(j+1)+3*m+4 = k+j+3*m+5 := by omega
              _ = 2^(2*m+2)*(j+3) := hstop
              _ = 2^(2*m+2)*((j+1)+2) := by congr 1 <;> omega
          exact False.elim
            ((high_stop_excluded (j+1) m k (by omega) hstop' hc) hr)
      exact Or.inr ⟨j,m,⟨hfull,hC70,hmod⟩,hroot⟩
  · intro h
    rcases h with ⟨m,hallow,hroot⟩ | ⟨j,m,hallow,hroot⟩
    · exact (BB6.Agent27FullBool.blank_halts_iff_full_booleans).mpr
        (Or.inl ⟨m,hallow.1,hroot⟩)
    · exact (BB6.Agent27FullBool.blank_halts_iff_full_booleans).mpr
        (Or.inr ⟨j,m,hallow.1,hroot⟩)

#print axioms blank_halts_iff_full_modular

end BB6.Agent42ModularCone
