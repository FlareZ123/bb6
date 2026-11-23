import LowM67All1519Criterion
import LowM67Z16Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

/-!
Source-exact Machine C low-stop criterion after a further disjoint all-time
root exclusion z≡16 mod128 inside m=512z+67. This upgrades the previous
1519 formal excluded z-residues per 4096 to 1551; the high family and every
remaining unbounded low existential are exactly unchanged. These are
arithmetic low-gateway residue counts, NOT machine/halting percentages.
-/

namespace BB6.Agent13Low1551

def lowAllowedSource1551 (m : Nat) : Prop :=
  BB6.Agent13Low1519.lowAllowedSource1519 m ∧
  m%65536≠8259

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Lossless original-source halting criterion excluding the additional
    z=16 mod128 infinite low-stop progression. Neither Machine C nor
    BB(6) is decided: both remaining existential branches are unbounded. -/
theorem blank_halts_iff_six_low1551 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource1551 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent13Low1519.blank_halts_iff_six_low1519]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon16 : m%65536≠8259 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%128=16 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13LowZ16.low_stop_m67_z16_mod128_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon16⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low1551
end BB6.Agent13Low1551
