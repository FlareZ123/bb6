import LowM67All1327Criterion
import LowM67Z44Source
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

/-!
# Source-authentic Machine C low-stop lossless criterion: 1519/4096

Combines the prior exact 1327/4096 low-stop source filter with
z ≡ 24 mod32 (Agent 8, 128/4096 cells) and the new z ≡ 44 mod64
(Agent 13, 64/4096 cells). All cylinders are disjoint. The entire
high-stop existential and every remaining low-depth root test survive
unchanged. This is not a halt/nonhalt decision.
-/

namespace BB6.Agent13Low1519

def lowAllowedSource1519 (m : Nat) : Prop :=
  BB6.Agent8CLow1327.lowAllowedSource1327 m ∧
  m%16384≠12355 ∧ m%32768≠22595

private theorem low_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3=(2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Exact original-source Machine C blank-halting equivalence after
    proving TWO further infinite parameter families impossible. This
    does not bound the residual low or high stop parameter domains. -/
theorem blank_halts_iff_six_low1519 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedSource1519 m ∧
        BB6.Agent11SixForced.sixForcedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, BB6.Agent11SixAll.highAllowed j m ∧
        BB6.Agent11SixForced.sixForcedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent8CLow1327.blank_halts_iff_six_low1327]
  constructor
  · rintro (⟨m,hprior,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · let k := 2^(2*m+3)-(3*m+4)
      have hr : BB6.Agent3.CReach 1 k :=
        (BB6.Agent11SixForced.sixForcedRootDecision_iff 1 k).mp hroot
      have hstop : k+3*m+4=2^(2*m+3) := by
        dsimp [k]
        have hb := Nat.sub_add_cancel (low_power_bound m)
        omega
      have hnon24 : m%16384≠12355 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%32=24 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent8CLowZ24.low_stop_m67_z24_mod32_unreachable
          z m k hm hz hstop) hr
      have hnon44 : m%32768≠22595 := by
        intro hm0
        let z := m/512
        have hm : m=512*z+67 := by
          have hh := Nat.mod_add_div m 512
          dsimp [z]
          omega
        have hz : z%64=44 := by
          rw [hm] at hm0
          omega
        exact (BB6.Agent13LowZ44.low_stop_m67_z44_mod64_unreachable
          z m k hm hz hstop) hr
      exact Or.inl ⟨m,⟨hprior,hnon24,hnon44⟩,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩
  · rintro (⟨m,⟨hprior,_,_⟩,hroot⟩ | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl ⟨m,hprior,hroot⟩
    · exact Or.inr ⟨j,m,hprior,hroot⟩

#print axioms blank_halts_iff_six_low1519
end BB6.Agent13Low1519
