import BounceHaltingInputs
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem haltLevel_char (k c : Nat) :
    (∃ n : Nat, c=haltLevel k n) ↔
      (c=5 ∨ (2*k+8<c ∧ ∃ n : Nat, c-(2*k+5)=haltLevel (2*k+4) n)) := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
        left
        simpa [haltLevel] using hn
    | succ n =>
        right
        have hmin := haltLevel_ge_five (2*k+4) n
        refine ⟨by rw [hn]; simp only [haltLevel]; omega, ⟨n,?_⟩⟩
        rw [hn]
        simp only [haltLevel]
        omega
  · rintro (hfive | ⟨hlarge,n,hn⟩)
    · exact ⟨0,by simpa [haltLevel] using hfive⟩
    · refine ⟨n+1,?_⟩
      simp only [haltLevel]
      omega

/-- Complete exact halting criterion for high-zero-left even-middle inputs. -/
theorem even_bounce_none_iff_level (c : Nat) : ∀ k, k%2=0 → 4≤c →
    ((bounce k c).2=none ↔ ∃ n : Nat, c=haltLevel k n) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k hk hc
    rw [bounce.eq_1]
    have hnot : ¬c<4 := by omega
    have hodd : ¬k%2=1 := by omega
    simp only [hnot,ite_false,hodd]
    by_cases hc4 : c=4
    · simp only [hc4,ite_true]
      rw [haltLevel_char]
      simp only [Option.some_ne_none, false_iff]
      omega
    · simp only [hc4,ite_false]
      by_cases hc5 : c=5
      · simp only [hc5,ite_true]
        rw [haltLevel_char]
        simp
      · simp only [hc5,ite_false]
        by_cases hs : c≤2*k+8
        · simp only [hs,ite_true]
          rw [haltLevel_char]
          simp only [Option.some_ne_none,false_iff]
          omega
        · simp only [hs,ite_false]
          have hlarge : 2*k+8<c := by omega
          have hcsmall : 4≤c-(2*k+5) := by omega
          have hlt : c-(2*k+5)<c := Nat.sub_lt (by omega) (by omega)
          have hknew : (2*k+4)%2=0 := by omega
          have hrec := ih (c-(2*k+5)) hlt (2*k+4) hknew hcsmall
          rw [haltLevel_char]
          simp only [hc5,false_or, hlarge, true_and]
          exact hrec

#print axioms haltLevel_char
#print axioms even_bounce_none_iff_level
end BB6.Agent46
