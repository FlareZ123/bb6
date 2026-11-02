import BounceCalc
import EvenLadder
import Lean.Elab.Tactic.Omega

namespace BB6.Agent49
open BB6.Agent46 (bounce)

theorem KE_shift (k n : Nat) : KE (2*k+4) n = KE k (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [KE,ih]

theorem DE_shift (k n : Nat) :
    DE k (n+1) = 2*k+5+DE (2*k+4) n := by
  induction n with
  | zero => simp [DE,KE]
  | succ n ih =>
      change DE k (n+1)+2*KE k (n+1)+5 =
        2*k+5+(DE (2*k+4) n+2*KE (2*k+4) n+5)
      rw [ih, ← KE_shift]
      omega

theorem DE_next_ge (k n : Nat) : 2*k+5 ≤ DE k (n+1) := by
  rw [DE_shift]; omega

theorem bounce_even_none_iff (c : Nat) : ∀ k : Nat,
    k%2=0 → 4≤c →
    ((bounce k c).2 = none ↔ ∃ n : Nat, c=DE k n+5) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k he hc
    rw [bounce]
    have hnot : ¬c<4 := by omega
    have hodd : k%2 ≠ 1 := by omega
    simp only [hnot,ite_false,hodd]
    by_cases h4 : c=4
    · subst c
      simp only [ite_true,Option.some_ne_none]
      constructor
      · intro h
        cases h
      · intro h
        obtain ⟨n,hn⟩ := h
        cases n with
        | zero => simp [DE] at hn
        | succ n => have hge := DE_next_ge k n; omega
    · simp only [h4,ite_false]
      by_cases h5 : c=5
      · subst c
        simp only [ite_true]
        constructor
        · intro _
          exact ⟨0, by simp [DE]⟩
        · intro _
          trivial
      · simp only [h5,ite_false]
        by_cases hs : c≤2*k+8
        · simp only [hs,ite_true,Option.some_ne_none]
          constructor
          · intro h
            cases h
          · intro h
            obtain ⟨n,hn⟩ := h
            cases n with
            | zero => simp [DE] at hn; omega
            | succ n => have hge := DE_next_ge k n; omega
        · simp only [hs,ite_false]
          have hlarge : 2*k+8 < c := by omega
          have hsmall : c-(2*k+5)<c := by omega
          have hcsmall : 4≤c-(2*k+5) := by omega
          have he' : (2*k+4)%2=0 := by omega
          have hrec := ih (c-(2*k+5)) hsmall (2*k+4) he' hcsmall
          change (bounce (2*k+4) (c-(2*k+5))).2=none ↔ ∃ n, c=DE k n+5
          rw [hrec]
          constructor
          · rintro ⟨n,hn⟩
            refine ⟨n+1,?_⟩
            rw [DE_shift]
            clear ih hrec
            omega
          · rintro ⟨n,hn⟩
            cases n with
            | zero => simp [DE] at hn; omega
            | succ n =>
                refine ⟨n,?_⟩
                rw [DE_shift] at hn
                clear ih hrec
                omega

theorem bounce_odd_not_none (c : Nat) : ∀ k : Nat,
    k%2=1 → 4≤c → (bounce k c).2 ≠ none := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k hk hc
    rw [bounce]
    have hnot : ¬c<4 := by omega
    simp only [hnot,ite_false,hk,ite_true]
    by_cases hsmall : c≤2*k+6
    · simp only [hsmall,ite_true]
      exact Option.some_ne_none _
    · simp only [hsmall,ite_false]
      have hlarge : 2*k+6<c := by omega
      have hdec : c-(2*k+3)<c := by omega
      have hcdec : 4≤c-(2*k+3) := by omega
      have hk' : (2*k+3)%2=1 := by omega
      change (bounce (2*k+3) (c-(2*k+3))).2 ≠ none
      exact ih (c-(2*k+3)) hdec (2*k+3) hk' hcdec

theorem bounce_halting_criterion (k c : Nat) (hc : 4≤c) :
    ((bounce k c).2=none ↔ k%2=0 ∧ ∃ n : Nat, c=DE k n+5) := by
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · rw [bounce_even_none_iff c k he hc]
    simp [he]
  · have hn := bounce_odd_not_none c k ho hc
    simp [ho,hn]

theorem DE_closed (k n : Nat) :
    DE k n+2*k+3*n+8 = 2*((k+4)*2^n) := by
  have hd := DE_conservation k n
  have hk := KE_closed k n
  omega

theorem criterion_eq (k c n : Nat) :
    (c=DE k n+5) ↔ (c+2*k+3*n+3=(k+4)*2^(n+1)) := by
  have hd := DE_closed k n
  have hp : (k+4)*2^(n+1)=2*((k+4)*2^n) := by
    simp only [Nat.pow_succ]
    ac_rfl
  omega

theorem bounce_power_criterion (k c : Nat) (hc : 4≤c) :
    ((bounce k c).2=none ↔
      k%2=0 ∧ ∃ n : Nat, c+2*k+3*n+3=(k+4)*2^(n+1)) := by
  rw [bounce_halting_criterion k c hc]
  constructor
  · rintro ⟨he,n,hn⟩
    exact ⟨he,n,(criterion_eq k c n).mp hn⟩
  · rintro ⟨he,n,hn⟩
    exact ⟨he,n,(criterion_eq k c n).mpr hn⟩

#print axioms bounce_even_none_iff
#print axioms bounce_odd_not_none
#print axioms bounce_halting_criterion
#print axioms bounce_power_criterion
end BB6.Agent49
