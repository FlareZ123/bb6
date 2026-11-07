import Agent8DrainLogDepthSource
import Agent8BudgetSource
import Agent49ParitySource

/-!
A source-authentic logarithmic first-counter bound and two diagonal-gate
repulsion theorems for Cryptids BB6 #623.

These results quantify universally over synthetic accelerated states, not
over the genuine blank-origin orbit. In particular they make no halt/nonhalt
claim for #623 or BB(6).
-/

namespace BB6.Agent8GateRepulsionSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- An evaluator call increases its first counter by at most one. -/
theorem evalA_first_le_succ (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → aa ≤ a+1 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- The complete B-drain's first output rises by at most the ternary
digit-length budget k when its input block index b is below 3^k. -/
theorem drainB_first_le_pow (k : Nat) :
    ∀ a b d aa dd : Nat, b < 3^k → drainB a b d = some (.D aa dd) →
      aa ≤ a+k := by
  induction k with
  | zero =>
    intro a b d aa dd hb hs
    have hb0 : b=0 := by simpa using hb
    subst b
    simp [drainB] at hs
    cases hs
    omega
  | succ k ih =>
    intro a b d aa dd hb hs
    by_cases hb0 : b=0
    · subst b
      simp [drainB] at hs
      cases hs
      omega
    · rw [drainB] at hs
      simp only [if_neg hb0] at hs
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at hs
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at hs
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at hs
          have hf := evalA_first_le_succ a (b-1) (d+2*b+3) a1 b1 d1 he
          have hq := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
            a (b-1) (d+2*b+3) a1 b1 d1 he
          have hp : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
          have hb1 : b1<3^k := by omega
          have hr := ih a1 b1 d1 aa dd hb1 hs
          omega
        · simp [hlt] at hs

/-- A successful evaluator cannot decrease the third counter. -/
theorem evalA_third_ge (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → m ≤ dd := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hr := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- Even second-counter near-diagonal input: any successful return has
a second output counter at least twice the first, plus eight. -/
theorem even_diagonal_repulsion (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d)
    (hpow : a < 3^k) (hroom : 2*d+2*k+7 ≤ 4*a)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    2*aa+8 ≤ dd := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  have h5 : d%2 ≠ 1 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4, if_neg h5] at hstep
  cases hev : evalA (d+1-a) a (2*a+5) with
  | none => simp [hev] at hstep
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [hev,Option.bind_some] at hstep
    have hfirst := evalA_first_le_succ (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hsecond := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
      (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hthird := evalA_third_ge (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hb : b1 < 3^k := by omega
    have hf := drainB_first_le_pow k a1 b1 d1 aa dd hb hstep
    have ht := BB6.Agent8BudgetSource.drainB_d3 b1 a1 d1 aa dd hstep
    omega

/-- Odd second-counter near-diagonal input: the same exit conclusion. -/
theorem odd_diagonal_repulsion (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d)
    (hpow : a-1 < 3^k) (hroom : 2*d+2*k+16 ≤ 5*a)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    2*aa+8 ≤ dd := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  have h4 : a ≠ d+2 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
    if_pos hd] at hstep
  have hf := drainB_first_le_pow k (d+4-a) (a-1) 3 aa dd hpow hstep
  have ht := BB6.Agent8BudgetSource.drainB_d3 (a-1) (d+4-a) 3 aa dd hstep
  omega


/-- Any even-first-counter state with a sufficiently dominant second
counter returns at least one more time. -/
theorem right_dominated_safe (a d : Nat)
    (he : a%2=0) (hr : 2*a+8 ≤ d) :
    ∃aa dd, highLevelNext (.D a d) = some (.D aa dd) := by
  by_cases hzero : a=0
  · subst a
    by_cases hodd : d%2=1
    · have hones := BB6.Agent49ParitySource.ternaryOnes_ge (d+1)
      have hb : 2 ≤ BB6.Agent49ParitySource.ternaryOnes (d+1) := by omega
      obtain ⟨aa,dd,hs⟩ := BB6.Agent49ParitySource.drainB_safe_ones
        2 (d+1) 2 hb
      exact ⟨aa,dd,by simpa [highLevelNext,hodd] using hs⟩
    · exact ⟨d,7,by simp [highLevelNext,hodd]⟩
  · have ha : 0<a := by omega
    have hc : a+a/3+1 ≤ d := by omega
    exact BB6.Agent49ParitySource.next_safe_left_third_two a d ha he hc

/-- A successful even-second-counter near-diagonal return has a
guaranteed immediately following successful return. -/
theorem even_diagonal_two_step (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hside : a≤d)
    (hpow : a<3^k) (hroom : 2*d+2*k+7≤4*a)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have hr := even_diagonal_repulsion a d k aa dd ha he hd hside hpow hroom hstep
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he hstep
  exact right_dominated_safe aa dd hp hr

/-- Odd-second-counter companion to the source two-step theorem. -/
theorem odd_diagonal_two_step (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hside : a≤d)
    (hpow : a-1<3^k) (hroom : 2*d+2*k+16≤5*a)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have hr := odd_diagonal_repulsion a d k aa dd ha he hd hside hpow hroom hstep
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he hstep
  exact right_dominated_safe aa dd hp hr

#print axioms right_dominated_safe
#print axioms even_diagonal_two_step
#print axioms odd_diagonal_two_step

#print axioms evalA_first_le_succ
#print axioms evalA_third_ge
#print axioms drainB_first_le_pow
#print axioms even_diagonal_repulsion
#print axioms odd_diagonal_repulsion
end BB6.Agent8GateRepulsionSource
