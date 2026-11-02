import EvenSeed
import ResetGate
namespace BB6.Agent1

/-- Every reached even-left, right-two state requires an earlier reset that
    misses a formal halting-critical counter by precisely two. -/
theorem even_two_has_near_critical_reset (b : Nat)
    (hr : Reach b 2) (hb : b%2=0) :
    ∃ j s : Nat, Reach 2 s ∧ b+12=14*2^j ∧ s+2*j=b := by
  obtain ⟨j,s,hs,he,hnum⟩ :=
    even_hub_reset_seed b 2 hr hb (by decide) (by decide)
  exact ⟨j,s,hs,he,by omega⟩

private theorem linear_lt_seven_pow (j : Nat) : 2*j+4 < 7*2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

private theorem no_between_powers (j t x : Nat) (hj : 1≤j)
    (hlo : 14*2^(j-1) < x) (hhi : x < 14*2^j) :
    x ≠ 14*2^t := by
  intro hx
  by_cases ht : t<j
  · have horder : t ≤ j-1 := by omega
    have hpow := Nat.pow_le_pow_right (show (2:Nat)>0 by decide) horder
    omega
  · have horder : j≤t := by omega
    have hpow := Nat.pow_le_pow_right (show (2:Nat)>0 by decide) horder
    omega

/-- For a reached positive even-right two-cell hub, any exponent ≥2 is odd.
    The even exponents produce a reset counter divisible by four in a strict
    gap between consecutive 14-times-powers-of-two. -/
theorem even_two_exponent_not_positive_even (b j s : Nat)
    (hs : Reach 2 s) (hpow : b+12=14*2^j)
    (hmass : s+2*j=b) (hj : 2≤j) (heven : j%2=0) : False := by
  have hjpow : 4≤2^j := by
    have hp := Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hj
    simpa using hp
  have hsmall : 2*j+4 < 7*2^j := linear_lt_seven_pow j
  have hs12 : 12≤s := by omega
  have hp4 : 2^j = 4*2^(j-2) := by
    have hj2 : j=(j-2)+2 := by omega
    calc
      2^j = 2^((j-2)+2) := by congr 1
      _ = 4*2^(j-2) := by rw [Nat.pow_add]; simp only [Nat.reducePow]; omega
  have hsmod : s%4=0 := by
    rw [hp4] at hpow
    omega
  obtain ⟨t,he⟩ := reset_four_power s hs hs12 hsmod
  have hhi : s+8 < 14*2^j := by omega
  have hlo : 14*2^(j-1) < s+8 := by
    have hpowrel : 2^j=2*2^(j-1) := by
      have hj1 : j=(j-1)+1 := by omega
      calc
        2^j = 2^((j-1)+1) := by congr 1
        _ = 2*2^(j-1) := by rw [Nat.pow_succ]; omega
    omega
  exact (no_between_powers j t (s+8) (by omega) hlo hhi) he

/-- The exact accelerator cannot reach the zero-right state (1,0). -/
theorem blank_no_one_zero : ¬Reach 1 0 := by
  intro hr
  cases hr with
  | next a c _ _ hpre ht =>
    rcases T_to_odd_zero a c 1 ht (by decide) with h | h <;> omega

/-- The exceptional 0-th even-left two-cell hub is absent. -/
theorem blank_no_two_two : ¬Reach 2 2 := by
  intro hr
  cases hr with
  | next a c _ _ hpre ht =>
    obtain ⟨hc,hd⟩ := T_to_two_positive a c 2 ht (by decide)
    have ha : a=1 := by omega
    subst a
    subst c
    exact blank_no_one_zero hpre

/-- A genuine blank-reachable even-left, right-two hub has only an odd
    exponential index. This is a uniform all-time exclusion for every
    even exponent, conditional only on the exact published accelerator. -/
theorem reachable_even_two_odd_exponent (b : Nat)
    (hr : Reach b 2) (hb : b%2=0) :
    ∃ j : Nat, b+12=14*2^j ∧ j%2=1 := by
  obtain ⟨j,s,hs,hpow,hmass⟩ := even_two_has_near_critical_reset b hr hb
  have hjpositive : 0<j := by
    by_cases hjzero : j=0
    · subst j
      have hb2 : b=2 := by
        simp at hpow
        omega
      have hbase : Reach 2 2 := by simpa only [hb2] using hr
      exact False.elim (blank_no_two_two hbase)
    · omega
  have hjodd : j%2=1 := by
    by_cases hodd : j%2=1
    · exact hodd
    · have heven : j%2=0 := by omega
      have hj2 : 2≤j := by omega
      exact False.elim (even_two_exponent_not_positive_even b j s hs hpow hmass hj2 heven)
  exact ⟨j,hpow,hjodd⟩

#print axioms BB6.Agent1.reachable_even_two_odd_exponent
#print axioms BB6.Agent1.even_two_has_near_critical_reset
#print axioms BB6.Agent1.even_two_exponent_not_positive_even
end BB6.Agent1
