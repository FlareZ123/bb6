import Agent8LogRightSource

/-!
Source-true Cryptids #623 third-counter B-drain upper bound sublinear
above the sharp 3b lower envelope. For every successful complete drain
B(a,b,d)=D(A,D), if b<3^n, then D <= d+3b+n(n+5), independent of a,d.

This all-input quadratic-in-ternary-length bound is asymptotically
stronger than the previous 7b upper bound and has no blank-root verdict.
-/

namespace BB6.Agent8DrainQuadraticLogSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- The source evaluator incurs at most two units of third-potential
overhead per base-three digit of its input index. -/
theorem evalA_upper_log (n : Nat) :
    ∀ a k m aa bb dd : Nat, k<3^n →
    evalA a k m = some (aa,bb,dd) → dd+3*bb ≤ m+k+2*(n+1) := by
  induction n with
  | zero =>
    intro a k m aa bb dd hk hs
    have hk0 : k=0 := by simpa using hk
    subst k
    rw [evalA] at hs
    by_cases ha : a=0
    · simp [ha] at hs
    · simp [ha] at hs
      cases hs
      omega
  | succ n ih =>
    intro a k m aa bb dd hk hs
    rw [evalA] at hs
    by_cases h2 : k%3=2
    · simp [h2] at hs
      cases hs
      omega
    · by_cases ha : a=0
      · by_cases h0 : k%3=0
        · simp [h2,ha,h0] at hs
        · simp [h2,ha,h0] at hs
          cases hs
          omega
      · by_cases h0 : k%3=0
        · simp [h2,ha,h0] at hs
          cases hs
          omega
        · simp [h2,ha,h0] at hs
          have hpow : 3^(n+1) = 3*3^n := by rw [Nat.pow_succ]; omega
          have hq : k/3<3^n := by omega
          have hr := ih (a-1) (k/3) (m+2*(k/3)+3) aa bb dd hq hs
          omega

/-- The excess over the sharp 3b lower bound is O((log_3 b)^2)
uniformly for all successful original-source B-drains. -/
theorem drainB_upper_quadratic_log (n : Nat) :
    ∀ a b d aa dd : Nat, b<3^n →
    drainB a b d = some (.D aa dd) → dd ≤ d+3*b+n*(n+5) := by
  induction n with
  | zero =>
    intro a b d aa dd hb hs
    have hb0 : b=0 := by simpa using hb
    subst b
    simp [drainB] at hs
    cases hs
    omega
  | succ n ih =>
    intro a b d aa dd hb hs
    by_cases hb0 : b=0
    · subst b
      simp [drainB] at hs
      cases hs
      omega
    · rw [drainB] at hs
      simp only [if_neg hb0] at hs
      cases hev : evalA a (b-1) (d+2*b+3) with
      | none => simp [hev] at hs
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [hev,Option.bind_some] at hs
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at hs
          have hevbound := evalA_upper_log (n+1) a (b-1) (d+2*b+3)
            a1 b1 d1 (by omega) hev
          have hquot := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
            a (b-1) (d+2*b+3) a1 b1 d1 hev
          have hpow : 3^(n+1) = 3*3^n := by rw [Nat.pow_succ]; omega
          have hb1 : b1<3^n := by omega
          have hr := ih a1 b1 d1 aa dd hb1 hs
          have hid : n*(n+5)+2*n+6 = (n+1)*(n+6) := by
            simp only [Nat.mul_add, Nat.add_mul]
            omega
          have hident : (n+1)*(n+1+5) = (n+1)*(n+6) := by
            congr 1 <;> omega
          omega
        · simp only [if_neg hlt] at hs
          contradiction

#print axioms evalA_upper_log
#print axioms drainB_upper_quadratic_log
end BB6.Agent8DrainQuadraticLogSource
