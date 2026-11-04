import Std

namespace BB6.Agent28

/-- Source-independent exact abstraction of the odd inverse-word recurrence.
    Every step has a strictly positive dyadic cost l. -/
inductive OddWord (K : Nat) : Nat → Nat → Nat → Nat → Prop where
  | base : OddWord K 1 0 0 0
  | next {D m A T D' l : Nat} (h : OddWord K D m A T)
      (hl : 1 ≤ l) (hstep : 2^l * D' + m = K + D) :
      OddWord K D' (m+l) (A + 2^m) (T + m*2^m)

/-- An arbitrary exact inverse word has a binary affine mass identity. -/
theorem OddWord.mass_identity {K D m A T : Nat} (h : OddWord K D m A T) :
    2^m*D + T = 1 + K*A := by
  induction h with
  | base => simp
  | @next D m A T D' l h hl hstep ih =>
      have hp : (2:Nat)^(m+l) = 2^m*2^l := Nat.pow_add 2 m l
      have step_eq := congrArg (fun z : Nat => 2^m*z) hstep
      have hbridge : (2^m)*(2^l*D') + m*2^m = 2^m*(K+D) := by
        calc
          (2^m)*(2^l*D') + m*2^m = (2^m)*(2^l*D'+m) := by rw [Nat.mul_add]; ac_rfl
          _ = 2^m*(K+D) := step_eq
      calc
        2^(m+l)*D' + (T + m*2^m)
          = (2^m)*(2^l*D') + m*2^m + T := by rw [hp]; ac_rfl
        _ = 2^m*(K+D) + T := congrArg (fun t : Nat => t+T) hbridge
        _ = 2^m*K+(2^m*D+T) := by simp only [Nat.mul_add]; ac_rfl
        _ = 1 + K*(A+2^m) := by rw [ih]; simp only [Nat.mul_add]; ac_rfl

/-- A is a proper binary subword of 2^m. -/
theorem OddWord.binary_coefficient_small {K D m A T : Nat} (h : OddWord K D m A T) :
    A < 2^m := by
  induction h with
  | base => decide
  | @next D m A T D' l h hl hstep ih =>
      have hl2 : (2:Nat) ≤ 2^l := by
        calc
          2 = (2:Nat)^1 := by decide
          _ ≤ 2^l := Nat.pow_le_pow_right (by decide) hl
      have hpow : 2^(m+l) = 2^m*2^l := Nat.pow_add 2 m l
      have hprod : (2^m)*2 ≤ (2^m)*2^l := Nat.mul_le_mul_left (2^m) hl2
      rw [hpow]
      omega

/-- No affine-wall word can have negligible cost compared with the root K. -/
theorem OddWord.wall_cost_necessary {K D m A T n : Nat}
    (h : OddWord K D m A T)
    (hwall : D + 3*m + 2*n + 4 = K) :
    K ≤ 1 + 2^m*(3*m+2*n+4) := by
  have hsmall := h.binary_coefficient_small
  have hmass := h.mass_identity
  have hAle : A+1 ≤ 2^m := by omega
  have hmul : K*(A+1) ≤ K*2^m := Nat.mul_le_mul_left K hAle
  have htarget : 2^m*K+T = 1+K*A+2^m*(3*m+2*n+4) := by
    calc
      2^m*K+T = 2^m*(D+3*m+2*n+4)+T := by rw [hwall]
      _ = (2^m*D+T)+2^m*(3*m+2*n+4) := by
        simp only [Nat.mul_add]; ac_rfl
      _ = 1+K*A+2^m*(3*m+2*n+4) := by rw [hmass]
  have hrewrite : K*(A+1) = K*A+K := by simp only [Nat.mul_add]; omega
  have hlemma : K*A+K ≤ 2^m*K := by
    rw [← hrewrite]
    simpa only [Nat.mul_comm K (2^m)] using hmul
  omega

private theorem power_beats_eight (k : Nat) (hk : 6 ≤ k) : 8*k ≤ 2^k := by
  have hb : ∀ t : Nat, 8*(t+6) ≤ 2^(t+6) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have hidx : (t+1)+6 = (t+6)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have heq : (k-6)+6 = k := by omega
  simpa only [heq] using hb (k-6)

private theorem power_beats_linear (n : Nat) (hn : 4 ≤ n) : n+4 ≤ 2^n := by
  have hb : ∀ t:Nat, (t+4)+4 ≤ 2^(t+4) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have hidx : (t+1)+4 = (t+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have heq : (n-4)+4 = n := by omega
  simpa only [heq] using hb (n-4)

/-- A weaker but immediate explicit corollary. -/
theorem OddWord.wall_needs_half_cost {n K D m A T : Nat}
    (hn : 14 ≤ n) (hK : K + n + 3 = 7*2^n)
    (h : OddWord K D m A T)
    (hwall : D+3*m+2*n+4 = K) : n ≤ 2*m := by
  by_cases hlow : n ≤ 2*m
  · exact hlow
  have hl : 2*m < n := by omega
  let k := n-m
  have hk : n = m+k := by dsimp [k]; omega
  have hkm : m < k := by omega
  have hk6 : 6 ≤ k := by omega
  have hpowk : 8*k ≤ 2^k := power_beats_eight k hk6
  have hkn : 4*n ≤ 2^k := by omega
  have hcoeff : 3*m+2*n+4 ≤ 4*n := by omega
  have hpower : 2^n = 2^m*2^k := by
    rw [hk]; exact Nat.pow_add 2 m k
  have hcost : 2^m*(3*m+2*n+4) ≤ 2^n := by
    calc
      _ ≤ 2^m*(4*n) := Nat.mul_le_mul_left (2^m) hcoeff
      _ ≤ 2^m*(2^k) := Nat.mul_le_mul_left (2^m) hkn
      _ = 2^n := hpower.symm
  have hw := h.wall_cost_necessary hwall
  have hlinear : n+4 ≤ 2^n := power_beats_linear n (by omega)
  have hpospow : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
  omega

/-- Stronger all-depth necessary condition: the distance n-m is only logarithmic. -/
theorem OddWord.wall_cost_logarithmic_gap {n K D m A T : Nat}
    (hn : 14 ≤ n) (hK : K+n+3 = 7*2^n)
    (h : OddWord K D m A T)
    (hwall : D+3*m+2*n+4 = K) : 2^(n-m) < n := by
  by_cases hm : n ≤ m
  · have hzero : n-m = 0 := by omega
    simp only [hzero]; simp
    omega
  · have hless : m < n := by omega
    let k := n-m
    have hnk : n = m+k := by dsimp [k]; omega
    have hP : 2^n = 2^m*2^k := by
      rw [hnk]; exact Nat.pow_add 2 m k
    have hlin : n+4 ≤ 2^n := power_beats_linear n (by omega)
    have hcoeff : 3*m+2*n+4 ≤ 5*n+1 := by omega
    have hc := h.wall_cost_necessary hwall
    have hbound : 7*2^n ≤ 2^n+2^m*(5*n+1) := by
      have hcoeffmul : 2^m*(3*m+2*n+4) ≤ 2^m*(5*n+1) :=
        Nat.mul_le_mul_left (2^m) hcoeff
      omega
    have hc6 : 6*2^n ≤ 2^m*(5*n+1) := by omega
    have hmult : 2^m*(6*2^k) ≤ 2^m*(5*n+1) := by
      calc
        _ = 6*2^n := by rw [hP]; ac_rfl
        _ ≤ _ := hc6
    have hpos : 0 < 2^m := Nat.pow_pos (by decide)
    have hkbound : 6*2^k ≤ 5*n+1 := Nat.le_of_mul_le_mul_left hmult hpos
    have hkn : 2^k < n := by omega
    simpa only [show n-m = k by rfl] using hkn

#print axioms BB6.Agent28.OddWord.mass_identity
#print axioms BB6.Agent28.OddWord.binary_coefficient_small
#print axioms BB6.Agent28.OddWord.wall_cost_necessary
#print axioms BB6.Agent28.OddWord.wall_needs_half_cost
#print axioms BB6.Agent28.OddWord.wall_cost_logarithmic_gap
end BB6.Agent28
