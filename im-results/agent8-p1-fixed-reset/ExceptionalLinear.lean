import ExceptionalExp
namespace BB6.Agent8Exceptional
open BB6.Agent28

private theorem pow_four_big (t : Nat) (ht : 3 ≤ t) :
    4*(t+1) ≤ 2^(t+1) := by
  have h : ∀ r : Nat, 4*(r+4) ≤ (2:Nat)^(r+4) := by
    intro r
    induction r with
    | zero => decide
    | succ r ih =>
        have hp : (2:Nat)^((r+1)+4)=2*2^(r+4) := by
          rw [show (r+1)+4=(r+4)+1 by omega, Nat.pow_succ]
          omega
        omega
  have heq : (t-3)+4=t+1 := by omega
  simpa only [heq] using h (t-3)

private theorem n_lt_quarter_power (n : Nat) (hn : 14 ≤ n) :
    n < 2^(n/4+1) := by
  have hq : 3≤n/4 := by omega
  have hrem : n < 4*(n/4+1) := by omega
  exact Nat.lt_of_lt_of_le hrem (pow_four_big (n/4) hq)

/-- Every critical P1 odd word terminating at D=2 must incur a cost
at least 7/4 of the critical exponent. -/
theorem OddWord.exceptional_seven_fourths_cost
    (n K m A T : Nat) (hn : 14 ≤ n)
    (hK : K+n+3=7*2^n)
    (h : OddWord K 2 m A T) : 7*n ≤ 4*m := by
  have hm := OddWord.exceptional_needs_n_plus_four n K m A T hn hK h
  have hE := OddWord.exceptional_exponential_cost n K m A T hn hK h
  by_cases hgoal : 7*n ≤ 4*m
  · exact hgoal
  · have hsmall : 4*m < 7*n := by omega
    have hm2 : m < 2*n := by omega
    let q : Nat := 2*n-m
    let r : Nat := m+1-n
    have hq : q = 2*n-m := rfl
    have hqpos : 1 ≤ q := by dsimp [q]; omega
    let s : Nat := q-1
    have hqeq : q = s+1 := by dsimp [s]; omega
    have heq : n = r+s := by dsimp [r,s,q]; omega
    have hcoeff : n+m+3 ≤ 3*n := by omega
    have hpow : (2:Nat)^n=2^r*2^s := by rw [heq, Nat.pow_add]
    have hrpos : 0<(2:Nat)^r := Nat.pow_pos (by decide)
    have hmult : (2^r)*(6*2^s) ≤ (2^r)*(3*n) := by
      calc
        _ = 6*2^n := by rw [hpow]; ac_rfl
        _ ≤ (n+m+3)*2^(m+1-n) := hE
        _ ≤ 3*n*2^r := by
          dsimp [r]
          exact Nat.mul_le_mul_right _ hcoeff
        _ = _ := by ac_rfl
    have hcancel : 6*2^s ≤ 3*n := Nat.le_of_mul_le_mul_left hmult hrpos
    have htwo : 2*2^s≤n := by omega
    have hqpow : 2^q ≤ n := by
      rw [hqeq, Nat.pow_succ]
      simpa only [Nat.mul_comm] using htwo
    have hqbound : n/4+1≤q := by dsimp [q]; omega
    have hmono : 2^(n/4+1)≤(2:Nat)^q := Nat.pow_le_pow_right (by decide) hqbound
    have hbig := n_lt_quarter_power n hn
    omega

#print axioms BB6.Agent8Exceptional.OddWord.exceptional_seven_fourths_cost
end BB6.Agent8Exceptional
