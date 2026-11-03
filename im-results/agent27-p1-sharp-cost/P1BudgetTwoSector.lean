import P1BudgetOffsetPure
import InverseIff
import OddConeMass
import PosEvenForm

namespace BB6.Agent27Budget
open BB6.Agent47P1
open BB6.Agent1Quarter

/-- Source-identical arithmetic expression to Agent45TwoRoot.u2. -/
def u27 (q : Nat) : Nat := 7*2^(16*q)-4*q-3

private theorem u27_balance (q : Nat) (hq : 1≤q) :
    2 ≤ u27 q ∧ u27 q+4*q+3=7*2^(16*q) := by
  have hp := pow16_ge_linear_20 q hq
  dsimp [u27]
  omega

/-- Generic source-connected strengthening of the old m>=8P-or-wall
result for the two authentic P1 feeders n=16q+2: every non-wall
positive-even-right exit blank-reachable in the original P1 map requires
m>9P. OddCone uses exact source inverseAt edges, with no cutoff. -/
theorem authentic_two_feeder_nine_or_wall
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1≤q)
    (hcone : OddCone
      (if root then 4*u27 q-4 else 6*u27 q-2)
      (if root then 4*u27 q+9 else 2*u27 q+5) b d m)
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hce : c%2=0) (hk : 2≤k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    (t=1 ∧ b=4*m+64*q+(if root then 12 else 16)) ∨
      9*2^(16*q)<m := by
  have hu := u27_balance q hq
  have hpow4 : 2^(16*q+2)=4*2^(16*q) := by
    rw [Nat.pow_add]
    rw [show (2:Nat)^2=4 by decide]
    omega
  have hinit :
      (if root then 4*u27 q-4 else 6*u27 q-2) +
      (if root then 4*u27 q+9 else 2*u27 q+5) +
      2*(16*q+2)+13+2*(if root then 1 else 2) =
      14*2^(16*q+2) := by
    cases root with
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        omega
    | true =>
        simp
        omega
  have hm := odd_cone_mass _ _ b d m hcone
  have hroot : b+d+2*m+2*(16*q+2)+13+
      2*(if root then 1 else 2)=14*2^(16*q+2) := by omega
  obtain ⟨hpower,hlinear⟩ :=
    (inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi
  have hlinear_even : 2*k+c+2*t+1=b+d := by omega
  have he : (2*k-4)%2=0 := by omega
  have hp : 0<c+4 := by omega
  have hceven : (c+4)%2=0 := by omega
  obtain ⟨j,hj⟩ :=
    BB6.Agent1.even_left_power_shape (2*k-4) (c+4) hr he hp hceven
  have hpow : 2*k+8=14*2^j := by omega
  have h := sharp_even_exit_shifted (16*q+2) j t b d k c m
    (if root then 1 else 2) (by omega) hb hb4 hd hc hce
    hroot hpower hlinear_even hpow
  rcases h with ⟨ht,hj',hwall⟩|hcost
  · left
    constructor
    · exact ht
    · cases root with
      | false => simp only [Bool.false_eq_true, ite_false] at hwall ⊢; omega
      | true => simp at hwall ⊢; omega
  · right
    have hrle : (if root then 1 else 2) ≤ 2 := by cases root <;> decide
    exact shifted_two_sector_nine_barrier q m
      (if root then 1 else 2) hq hrle hcost

#print axioms authentic_two_feeder_nine_or_wall
end BB6.Agent27Budget
