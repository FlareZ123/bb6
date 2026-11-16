import U5Q0OddOddFan
import CRange
import Lean.Elab.Tactic.Omega

/-!
A source-level filter on the complete q-fan of original-section parents
of X_t=(44*t-1,42*t-1).

For a fan member, write U=2*V.  The exact equations imply
  k + V + 3*q = 64*t - 4,
  (U-2)+k = V + 64*t - 6 - 3*q.
If V+q is 3 modulo 4, then k is odd and at least 5, while
(U-2)+k is 1 modulo 4.  This contradicts the original-source
CLine invariant BB6.CRange.reached_odd_zero_mod4_hole.

This excludes a whole parameterized quarter of the exact parent fan.
It does not close the remaining fan or the U5 blank-root problem.
-/

namespace BB6.Agent3U5CLineFilter

open BB6.Agent46

private theorem four_mul_le_pow_four (q : Nat) (hq : 1 ≤ q) :
    4*q ≤ 4^q := by
  cases q with
  | zero => omega
  | succ q =>
    induction q with
    | zero => norm_num
    | succ q ih =>
      have hstep : 4*(q+2) ≤ (4*(q+1))*4 := by omega
      have hmul := Nat.mul_le_mul_right 4 ih
      have hpow : (4:Nat)^(q+2) = 4^(q+1)*4 := by
        rw [Nat.pow_succ]
      rw [hpow]
      exact le_trans hstep hmul

/-- An exact q-fan parent with V+q=3 (mod 4) is outside the
    authentic blank-start CLine orbit.  The bound k≥5 is derived
    from the exact fan equations, not assumed as an extra hypothesis. -/
theorem qfan_parent_not_reach_vq3
    (t q U k : Nat)
    (ht : 1 ≤ t)
    (hUge : 4 ≤ U)
    (hUeven : U % 2 = 0)
    (hpow : 43*t-1 = 4^q*U)
    (hcost : 2*k+U+6*q = 128*t-8)
    (hvq : (U/2+q)%4=3) :
    ¬ BB6CLine.Reach (U-2,k,0) := by
  let V := U/2
  have hUeq : U=2*V := by
    dsimp [V]
    omega
  have hpowpos : 0 < 4^q := Nat.pow_pos (by decide)
  have hpowge : 1 ≤ 4^q := by omega
  have hUle : U ≤ 43*t-1 := by
    calc
      U = 1*U := by omega
      _ ≤ 4^q*U := Nat.mul_le_mul_right U hpowge
      _ = 43*t-1 := hpow.symm
  have h4pow : 4^q*4 ≤ 43*t-1 := by
    calc
      4^q*4 ≤ 4^q*U := Nat.mul_le_mul_left (4^q) hUge
      _ = 43*t-1 := hpow.symm
  have h4q : 4*q ≤ 4^q := by
    cases q with
    | zero => norm_num
    | succ q => exact four_mul_le_pow_four (q+1) (by omega)
  have hmul := Nat.mul_le_mul_right 4 h4q
  have h16q : 16*q ≤ 43*t-1 := by
    calc
      16*q = (4*q)*4 := by omega
      _ ≤ 4^q*4 := hmul
      _ ≤ 43*t-1 := h4pow
  have hqbound : q ≤ 3*t := by omega
  have hcost' : 2*k+2*V+6*q=128*t-8 := by
    simpa [hUeq] using hcost
  have h2k : 67*t-7 ≤ 2*k := by omega
  have hkge : 5 ≤ k := by omega
  have hcostV : k+V+3*q=64*t-4 := by omega
  have hvq' : (V+q)%4=3 := by
    simpa [V] using hvq
  have hvqOdd : (V+q)%2=1 := by omega
  have hsumEven : (k+V+3*q)%2=0 := by
    rw [hcostV]
    omega
  have hodd : k%2=1 := by omega
  have hsumEq : U-2+k=V+64*t-6-3*q := by omega
  have hsum : ((U-2)+k)%4=1 := by
    rw [hsumEq]
    omega
  intro hreach
  have hhole := BB6.CRange.reached_odd_zero_mod4_hole
    (U-2) k hreach hkge hodd
  rcases hhole with h0 | h3 <;> omega

/-- If an original-section predecessor of X_t is genuinely reached
    by the blank-start CLine orbit, its exact fan parameters must
    avoid the excluded V+q=3 (mod 4) class. -/
theorem reachable_q0_parent_filter
    (t a k : Nat)
    (ht : 1 ≤ t)
    (hsec : secNext (a,k)=some (44*t-1,42*t-1))
    (hreach : BB6CLine.Reach (a,k,0)) :
    ∃ q U,
      43*t-1=4^q*U ∧
      4≤U ∧ U%2=0 ∧
      a=U-2 ∧ 0<k ∧ a<2*k ∧
      2*k+U+6*q=128*t-8 ∧
      (U/2+q)%4≠3 := by
  obtain ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩ :=
    BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan t a k ht hsec
  refine ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost,?_⟩
  intro hvq
  have hreach' : BB6CLine.Reach (U-2,k,0) := by
    simpa [ha] using hreach
  exact qfan_parent_not_reach_vq3 t q U k ht hUge hUeven
    hpow hcost hvq hreach'

#print axioms qfan_parent_not_reach_vq3
#print axioms reachable_q0_parent_filter

end BB6.Agent3U5CLineFilter
