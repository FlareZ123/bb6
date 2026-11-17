import U5Q0OddOddFan
import CRange
import CBack
import KZeroMod4
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


/-- In the V+q=0 class, a parent with k=4 (mod 8) is also
    outside the authentic blank-start CLine orbit.  The exact inverse
    hub forces a c=0 reset with odd middle coordinate 1 (mod 4),
    contradicting the same source-image invariant. -/
theorem qfan_parent_not_reach_vq0_k4
    (t q U k : Nat)
    (ht : 1 ≤ t)
    (hUge : 4 ≤ U)
    (hUeven : U % 2 = 0)
    (hpow : 43*t-1 = 4^q*U)
    (hcost : 2*k+U+6*q = 128*t-8)
    (hvq : (U/2+q)%4=0)
    (hk8 : k%8=4) :
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
  have hkge : 7 ≤ k := by omega
  have hcostV : k+V+3*q=64*t-4 := by omega
  have hvq' : (V+q)%4=0 := by
    simpa [V] using hvq
  have hsumEq : U-2+k=V+64*t-6-3*q := by omega
  have hsum : (U-2+k)%4=2 := by
    rw [hsumEq]
    omega
  intro hreach
  have hreach0 : BB6CLine.Reach (U-2,(k-7)+7,0) := by
    have heq : (k-7)+7=k := by omega
    simpa [heq] using hreach
  have hhub := BB6.CBack.reached_zero_hub (U-2) (k-7) hreach0
  let A := U-2+k-5
  have hleft : U-2+(k-7)+2=A := by
    dsimp [A]
    omega
  have hright : (k-7)+5=k-2 := by omega
  have hhub' : BB6CLine.Reach (A,2,k-2) := by
    simpa [hleft,hright] using hhub
  have hAmod : A%4=1 := by
    dsimp [A]
    omega
  have hAne : A%4≠2 := by omega
  have hhubInput : BB6CLine.Reach (A,2,(k-6)+4) := by
    have heq : (k-6)+4=k-2 := by omega
    simpa [heq] using hhub'
  have hprev := BB6.CBack.reached_hub_prev A (k-6) hhubInput hAne
  have hprev' : BB6CLine.Reach (A+1,1,(k-5)+4) := by
    have heq : (k-6)+5=(k-5)+4 := by omega
    simpa [heq] using hprev
  have hsplit := BB6.CBack.reached_one_high_or_reset (A+1) (k-5) hprev'
  rcases hsplit with hhigh | ⟨r,hrEq,hreset⟩
  · have hhigh' : BB6CLine.Reach (A+2,0,k) := by
      have heq : (k-5)+5=k := by omega
      simpa [heq] using hhigh
    have hmid := BB6.Agent48.reached_middle_zero_mod4 (A+2) k hhigh'
    have hAplus2 : (A+2)%4=3 := by
      dsimp [A]
      omega
    omega
  · have hrMod : r%4=1 := by omega
    have hrge : 5≤r := by omega
    have hleftMod : (A+3)%4=0 := by
      dsimp [A]
      omega
    have hsumR : ((A+3)+r)%4=1 := by omega
    have hhole := BB6.CRange.reached_odd_zero_mod4_hole
      (A+3) r hreset hrge (by omega)
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
      (U/2+q)%4≠3 ∧
      ((U/2+q)%4≠0 ∨ k%8≠4) := by
  obtain ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩ :=
    BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan t a k ht hsec
  refine ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost,?_⟩
  · intro hvq
    have hreach' : BB6CLine.Reach (U-2,k,0) := by
      simpa [ha] using hreach
    exact qfan_parent_not_reach_vq3 t q U k ht hUge hUeven
      hpow hcost hvq hreach'
  · by_contra hbad
    have hvq0 : (U/2+q)%4=0 := by omega
    have hk8 : k%8=4 := by omega
    have hreach' : BB6CLine.Reach (U-2,k,0) := by
      simpa [ha] using hreach
    exact qfan_parent_not_reach_vq0_k4 t q U k ht hUge hUeven
      hpow hcost hvq0 hk8 hreach'

#print axioms qfan_parent_not_reach_vq3
#print axioms qfan_parent_not_reach_vq0_k4
#print axioms reachable_q0_parent_filter

end BB6.Agent3U5CLineFilter
