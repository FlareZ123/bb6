import CountedLastResetDraft

namespace BB6.Agent43LastResetStrength

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetDraft

private theorem five_times_le_two_pow (n : Nat) (hn : 5 ≤ n) :
    5*n ≤ 2^n := by
  have hb : ∀ k : Nat, 5*(k+5) ≤ 2^(k+5) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hidx : (k+1)+5 = (k+5)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have heq : (n-5)+5 = n := by omega
  simpa only [heq] using hb (n-5)

/-- The original P1 odd-cone source mass is retained by its counted witness. -/
theorem counted_to_odd_cone (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) : OddCone b0 d0 b d m := by
  induction h with
  | root => exact OddCone.root
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
      exact OddCone.parent b d m t k c ih hb hb4 hd hi hk hc

/-- Original inverseAt power and mass force a large outgoing left coordinate
    at the final positive reset of a low-cost critical affine-wall candidate.
    This lemma itself does not use the affine-wall endpoint. -/
theorem source_last_positive_large_left
    (n bp dp mp t k c m z : Nat)
    (hn : 14 ≤ n) (hz : 1 ≤ z)
    (hpre : OddCone (14*2^n-2*n-16) 3 bp dp mp)
    (hb : 8 ≤ bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp t=some (k,c))
    (hk : 2 ≤ k) (hc : c%2=1) (ht : 1 ≤ t)
    (hm1 : mp+t+1 ≤ m)
    (hcount : 2*z ≤ mp+t+1)
    (hcost : m ≤ n+z) :
    3*2^n ≤ k+4 := by
  have hfive : 5*n ≤ 2^n :=
    five_times_le_two_pow n (by omega)
  have hroot : (14*2^n-2*n-16)+2*n+16=14*2^n := by omega
  have hmassPre := odd_cone_mass
    (14*2^n-2*n-16) 3 bp dp mp hpre
  have hp := (inverseAt_iff_power_mass bp dp t k c
    (by omega) hb4 hd).mp hi
  have hpowlt : (2:Nat)^0 < 2^t :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have htwo : 2 ≤ (2:Nat)^t := by
    simp only [pow_zero] at hpowlt
    omega
  have hpowBound : 2*(c+3) ≤ 2^t*(c+3) :=
    Nat.mul_le_mul_right (c+3) htwo
  have hcBound : c+n+8 ≤ 7*2^n := by omega
  have hpost : OddCone (14*2^n-2*n-16) 3
      (2*k-4) (c+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k c hpre hb hb4 hd hi hk hc
  have hmassPost := odd_cone_mass
    (14*2^n-2*n-16) 3
    (2*k-4) (c+4) (mp+t+1) hpost
  omega

#print axioms BB6.Agent43LastResetStrength.counted_to_odd_cone
#print axioms BB6.Agent43LastResetStrength.source_last_positive_large_left

end BB6.Agent43LastResetStrength
