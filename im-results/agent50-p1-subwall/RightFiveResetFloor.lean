import ExceptionalLastResetDepthSource

namespace BB6.Agent50RightFive

open BB6.Agent28 BB6.Agent1UpperTail BB6.Agent50ExceptionalDepth

/-- A genuine depth-zero inverse step cannot produce right counter five.
    Consequently an all-zero-reset inverse tail beginning at right counter
    three cannot end at right counter five. -/
theorem upper_tail_from_three_never_five
    (b0 m0 b m r : Nat)
    (hu : UpperTail b0 3 m0 b 5 m r) : False := by
  cases hu with
  | step =>
      have hstep := inv0_halve _ _ _ 1 (by assumption) (by assumption)
      omega

/-- A zero-length upper tail preserves the right counter. -/
theorem upper_tail_zero_right
    (b0 d0 m0 b d m r : Nat)
    (hu : UpperTail b0 d0 m0 b d m r) (hz : r=0) : d=d0 := by
  cases hu with
  | root => rfl
  | step bp dp mp s k c hpre hb hb4 hd hi hk hc => omega

private theorem five_mul_le_pow (n : Nat) (hn : 5 ≤ n) :
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

/-- The source's exceptional right-five gate requires two positive-depth
    inverse resets, with no restriction on cost or inverse-word length.
    This constrains source CountCone witnesses and makes no claim of genuine
    forward blank-orbit reachability. -/
theorem source_right_five_needs_two_resets
    (n b m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    2 ≤ z := by
  by_cases hbig : 2 ≤ z
  · exact hbig
  · exfalso
    have hzCases : z=0 ∨ z=1 := by omega
    rcases hzCases with hzero | hone
    · obtain ⟨s,hu⟩ := (cone_shape _ _ b 5 m z h).1 hzero
      exact False.elim (upper_tail_from_three_never_five _ _ _ _ _ hu)
    · have hzpos : 1 ≤ z := by omega
      obtain ⟨bp,dp,mp,zp,t,k,hpre,hzEq,hip,hb,hkm,hbpPow,hdpPow,
        hcost,henergy,henergyB,hmCost,hdpMin,hexact,hup,hlow,htLow,htUpper⟩ :=
        source_exceptional_last_reset_depth_window n b 5 m z hn hzpos h rfl
      have hzp : zp=0 := by omega
      have hprefix : CountCone (14*2^n-2*n-16) 3 bp dp mp 0 := by
        simpa only [hzp] using hpre
      obtain ⟨r,hu⟩ := (cone_shape _ _ bp dp mp 0 hprefix).1 rfl
      have hdy := upper_tail_dyadic
        (14*2^n-2*n-16) 3 0 bp dp mp r hu
      have hrpos : 1 ≤ r := by
        by_cases hrzero : r=0
        · have hroot : dp=3 :=
            upper_tail_zero_right _ _ _ _ _ _ _ hu hrzero
          omega
        · omega
      have hprefixEnergy : mp ≤ n+1 := by
        have he := BB6.Agent43CountedEnergy.source_counted_cost_linear_in_resets
          n bp dp mp 0 hn hprefix
        simpa using he
      have h5n : 5*n ≤ 2^n := five_mul_le_pow n (by omega)
      have hP : 2 ≤ 2^r := by
        have hh := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hrpos
        simpa using hh
      have hleftBound : 2*(bp+12) ≤ (14*2^n-2*n-16)+12 := by
        calc
          _ ≤ 2^r*(bp+12) := Nat.mul_le_mul_right (bp+12) hP
          _ = _ := hdy.1
      have hroot : (14*2^n-2*n-16)+12+2*n+4=14*2^n := by omega
      have hbpBound : bp ≤ 7*2^n := by omega
      have hpow : 2^(t+3) ≤ 2^(n+4) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hfour : 2^(n+4)=16*2^n := by simp [Nat.pow_add, Nat.mul_comm]
      have hpowBound : 2^(t+3) ≤ 16*2^n := by omega
      have hlast : bp+2^(t+3)+4*mp+4*n+20=28*2^n := by omega
      omega

#print axioms BB6.Agent50RightFive.upper_tail_from_three_never_five
#print axioms BB6.Agent50RightFive.source_right_five_needs_two_resets

end BB6.Agent50RightFive
