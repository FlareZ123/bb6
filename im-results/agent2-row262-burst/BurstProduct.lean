import Valuation
set_option maxHeartbeats 2000000
namespace BB6.Row262

theorem rightBurst_comm (q : Nat) :
    rightBurst q ++ [false,false,true] = [false,false,true] ++ rightBurst q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      change (rightBurst q ++ [false,false,true]) ++ [false,false,true] =
        [false,false,true] ++ (rightBurst q ++ [false,false,true])
      rw [ih]
      simp [ih]

theorem rightBurst_front (q : Nat) :
    rightBurst (q+1) = [false,false,true] ++ rightBurst q := rightBurst_comm q

theorem bits_011 (xs : List Bool) :
    bitsVal (false::true::true::xs) = 6 + 8*bitsVal xs := by simp [bitsVal]; omega

-- The 7-adjusted right tape is multiplied by 8 for each initial 001 triple.
theorem right_factor (q : Nat) (ys : List Bool) :
    7*bitsVal (rightBurst q ++ ys)+4 = 8^q * (7*bitsVal ys+4) := by
  induction q with
  | zero => simp [rightBurst]
  | succ q ih =>
      have hlist : rightBurst (q+1) ++ ys = false::false::true::(rightBurst q ++ ys) := by
        rw [rightBurst_front]; rfl
      rw [hlist, bits_001]
      calc
        7*(4+8*bitsVal (rightBurst q ++ ys))+4 =
            8*(7*bitsVal (rightBurst q ++ ys)+4) := by omega
        _ = 8*(8^q*(7*bitsVal ys+4)) := by rw [ih]
        _ = 8^(q+1)*(7*bitsVal ys+4) := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

-- The 7-adjusted left tape is multiplied by 8 for each initial 011 triple.
theorem left_factor (q : Nat) (ls : List Bool) :
    7*bitsVal (leftBurst q ++ ls)+6 = 8^q * (7*bitsVal ls+6) := by
  induction q with
  | zero => simp [leftBurst]
  | succ q ih =>
      have hlist : leftBurst (q+1) ++ ls = false::true::true::(leftBurst q ++ ls) := by rfl
      rw [hlist, bits_011]
      calc
        7*(6+8*bitsVal (leftBurst q ++ ls))+6 =
            8*(7*bitsVal (leftBurst q ++ ls)+6) := by omega
        _ = 8*(8^q*(7*bitsVal ls+6)) := by rw [ih]
        _ = 8^(q+1)*(7*bitsVal ls+6) := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

-- A multiplicative first integral of every source-certified 9q burst:
-- (7L+6)(7R+9) is conserved, where L and R encode finite side tapes.
theorem burst_product_invariant (q : Nat) (ls ys : List Bool) :
    (7*bitsVal (leftBurst q ++ ls)+6) *
      (7*bitsVal ([true,false] ++ ys)+9) =
    (7*bitsVal ls+6) *
      (7*bitsVal ([true,false] ++ rightBurst q ++ ys)+9) := by
  have hleft := left_factor q ls
  have hright := right_factor q ys
  have hpre : 7*bitsVal ([true,false] ++ rightBurst q ++ ys)+9 =
        4 * (7*bitsVal (rightBurst q ++ ys)+4) := by simp [bitsVal]; omega
  have hpost : 7*bitsVal ([true,false] ++ ys)+9 = 4*(7*bitsVal ys+4) := by
    simp [bitsVal]; omega
  rw [hleft,hpre,hpost,hright]
  ac_rfl

#print axioms BB6.Row262.right_factor
#print axioms BB6.Row262.left_factor
#print axioms BB6.Row262.burst_product_invariant
end BB6.Row262
