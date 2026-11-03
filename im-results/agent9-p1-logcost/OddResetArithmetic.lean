import Init.Omega
namespace BB6.Agent9OddReset

/-- A non-upper odd inverse edge cannot create a small left counter when
    total inverse cost is below the exponential threshold. -/
theorem positive_depth_odd_has_large_left
    (q u e b d m t k c : Nat)
    (hq : 1≤q)
    (he : e=3 ∨ e=5)
    (hu : u+4*q+3=7*2^(16*q))
    (hmass : b+d+2*m=8*u+e)
    (hinverse : d+b/2+3=2^t*(c+3))
    (hcost : 2*k+c+2*t+2=b+d)
    (hk : 2≤k)
    (ht : 1≤t)
    (htbound : t≤16*q+4)
    (hbudget : m+t+1 < 8*2^(16*q))
    (hP : 256*q ≤ 2^(16*q)) :
    19*2^(16*q) ≤ 2*k-4 := by
  have htwopow : 2≤2^t := by
    have hp : 2^1≤2^t := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
    simpa using hp
  have hcu : 2*(c+3)≤d+b/2+3 := by
    calc
      2*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) htwopow
      _ = d+b/2+3 := hinverse.symm
  have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
  rcases he with he | he <;> omega

/-- A depth >=2 odd inverse branch resets the left counter even higher. -/
theorem deeper_odd_has_large_left
    (q u e b d m t k c : Nat)
    (hq : 1≤q)
    (he : e=3 ∨ e=5)
    (hu : u+4*q+3=7*2^(16*q))
    (hmass : b+d+2*m=8*u+e)
    (hinverse : d+b/2+3=2^t*(c+3))
    (hcost : 2*k+c+2*t+2=b+d)
    (hk : 2≤k)
    (ht : 2≤t)
    (htbound : t≤16*q+4)
    (hbudget : m+t+1 < 8*2^(16*q))
    (hP : 256*q ≤ 2^(16*q)) :
    29*2^(16*q) ≤ 2*k-4 := by
  have htwopow : 4≤2^t := by
    have hp : 2^2≤2^t := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ht
    simpa using hp
  have hcu : 4*(c+3)≤d+b/2+3 := by
    calc
      4*(c+3) ≤ 2^t*(c+3) := Nat.mul_le_mul_right (c+3) htwopow
      _ = d+b/2+3 := hinverse.symm
  have hscaled : 8*u+32*q+24=56*2^(16*q) := by omega
  rcases he with he | he <;> omega

#print axioms deeper_odd_has_large_left
#print axioms positive_depth_odd_has_large_left
end BB6.Agent9OddReset
