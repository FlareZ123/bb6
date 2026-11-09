import SweepBitOutcome

namespace CascadeFastReturn
open CascadeBitSweep

/-- Every odd source-C first return advances beyond the current dyadic 8p gate. -/
theorem bitOutcome_odd_crosses (h u : Nat)
    (ho : bitOutcome h=some u)
    (hodd : (h+firstFailIndex h)%2=1) :
    8*2^(firstFailIndex h) ≤ u := by
  let k := firstFailIndex h
  let p := 2^k
  let q := 4*p+(h+k)/2+3
  let t := (stripTwos q).1
  let d := (stripTwos q).2
  have hlower : 4*p ≤ h+k+4 := firstFailIndex_low h
  have hqpos : 0<q := by dsimp [q]; omega
  have hqbound : 6*p+1 ≤ q := by dsimp [q]; omega
  have hfactor : q=2^t*d := (stripTwos_spec q hqpos).1
  have hpow : 2^t ≤ 3^t := Nat.pow_le_pow_left (by decide) t
  have hprod : 3*q ≤ 3^(t+1)*d := by
    rw [hfactor]
    calc
      3*(2^t*d) ≤ 3*(3^t*d) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right d hpow)
      _ = 3^(t+1)*d := by rw [Nat.pow_succ]; ac_rfl
  have hnot : (h+k)%2≠0 := by omega
  change (if h+k+4=4*2^k then none
    else if (h+k)%2=0 then some (4*2^k+(h+k)/2)
    else some ((3^(t+1)*d-5)/2)) = some u at ho
  by_cases hf : h+k+4=4*2^k
  · simp [hf] at ho
  · simp [hf,hnot] at ho
    have hp : 1≤p := Nat.one_le_pow k 2 (by decide)
    change 8*p ≤ u
    omega

#print axioms bitOutcome_odd_crosses
end CascadeFastReturn
