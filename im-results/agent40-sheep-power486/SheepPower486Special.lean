import SheepPower486Target
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace SheepPower486

private theorem exp_dominates (n : Nat) (hn : 480 ≤ n) :
    729*(n+9)+64 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : n=480
    · subst n
      decide
    have hprev : 480≤n-1 := by omega
    have hlt : n-1<n := by omega
    have ip := ih (n-1) hlt hprev
    have hs : n=n-1+1 := by omega
    have hp : 2^n=2*2^(n-1) := by
      calc
        2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) hs
        _ = 2*2^(n-1) := by rw [Nat.pow_succ]; omega
    rw [hp]
    omega

/-- A uniform exponential gap forbids exceptional cofactor-three sources. -/
private theorem no_special_band
    (j h a e D S : Nat)
    (hj : 486 ≤ j) (hD : D ≤ 729) (hS : S ≤ 64)
    (hebound : e ≤ h+5)
    (he_low : 2^e < 3*D) (he_high : 3*D < 2^(e+1))
    (heq : 3*D*2^a + D*(a+2)+S = 2^(j+h)) : False := by
  let z := j+h-e
  have hzEq : j+h=e+z := by dsimp [z]; omega
  have hzBound : 481≤z := by dsimp [z]; omega
  by_cases hz : z≤a
  · have hpow : 2^z ≤ 2^a := Nat.pow_le_pow_right (by decide) hz
    have hmpos : 0<2^z := Nat.pow_pos (by decide)
    have hp : 2^(j+h)=2^e*2^z := by
      calc
        2^(j+h) = 2^(e+z) := congrArg (fun m:Nat => 2^m) hzEq
        _ = 2^e*2^z := Nat.pow_add ..
    have hmul1 : 2^e*2^z < 3*D*2^z :=
      Nat.mul_lt_mul_of_pos_right he_low hmpos
    have hmul2 : 3*D*2^z ≤ 3*D*2^a := Nat.mul_le_mul_left (3*D) hpow
    omega
  · have haw : a≤z-1 := by omega
    let w := z-1
    have hw : 480≤w := by dsimp [w]; omega
    have hEq : j+h=(e+1)+w := by dsimp [w]; omega
    have hp : 2^(j+h)=2^(e+1)*2^w := by
      calc
        2^(j+h) = 2^((e+1)+w) := congrArg (fun m:Nat => 2^m) hEq
        _ = 2^(e+1)*2^w := Nat.pow_add ..
    have hpow : 2^a ≤ 2^w := Nat.pow_le_pow_right (by decide) haw
    have hmul : 3*D*2^a ≤ 3*D*2^w := Nat.mul_le_mul_left (3*D) hpow
    have hsmall1 : D*(a+2) ≤ D*(w+9) :=
      Nat.mul_le_mul_left D (by omega)
    have hsmall2 : D*(w+9) ≤ 729*(w+9) :=
      Nat.mul_le_mul_right (w+9) hD
    have hsmall3 := exp_dominates w hw
    have hq : D*(a+2)+S < 2^w := by omega
    have hcoef : 3*D+1 ≤2^(e+1) := by omega
    have htotal : (3*D+1)*2^w ≤2^(e+1)*2^w :=
      Nat.mul_le_mul_right (2^w) hcoef
    have hsum : 3*D*2^w + 2^w = (3*D+1)*2^w := by
      rw [Nat.add_mul]
      omega
    omega

/-- No exceptional cofactor-three edge reaches any sixth-stratum target. -/
theorem no_special_all_a (h a t : Nat)
    (hh : h≤6) (ht : 1≤t)
    (heq : 3^h*(3*2^a+a+2)+2^h = 2^(486*t+h)) : False := by
  have hj : 486≤486*t := by omega
  have htri : 3^h*(3*2^a+a+2) = 3*(3^h)*2^a+3^h*(a+2) := by
    have hsum : 3*2^a+a+2 = (3*2^a)+(a+2) := by omega
    rw [hsum, Nat.mul_add]
    have hac : 3^h*(3*2^a) = 3*(3^h)*2^a := by ac_rfl
    rw [hac]
  have hsrc : 3*(3^h)*2^a+3^h*(a+2)+2^h=2^(486*t+h) := by omega
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 from by omega) with h0|h1|h2|h3|h4|h5|h6
  · subst h
    exact no_special_band (486*t) 0 a 1 1 1
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)
  · subst h
    exact no_special_band (486*t) 1 a 3 3 2
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)
  · subst h
    exact no_special_band (486*t) 2 a 4 9 4
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)
  · subst h
    exact no_special_band (486*t) 3 a 6 27 8
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)
  · subst h
    exact no_special_band (486*t) 4 a 7 81 16
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)
  · subst h
    exact no_special_band (486*t) 5 a 9 243 32
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)
  · subst h
    exact no_special_band (486*t) 6 a 11 729 64
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

#print axioms exp_dominates
#print axioms no_special_band
#print axioms no_special_all_a
end SheepPower486
