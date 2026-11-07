import Std

namespace PeriodCore

theorem iterated_dilation (A : Nat) (e : Nat → Int)
    (he : ∀ n, e n = (A : Int) * e (n+1)) :
    ∀ n, e 0 = ((A^n : Nat) : Int) * e n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, he n]
    rw [Nat.pow_succ, Int.natCast_mul]
    simp only [Int.mul_assoc]

private theorem grow (A x : Nat) (hA : 2 ≤ A) : x < A^x := by
  have h1 : x < 2^x := Nat.lt_two_pow_self
  have h2 : 2^x ≤ A^x := Nat.pow_le_pow_left hA x
  omega

theorem forced_zero (A : Nat) (hA : 2 ≤ A) (e : Nat → Int)
    (he : ∀ n, e n = (A : Int) * e (n+1)) : e 0 = 0 := by
  let N := (e 0).natAbs
  have hg : N < A^N := grow A N hA
  have eq0 := iterated_dilation A e he N
  have habs : (e 0).natAbs = A^N * (e N).natAbs := by
    have := congrArg Int.natAbs eq0
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using this
  by_cases hn : e N = 0
  · rw [hn] at eq0
    simpa using eq0
  · have hn1 : 1 ≤ (e N).natAbs := by
      have hh : (e N).natAbs ≠ 0 := by simpa using hn
      omega
    have hb : A^N ≤ A^N * (e N).natAbs := by
      have := Nat.mul_le_mul_left (A^N) hn1
      simpa using this
    omega

theorem affine_difference (A H S X D : Int) (z : Nat → Int)
    (hr : ∀ n, A * z (n+1) = z n + H*X + (H*S)*(n:Int) + D) :
    ∀ n, A*(z (n+2)-z (n+1)) = z (n+1)-z n + H*S := by
  intro n
  have h0 := hr n
  have h1 := hr (n+1)
  have hc : ((n+1:Nat):Int) = (n:Int)+1 := by simp
  have hi : n + 1 + 1 = n + 2 := by omega
  rw [hi, hc, Int.mul_add] at h1
  simp only [Int.mul_sub]
  omega

theorem periodic_integral_slope (A : Nat) (hA : 2 ≤ A)
    (H S X D : Int) (z : Nat → Int)
    (hr : ∀ n, (A:Int) * z (n+1) = z n + H*X + (H*S)*(n:Int) + D) :
    ∃ d : Int, ((A:Int)-1)*d = H*S := by
  let delta : Nat → Int := fun n => z (n+1) - z n
  let err : Nat → Int := fun n => ((A:Int)-1)*delta n-H*S
  have hdiff := affine_difference (A:Int) H S X D z hr
  have herr : ∀ n, err n = (A:Int) * err (n+1) := by
    intro n
    have hd : (A:Int)*delta (n+1) = delta n+H*S := by
      simpa only [delta, show n+1+1 = n+2 by omega] using hdiff n
    have hmul := congrArg (fun x : Int => ((A:Int)-1)*x) hd
    have hx : (A:Int)*(((A:Int)-1)*delta (n+1)) =
        ((A:Int)-1)*delta n + ((A:Int)-1)*(H*S) := by
      calc
        _ = ((A:Int)-1)*((A:Int)*delta (n+1)) := by
          simp only [Int.mul_left_comm]
        _ = _ := by simpa only [Int.mul_add] using hmul
    have hs : ((A:Int)-1)*(H*S) = (A:Int)*(H*S) - H*S := by
      rw [Int.sub_mul]
      simp
    change ((A:Int)-1)*delta n-H*S =
      (A:Int)*(((A:Int)-1)*delta (n+1)-H*S)
    rw [hs] at hx
    calc
      _ = (A:Int)*(((A:Int)-1)*delta (n+1))-(A:Int)*(H*S) := by omega
      _ = (A:Int)*(((A:Int)-1)*delta (n+1)-H*S) := by
        exact (Int.mul_sub _ _ _).symm
  have hz := forced_zero A hA err herr
  refine ⟨delta 0, ?_⟩
  dsimp [err] at hz
  omega

theorem no_periodic_affine_ray (A : Nat) (hA : 2 ≤ A)
    (H S X D : Int) (z : Nat → Int)
    (hbad : ∀ d : Int, ((A:Int)-1)*d ≠ H*S)
    (hr : ∀ n, (A:Int)*z (n+1) = z n + H*X + (H*S)*(n:Int) + D) :
    False := by
  obtain ⟨d, hd⟩ := periodic_integral_slope A hA H S X D z hr
  exact hbad d hd

-- The depth pattern t = [0,1] has total cost S=3 and marker H=5.
-- Its block recurrence would have A=8 and HS=15; 7 does not divide 15.
theorem no_mixed_01_ray (X D : Int) (z : Nat → Int)
    (hr : ∀ n, (8:Int)*z (n+1) = z n + 5*X + 15*(n:Int) + D) :
    False := by
  apply no_periodic_affine_ray 8 (by decide) 5 3 X D z ?_ ?_
  · intro d hd
    omega
  · simpa using hr

end PeriodCore
#print axioms PeriodCore.periodic_integral_slope
#print axioms PeriodCore.no_mixed_01_ray
