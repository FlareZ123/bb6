import OddRescale

namespace BB6.Agent9CrossFeeder

/-- Infinite shared-depth difference dynamics with identical L parameters
force identical shadow coordinates at every position. -/
theorem zero_offset_difference_vanishes
    (D : Nat → Int) (t : Nat → Nat)
    (hstep : ∀ n, D n=(2:Int)^(t n)*(2*D (n+1))) :
    ∀ n, D n=0 := by
  intro n
  by_cases hzero : D n=0
  · exact hzero
  let N : Nat := (D n).natAbs+1
  obtain ⟨u,v,heq⟩ := difference_2adic_prefix 0 D t (by
    intro j
    simpa using hstep j) n N
  have hdivI : (2:Int)^N ∣ D n := by
    refine ⟨u,?_⟩
    simpa using heq
  have hdivN : (2:Nat)^N ∣ (D n).natAbs := by
    have h := (Int.natAbs_dvd_natAbs).mpr hdivI
    simpa only [Int.natAbs_pow, show (2:Int).natAbs=2 by decide] using h
  have hpos : 0 < (D n).natAbs := Int.natAbs_pos.mpr hzero
  have hle := Nat.le_of_dvd hpos hdivN
  have hlt : (D n).natAbs < 2^N := by
    have hh := Nat.lt_two_pow_self (n:=N)
    omega
  omega

#print axioms zero_offset_difference_vanishes
end BB6.Agent9CrossFeeder
