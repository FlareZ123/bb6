import Std

namespace PeriodicTriple

private theorem small_multiple_zero (M B : Nat) (hbig : 2*B < M)
    (z : Int) (hz : z.natAbs ≤ 2*B) (hdiv : (M:Int) ∣ z) :
    z = 0 := by
  obtain ⟨k, hk⟩ := hdiv
  have habs : z.natAbs = M * k.natAbs := by
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
  by_cases hzero : k = 0
  · simpa [hzero] using hk
  · have hkpos : 1 ≤ k.natAbs := by
      have hh := Int.natAbs_pos.mpr hzero
      omega
    have hle : M ≤ M * k.natAbs := by
      simpa using Nat.mul_le_mul_left M hkpos
    omega

/-- Three consecutive copies of an identical affine-rank word suffice to
    force the first and second period differences to agree, if the scale
    M beats twice the maximum first-coordinate height B. -/
theorem three_periods_force_affine (M B a b c d p q : Nat)
    (hlarge : 2*B < M) (ha : a ≤ B) (hb : b ≤ B) (hc : c ≤ B)
    (h0 : M*b = a+q)
    (h1 : M*c = b+p+q)
    (h2 : M*d = c+2*p+q) :
    (a:Int)+(c:Int)=2*(b:Int) ∧
      ((M:Int)-1)*((b:Int)-(a:Int)) = (p:Int) := by
  let delta : Int := (c:Int)-2*(b:Int)+(a:Int)
  have hrange : -2*(B:Int) ≤ delta ∧ delta ≤ 2*(B:Int) := by
    dsimp [delta]
    omega
  have habs : delta.natAbs ≤ 2*B := by
    obtain hs | hs := Int.natAbs_eq delta
    · omega
    · omega
  have hdvd : (M:Int) ∣ delta := by
    have hh0 : (M:Int)*(b:Int) = (a:Int)+(q:Int) := by exact_mod_cast h0
    have hh1 : (M:Int)*(c:Int) = (b:Int)+(p:Int)+(q:Int) := by exact_mod_cast h1
    have hh2 : (M:Int)*(d:Int) = (c:Int)+2*(p:Int)+(q:Int) := by exact_mod_cast h2
    refine ⟨(d:Int)-2*(c:Int)+(b:Int), ?_⟩
    dsimp [delta]
    grind
  have hz := small_multiple_zero M B hlarge delta habs hdvd
  constructor
  · dsimp [delta] at hz
    omega
  · have hh0 : (M:Int)*(b:Int) = (a:Int)+(q:Int) := by exact_mod_cast h0
    have hh1 : (M:Int)*(c:Int) = (b:Int)+(p:Int)+(q:Int) := by exact_mod_cast h1
    dsimp [delta] at hz
    grind

#print axioms three_periods_force_affine
end PeriodicTriple
