import Std

namespace CascadeSlopeGap

/-- A cycle of ordered slope gaps with one additive boundary event has
    the same full denominator as its unsimplified affine composition. -/
theorem constant_gap_denominator
    (r p M R Q q g h t : Nat)
    (e1 : 2*p*g = r*(q+h))
    (e2 : p*h = r*t)
    (e3 : M*t = R*g)
    (e4 : 2*p*p*M = Q+r*r*R)
    (hc : Nat.Coprime Q (r*p*M)) : Q ∣ q := by
  have he : (2*p*p*M)*g = (r*p*M)*q + (r*r*R)*g := by
    calc
      (2*p*p*M)*g = (p*M)*(2*p*g) := by ac_rfl
      _ = (p*M)*(r*(q+h)) := by rw [e1]
      _ = (r*p*M)*q + (r*M)*(p*h) := by grind
      _ = (r*p*M)*q + (r*M)*(r*t) := by rw [e2]
      _ = (r*p*M)*q + (r*r)*(M*t) := by ac_rfl
      _ = (r*p*M)*q + (r*r)*(R*g) := by rw [e3]
      _ = (r*p*M)*q + (r*r*R)*g := by ac_rfl
  rw [e4, Nat.add_mul] at he
  have hq : Q*g = (r*p*M)*q := Nat.add_right_cancel he
  exact hc.dvd_of_dvd_mul_left ⟨g, hq.symm⟩

/-- If a positive bounded rational gap has no additive event inside a
    segment, its numerator plus q must be divisible by the full power
    of two consumed by the segment. -/
theorem gap_segment_bound (q n n' a b : Nat)
    (hn : 0 < n) (hlt : n < q)
    (he : 2^b*n' = 3^a*(n+q)) : 2^b < 2*q := by
  have hc : Nat.Coprime (2^b) (3^a) := (by decide : Nat.Coprime 2 3).pow b a
  have hd : 2^b ∣ n+q := hc.dvd_of_dvd_mul_left ⟨n', he.symm⟩
  have hh := Nat.le_of_dvd (by omega : 0 < n+q) hd
  omega

/-- The unsimplified slope denominator exceeds the second-difference
    limit whenever A>=D and L,D>0, using the strict slope-product bound. -/
theorem full_denominator_excludes (A L D Q : Nat)
    (hAD : D ≤ A) (hL : 0 < L) (hD0 : 0 < D)
    (hR : 3^A < 2^(A+D))
    (he : Q+3^A = 2^(A+L+D)) : ¬ Q ∣ (2^D-1)^2 := by
  have hpow : 2^(A+D) ≤ 2^(A+L+D) / 2 := by
    have hle : 2^(A+D+1) ≤ 2^(A+L+D) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hle
    omega
  have hlarge : 2^(A+D) < Q := by omega
  have hD : 2^(D+D) ≤ 2^(A+D) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add] at hD
  have hpos : 0 < 2^D := Nat.pow_pos (by decide)
  have hlim : (2^D-1)^2 < Q := by
    rw [Nat.pow_succ, Nat.pow_one]
    have hh : (2^D-1)*(2^D-1) ≤ 2^D*2^D :=
      Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)
    omega
  intro hd
  have hpos' : 0 < (2^D-1)^2 := by
    have hge : 2^1 ≤ 2^D := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.pow_pos (by omega)
  exact (Nat.not_le_of_lt hlim) (Nat.le_of_dvd hpos' hd)

end CascadeSlopeGap

#print axioms CascadeSlopeGap.constant_gap_denominator
#print axioms CascadeSlopeGap.gap_segment_bound
#print axioms CascadeSlopeGap.full_denominator_excludes
