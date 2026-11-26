import Std

namespace BB6.Agent10BetaThreeBridge

set_option maxHeartbeats 1000000

/-- For a negative three-phase beta cycle, write the inverse recurrence
    R_i u_i = R_i r + P_i u_(i+1), with positive magnitude u_i.
    If the product of the R_i is at least twice the product of the P_i,
    and each P_i≤2R_i, every phase satisfies u_i≤14r. -/
theorem phase_bound {a b c x y z u v w r : Nat}
    (hR : 0<a*b*c)
    (ha : a*u=a*r+x*v) (hb : b*v=b*r+y*w) (hc : c*w=c*r+z*u)
    (hx : x≤2*a) (hy : y≤2*b) (hprod : 2*(x*y*z)≤a*b*c) : u≤14*r := by
  have h0 : (a*b*c)*u=(a*b*c)*r+(x*b*c)*r+(x*y*c)*r+(x*y*z)*u := by
    calc
      _ = (b*c)*(a*u) := by ac_rfl
      _ = (b*c)*(a*r+x*v) := by rw [ha]
      _ = (a*b*c)*r+x*c*(b*v) := by rw [Nat.mul_add]; ac_rfl
      _ = (a*b*c)*r+x*c*(b*r+y*w) := by rw [hb]
      _ = (a*b*c)*r+(x*b*c)*r+x*y*(c*w) := by rw [Nat.mul_add]; ac_rfl
      _ = (a*b*c)*r+(x*b*c)*r+x*y*(c*r+z*u) := by rw [hc]
      _ = _ := by rw [Nat.mul_add]; ac_rfl
  have h1 : x*b*c≤2*(a*b*c) := by
    calc
      _ ≤ (2*a)*b*c := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hx)
      _ = _ := by ac_rfl
  have h2 : x*y*c≤4*(a*b*c) := by
    calc
      _ ≤ (2*a)*(2*b)*c := Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hy)
      _ = _ := by change _ = (2*2)*(a*b*c); ac_rfl
  have hsum : (a*b*c)*u≤7*((a*b*c)*r)+(x*y*z)*u := by
    rw [h0]
    have h1' := Nat.mul_le_mul_right r h1
    have h2' := Nat.mul_le_mul_right r h2
    rw [show (2*(a*b*c))*r = 2*((a*b*c)*r) by ac_rfl] at h1'
    rw [show (4*(a*b*c))*r = 4*((a*b*c)*r) by ac_rfl] at h2'
    omega
  have hh : 2*((a*b*c)*u)≤14*((a*b*c)*r)+(a*b*c)*u := by
    have hp := Nat.mul_le_mul_right u hprod
    rw [Nat.mul_assoc] at hp
    omega
  have h : (a*b*c)*u≤(a*b*c)*(14*r) := by
    have he : (a*b*c)*(14*r)=14*((a*b*c)*r) := by ac_rfl
    rw [he]; omega
  exact Nat.le_of_mul_le_mul_left h hR

/-- Each reduced numerator is divisible by the full power of three of the
    preceding valuation, because the denominator multiplier is a power of 2. -/
theorem numerator_dvd {a u v r : Nat} (h : 3^a*(u-r)=2^(a+1)*v) : 3^a∣v := by
  have hc : (3^a).Coprime (2^(a+1)) :=
    (show Nat.Coprime 3 2 by decide).pow_left _ |>.pow_right _
  apply hc.dvd_of_dvd_mul_left
  exact ⟨u-r,h.symm⟩

/-- For any lower valuation cutoff c≤a, the inverse recurrence and the
    uniform numerator upper bound force u close to r. -/
theorem close_to_r {a c u v r : Nat} (hc : c≤a)
    (h : 3^a*(u-r)=2^(a+1)*v) (hv : v≤14*r) : 3^c*(u-r)≤28*r*2^c := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hc
  have hk : 2^k≤3^k := Nat.pow_le_pow_left (by decide) _
  have he : 3^k*(3^c*(u-r))=2^k*(2^(c+1)*v) := by
    rw [Nat.pow_add 3] at h
    rw [show c+k+1=k+(c+1) by omega,Nat.pow_add 2] at h
    exact (by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h)
  apply Nat.le_of_mul_le_mul_left (c:=3^k) _ (Nat.pow_pos (by decide))
  calc
    _ = 2^k*(2^(c+1)*v) := he
    _ ≤ 3^k*(2^(c+1)*v) := Nat.mul_le_mul_right _ hk
    _ ≤ 3^k*(2^(c+1)*(14*r)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hv)
    _ = _ := by rw [Nat.pow_succ]; change _ = 3^k*((2*14)*r*2^c); ac_rfl

/-- If two distinct positive numerators both have a high 3-adic divisor,
    their difference cannot be smaller than that divisor. The closeness
    bound upgrades the divisor into a lower bound for the denominator. -/
theorem close_pair {b c u v r : Nat} (hu : r<u) (hv : r<v) (hne : u≠v)
    (hdu : 3^b∣u) (hdv : 3^b∣v)
    (hcu : 3^c*(u-r)≤28*r*2^c) (hcv : 3^c*(v-r)≤28*r*2^c) :
    3^(b+c)≤28*r*2^c := by
  have step : ∀ U V : Nat, r<V → V<U → 3^b∣U → 3^b∣V →
      3^c*(U-r)≤28*r*2^c → 3^(b+c)≤28*r*2^c := by
    intro U V hV hUV hU hVd hC
    have hd : 3^b∣U-V := Nat.dvd_sub hU hVd
    have hle := Nat.le_of_dvd (show 0<U-V by omega) hd
    rw [Nat.pow_add]
    calc
      3^b*3^c ≤ (U-V)*3^c := Nat.mul_le_mul_right _ hle
      _ ≤ (U-r)*3^c := Nat.mul_le_mul_right _ (by omega)
      _ = 3^c*(U-r) := Nat.mul_comm _ _
      _ ≤ _ := hC
  by_cases h : u<v
  · exact step v u hu h hdv hdu hcv
  · exact step u v hv (by omega) hdu hdv hcu

#print axioms phase_bound
#print axioms numerator_dvd
#print axioms close_to_r
#print axioms close_pair

end BB6.Agent10BetaThreeBridge
