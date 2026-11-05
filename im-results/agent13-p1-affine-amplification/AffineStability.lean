import Lean
namespace BB6.Agent13Affine

/-- A finite base shadow coordinate retains its bounded 2-adic depth
    after any shift by a multiple of 2^K. -/
theorem lifted_depth_lt
    (K z slope r t v : Nat)
    (hz : 0 < z) (hzsmall : z < 2^K)
    (hslope : 2^K ∣ slope)
    (hstep : z + slope*r = 2^t*v) : t < K := by
  by_cases hlt : t < K
  · exact hlt
  have hkt : K ≤ t := by omega
  have hpow : 2^K ∣ 2^t := Nat.pow_dvd_pow 2 hkt
  have hstepdiv : 2^K ∣ z + slope*r := by
    rw [hstep]
    rcases hpow with ⟨w,hw⟩
    refine ⟨w*v, ?_⟩
    rw [hw]
    ac_rfl
  have hslopeDiv : 2^K ∣ slope*r := by
    rcases hslope with ⟨w,hw⟩
    refine ⟨w*r, ?_⟩
    rw [hw]
    ac_rfl
  have hzdiv : 2^K ∣ z :=
    (Nat.dvd_add_iff_left hslopeDiv).mpr hstepdiv
  have hbound := Nat.le_of_dvd hz hzdiv
  omega

theorem lifted_base_divides
    (K z slope r t v : Nat)
    (ht : t ≤ K)
    (hslope : 2^K ∣ slope)
    (hstep : z + slope*r = 2^t*v) : 2^t ∣ z := by
  have hpow : 2^t ∣ 2^K := Nat.pow_dvd_pow 2 ht
  have hdivSlope : 2^t ∣ slope := by
    rcases hpow with ⟨w,hw⟩
    rcases hslope with ⟨u,hu⟩
    refine ⟨w*u, ?_⟩
    rw [hu,hw]
    ac_rfl
  have hdivSlopeR : 2^t ∣ slope*r := by
    rcases hdivSlope with ⟨u,hu⟩
    refine ⟨u*r, ?_⟩
    rw [hu]
    ac_rfl
  apply (Nat.dvd_add_iff_left hdivSlopeR).mpr
  rw [hstep]
  exact Nat.dvd_mul_right _ _

theorem lifted_quotient
    (z slope r t v v0 vs : Nat)
    (hbase : z=2^t*v0)
    (hslope : slope=2^t*vs)
    (hstep : z+slope*r=2^t*v) : v=v0+vs*r := by
  have hpow : 0<(2:Nat)^t := Nat.pow_pos (by decide)
  have h : 2^t*v = 2^t*(v0+vs*r) := by
    rw [←hstep, hbase, hslope]
    simp only [Nat.mul_add]
    ac_rfl
  exact Nat.mul_left_cancel hpow h

/-- Every true lifted inverse edge has an authentic base inverse edge.
    Its residual offset is *exactly affine*, with an integer slope. -/
theorem lifted_step_decompose
    (K q delta side m z slope r t v zp : Nat)
    (hz : 0 < z) (hzsmall : z < 2^K)
    (hslope : 2^K ∣ slope)
    (hinput : z + slope*r = 2^t*v)
    (houtput : 2*zp+1 = 16*(q+delta*r)+side+m+t+v) :
    ∃ v0 a zp0,
      z = 2^t*v0 ∧
      slope = 2^(t+1)*a ∧
      v = v0+2*a*r ∧
      2*zp0+1=16*q+side+m+t+v0 ∧
      zp=zp0+(8*delta+a)*r := by
  have ht : t<K := lifted_depth_lt K z slope r t v hz hzsmall hslope hinput
  have hdivSlope : 2^(t+1)∣slope :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hslope
  obtain ⟨a,ha⟩ := hdivSlope
  have hdivBase : 2^t ∣ z :=
    lifted_base_divides K z slope r t v (by omega) hslope hinput
  obtain ⟨v0,hz0⟩ := hdivBase
  have hslope0 : slope=2^t*(2*a) := by
    rw [ha,Nat.pow_succ]
    ac_rfl
  have hv : v = v0+2*a*r :=
    lifted_quotient z slope r t v v0 (2*a) hz0 hslope0 hinput
  have hraw : 2*zp+1=(16*q+side+m+t+v0)+2*((8*delta+a)*r) := by
    rw [hv] at houtput
    calc
      2*zp+1 = 16*(q+delta*r)+side+m+t+(v0+2*a*r) := houtput
      _ = (16*q+side+m+t+v0)+2*((8*delta+a)*r) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
  let deltaZ := (8*delta+a)*r
  have hlower : deltaZ≤zp := by
    dsimp [deltaZ]
    omega
  let zp0 := zp-deltaZ
  have hzp : zp=zp0+deltaZ := by dsimp [zp0]; omega
  have hbase : 2*zp0+1=16*q+side+m+t+v0 := by
    dsimp [zp0]
    omega
  exact ⟨v0,a,zp0,hz0,ha,hv,hbase,by simpa [deltaZ] using hzp⟩

#print axioms lifted_step_decompose
#print axioms lifted_depth_lt
#print axioms lifted_base_divides
#print axioms lifted_quotient
end BB6.Agent13Affine
