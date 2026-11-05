import AffineGraphTheorem
namespace BB6.Agent13Affine

/-- Uniform finite-cone amplification: a bound M on the entire base-q
    shadow orbit, with its positive coordinates bounded by 2^K, also bounds
    the orbit of every q+2^(M+K+1)*r under a compatible affine root shift. -/
theorem finite_base_amplifies
    (q side m0 zroot rootSlope M K : Nat)
    (delta : Nat)
    (hdelta : delta=2^(M+K+1))
    (hrootslope : delta ∣ rootSlope)
    (hbase : ∀ m z, ShadowReach q side m0 zroot m z →
       m≤M ∧ 0<z ∧ z<2^K)
    (r m z : Nat)
    (hreach : ShadowReach (q+delta*r) side m0
      (zroot+rootSlope*r) m z) :
    m≤M ∧ ∃ zb slope,
      ShadowReach q side m0 zroot m zb ∧
      z=zb+slope*r ∧ 2^(M+K+1-m) ∣ slope := by
  let D := M+K+1
  induction hreach with
  | root =>
    have hr : ShadowReach q side m0 zroot m0 zroot := .root
    have hm : m0≤M := (hbase m0 zroot hr).1
    have hpow : 2^(D-m0) ∣ delta := by
      rw [hdelta]
      exact Nat.pow_dvd_pow 2 (by dsimp [D]; omega)
    have hrootdiv : 2^(D-m0) ∣ rootSlope :=
      Nat.dvd_trans hpow hrootslope
    exact ⟨hm, zroot,rootSlope,hr,rfl,by simpa [D] using hrootdiv⟩
  | @step mx zx my zy hprev hedge ih =>
    obtain ⟨hm,zb,slope,hbaseReach,hz,hdiv⟩ := ih
    obtain ⟨t,v,hin,hmy,hout⟩ := hedge
    obtain ⟨_,hzpos,hzsmall⟩ := hbase mx zb hbaseReach
    have hK : 2^K ∣ slope := by
      have hle : K≤D-mx := by dsimp [D]; omega
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hle) (by simpa [D] using hdiv)
    have hin' : zb+slope*r=2^t*v := by rw [hz] at hin; exact hin
    have hout' : 2*zy+1=16*(q+delta*r)+side+mx+t+v := by simpa using hout
    obtain ⟨v0,a,z0,hzin,hsin,hv,hbaseOut,hzout⟩ :=
      lifted_step_decompose K q delta side mx zb slope r t v zy
        hzpos hzsmall hK hin' hout'
    have hbaseNext : ShadowReach q side m0 zroot my z0 := by
      apply ShadowReach.step hbaseReach
      exact ⟨t,v0,hzin,hmy,hbaseOut⟩
    have hmnext : my≤M := (hbase my z0 hbaseNext).1
    have hExp : D-mx=(t+1)+(D-my) := by
      dsimp [D]
      omega
    obtain ⟨factor,hfactor⟩ := (show 2^(D-mx)∣slope from by simpa [D] using hdiv)
    have hcancel : a=2^(D-my)*factor := by
      have hp : 0<(2:Nat)^(t+1) := Nat.pow_pos (by decide)
      have hc : 2^(t+1)*a=2^(t+1)*(2^(D-my)*factor) := by
        calc
          2^(t+1)*a=slope := hsin.symm
          _=2^(D-mx)*factor := hfactor
          _=2^(t+1)*(2^(D-my)*factor) := by
            rw [hExp, Nat.pow_add]
            ac_rfl
      exact Nat.mul_left_cancel hp hc
    have hdeltaDiv : 2^(D-my) ∣ delta := by
      rw [hdelta]
      exact Nat.pow_dvd_pow 2 (by dsimp [D]; omega)
    obtain ⟨dfac,hdfac⟩ := hdeltaDiv
    have hnextDiv : 2^(D-my) ∣ 8*delta+a := by
      refine ⟨8*dfac+factor, ?_⟩
      rw [hdfac,hcancel]
      simp only [Nat.mul_add]
      ac_rfl
    exact ⟨hmnext,z0,8*delta+a,hbaseNext,hzout,by simpa [D] using hnextDiv⟩

#print axioms finite_base_amplifies
end BB6.Agent13Affine
