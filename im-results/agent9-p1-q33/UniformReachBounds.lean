import UniformPrecisionPath
namespace BB6.Precision

/-- The abstract all-path precision theorem implies both a uniform
    inverse-cost bound and a dyadic nondivisibility bound for every path
    of a high-precision perturbed feeder. -/
theorem uniform_reach_bounds (K M L0 zbase r c : Nat)
    (S : Nat → Nat → Prop)
    (hroot : S 0 zbase)
    (hsmall : ∀ m z, S m z → m≤M)
    (hnodiv : ∀ m z, S m z → ¬2^K ∣ z)
    (hclosed : ∀ m z t v zp, S m z → z=2^t*v →
        2*zp+1=L0+m+t+v → S (m+t+1) zp)
    (m z : Nat)
    (hpath : ShadowReach (L0+16*2^(K+M)*r)
              (zbase+2^(K+M)*(c*r)) m z) :
    m≤M ∧ ¬2^K ∣ z := by
  obtain ⟨z0,s,hs,heq⟩ :=
    uniform_shadow_lift K M L0 zbase r c S
      hroot hsmall hnodiv hclosed m z hpath
  have hm : m≤M := hsmall m z0 hs
  refine ⟨hm, ?_⟩
  intro hz
  have he : K≤K+M-m := by omega
  have hshift : 2^K ∣ 2^(K+M-m)*s := by
    rcases Nat.pow_dvd_pow 2 he with ⟨u,hu⟩
    refine ⟨u*s, ?_⟩
    rw [hu]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hsum : 2^K ∣ z0+2^(K+M-m)*s := by
    rw [←heq]
    exact hz
  exact hnodiv m z0 hs ((Nat.dvd_add_iff_left hshift).mpr hsum)

#print axioms uniform_reach_bounds
end BB6.Precision
