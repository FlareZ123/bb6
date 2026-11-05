import AffineSourceAdapter
namespace BB6.Agent13Affine

/-- A finite exact shadow graph at one parameter gives a completely proved
    all-time bound. This is a generic base-certificate interface. -/
theorem base_list_bounded
    (q side zroot M K : Nat) (nodes : List (Nat × Nat))
    (hroot : (0,zroot)∈nodes)
    (hnodes : ∀ m z, (m,z)∈nodes → m≤M ∧ 0<z ∧ z<2^K)
    (hclosed : ∀ m z t v zp, (m,z)∈nodes →
       z=2^t*v → 2*zp+1=16*q+side+m+t+v →
       (m+t+1,zp)∈nodes)
    (m z : Nat)
    (hreach : BB6.Shadow.ShadowReach (16*q+side) zroot m z) :
    m≤M ∧ 0<z ∧ z<2^K := by
  have hmember : ∀ m z, BB6.Shadow.ShadowReach (16*q+side) zroot m z →
      (m,z)∈nodes := by
    intro m z hr
    induction hr with
    | root => exact hroot
    | step mp zp t v znext h hd hn ih =>
      exact hclosed mp zp t v znext ih hd (by omega)
  exact hnodes m z (hmember m z hreach)

/-- One completely finite source ShadowReach certificate suffices for
    a whole infinite arithmetic progression of parameters. -/
theorem finite_list_source_amplifies
    (q side zroot rootSlope M K : Nat)
    (nodes : List (Nat × Nat))
    (hroot : (0,zroot)∈nodes)
    (hnodes : ∀ m z, (m,z)∈nodes → m≤M ∧ 0<z ∧ z<2^K)
    (hclosed : ∀ m z t v zp, (m,z)∈nodes →
       z=2^t*v → 2*zp+1=16*q+side+m+t+v →
       (m+t+1,zp)∈nodes)
    (hrootSlope : 2^(M+K+1) ∣ rootSlope)
    (r m z : Nat)
    (hreach : BB6.Shadow.ShadowReach
       (16*(q+2^(M+K+1)*r)+side) (zroot+rootSlope*r) m z) :
    m≤M ∧ ∃ zb slope,
       BB6.Shadow.ShadowReach (16*q+side) zroot m zb ∧
       z=zb+slope*r ∧ 2^(M+K+1-m) ∣ slope := by
  exact source_shadow_finite_lift q side zroot rootSlope M K
      (2^(M+K+1)) rfl hrootSlope
      (base_list_bounded q side zroot M K nodes hroot hnodes hclosed)
      r m z hreach

#print axioms base_list_bounded
#print axioms finite_list_source_amplifies
end BB6.Agent13Affine
