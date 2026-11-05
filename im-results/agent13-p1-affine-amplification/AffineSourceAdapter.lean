import FiniteToCylinder
import ShadowGraphBridge

namespace BB6.Agent13Affine

theorem source_shadow_to_affine (q side zroot m z : Nat)
    (h : BB6.Shadow.ShadowReach (16*q+side) zroot m z) :
    ShadowReach q side 0 zroot m z := by
  induction h with
  | root => exact ShadowReach.root
  | step m z t v zp h hd hn ih =>
      exact ShadowReach.step ih ⟨t,v,hd,rfl,by omega⟩

theorem affine_shadow_to_source (q side zroot m z : Nat)
    (h : ShadowReach q side 0 zroot m z) :
    BB6.Shadow.ShadowReach (16*q+side) zroot m z := by
  induction h with
  | root => exact BB6.Shadow.ShadowReach.root
  | @step mx zx my zy hprev hedge ih =>
      obtain ⟨t,v,hin,hmy,hout⟩ := hedge
      have hh := BB6.Shadow.ShadowReach.step mx zx t v zy ih hin
        (by omega : 2*zy+1=(16*q+side)+mx+t+v)
      simpa only [hmy] using hh

/-- The finite-to-infinite theorem applies *verbatim* to the unchanged
    source Agent9 ShadowReach, not only the new abstract isomorphic graph. -/
theorem source_shadow_finite_lift
    (q side zroot rootSlope M K delta : Nat)
    (hdelta : delta=2^(M+K+1))
    (hrootSlope : delta ∣ rootSlope)
    (hbase : ∀ m z,
      BB6.Shadow.ShadowReach (16*q+side) zroot m z →
      m≤M ∧ 0<z ∧ z<2^K)
    (r m z : Nat)
    (hreach : BB6.Shadow.ShadowReach
      (16*(q+delta*r)+side) (zroot+rootSlope*r) m z) :
    m≤M ∧ ∃ zb slope,
      BB6.Shadow.ShadowReach (16*q+side) zroot m zb ∧
      z=zb+slope*r ∧ 2^(M+K+1-m)∣slope := by
  have hbase' : ∀ m z, ShadowReach q side 0 zroot m z →
       m≤M ∧ 0<z ∧ z<2^K := by
    intro m z ha
    exact hbase m z (affine_shadow_to_source q side zroot m z ha)
  have ha : ShadowReach (q+delta*r) side 0
      (zroot+rootSlope*r) m z :=
    source_shadow_to_affine (q+delta*r) side
      (zroot+rootSlope*r) m z hreach
  obtain ⟨hm,zb,slope,hbr,hz,hdiv⟩ :=
    finite_base_amplifies q side 0 zroot rootSlope M K delta
      hdelta hrootSlope hbase' r m z ha
  exact ⟨hm,zb,slope,affine_shadow_to_source q side zroot m zb hbr,hz,hdiv⟩

#print axioms source_shadow_finite_lift
end BB6.Agent13Affine
