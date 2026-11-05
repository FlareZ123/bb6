import AffineSourceList
import P130Arithmetic

namespace BB6.Agent13Affine
open BB6.Agent13P130

private theorem l0_base_bounds (m z : Nat) (h : (m,z)∈l0Nodes 0) :
    m≤10 ∧ 0<z ∧ z<512 := by
  have hm := l0_small 0 m z h
  have hz := l0_positive 0 m z h
  have hu : z<512 := by
    simp [l0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq] at h
    omega
  exact ⟨hm,hz,hu⟩

private theorem l1_base_bounds (m z : Nat) (h : (m,z)∈l1Nodes 0) :
    m≤10 ∧ 0<z ∧ z<512 := by
  have hm := l1_small 0 m z h
  have hz := l1_positive 0 m z h
  have hu : z<512 := by
    simp [l1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq] at h
    omega
  exact ⟨hm,hz,hu⟩

/-- Explicit source-certified finite-base-to-infinite cylinder:
    every original Agent9 L0 shadow graph at q=30+2^20*r has cost ≤10. -/
theorem q30_l0_original_shadow_amplified (r m z : Nat)
    (hr : BB6.Shadow.ShadowReach
      (16*(30+2^20*r)+8) (364+12*2^20*r) m z) : m≤10 := by
  have hroot : (0,364)∈l0Nodes 0 := by decide
  have hc : ∀ m z t v zp, (m,z)∈l0Nodes 0 →
      z=2^t*v → 2*zp+1=16*30+8+m+t+v →
      (m+t+1,zp)∈l0Nodes 0 := by
    intro m z t v zp hmem hd hn
    exact l0_closed 0 m z t v zp hmem hd (by simpa using hn)
  have hs : 2^(10+9+1) ∣ 12*2^20 := by decide
  exact (finite_list_source_amplifies 30 8 364 (12*2^20) 10 9
    (l0Nodes 0) hroot l0_base_bounds hc hs r m z hr).1

/-- Explicit source-certified finite-base-to-infinite cylinder:
    every original Agent9 L1 shadow graph at q=30+2^20*r has cost ≤10. -/
theorem q30_l1_original_shadow_amplified (r m z : Nat)
    (hr : BB6.Shadow.ShadowReach
      (16*(30+2^20*r)+9) (304+10*2^20*r) m z) : m≤10 := by
  have hroot : (0,304)∈l1Nodes 0 := by decide
  have hc : ∀ m z t v zp, (m,z)∈l1Nodes 0 →
      z=2^t*v → 2*zp+1=16*30+9+m+t+v →
      (m+t+1,zp)∈l1Nodes 0 := by
    intro m z t v zp hmem hd hn
    exact l1_closed 0 m z t v zp hmem hd (by simpa using hn)
  have hs : 2^(10+9+1) ∣ 10*2^20 := by decide
  exact (finite_list_source_amplifies 30 9 304 (10*2^20) 10 9
    (l1Nodes 0) hroot l1_base_bounds hc hs r m z hr).1

#print axioms q30_l0_original_shadow_amplified
#print axioms q30_l1_original_shadow_amplified
end BB6.Agent13Affine
