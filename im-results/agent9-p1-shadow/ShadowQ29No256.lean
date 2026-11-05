import ShadowQ29Finite
namespace BB6.Shadow

theorem q29L0_no_256 (m z : Nat)
    (hmem : (m,z) ∈ q29L0Nodes) : ¬ 256 ∣ z := by
  simp only [q29L0Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  omega

theorem q29L1_no_256 (m z : Nat)
    (hmem : (m,z) ∈ q29L1Nodes) : ¬ 256 ∣ z := by
  simp only [q29L1Nodes,List.mem_cons,List.not_mem_nil,Prod.mk.injEq,or_false] at hmem
  omega

#print axioms q29L0_no_256
#print axioms q29L1_no_256
end BB6.Shadow
