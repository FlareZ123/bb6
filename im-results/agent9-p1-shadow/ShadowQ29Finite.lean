import Lean
namespace BB6.Shadow

def q29L0Nodes : List (Nat × Nat) :=
  [(0,352),(2,324),(4,259),(4,318),(5,278),(5,367),(6,377),(7,308),(7,427),(8,393),(9,436),(10,458)]

theorem q29L0_closed (m z t r zp : Nat)
 (hmem : (m,z) ∈ q29L0Nodes)
 (hdiv : z=2^t*r)
 (hnext : 2*zp+1=472+m+t+r) :
 (m+t+1,zp) ∈ q29L0Nodes := by
  have hbound : 0<z ∧ z≤463 := by
    simp only [q29L0Nodes, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hmem
    omega
  have hr : 0<r := by
    by_cases he:r=0
    · simp [he] at hdiv
      omega
    · omega
  have hp : 2^t≤z := by
    rw [hdiv]
    exact Nat.le_mul_of_pos_right _ hr
  have ht : t≤8 := by
    by_cases hh : t≤8
    · exact hh
    · have hpow : 2^9≤2^t := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7∨t=8 := by omega
  simp only [q29L0Nodes, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h|h <;> subst t <;> simp_all [q29L0Nodes] <;> omega

#print axioms q29L0_closed

def q29L1Nodes : List (Nat × Nat) :=
  [(0,294),(1,383),(2,310),(2,428),(3,392),(3,451),(4,315),(4,463),(5,336),(7,323),(8,401),(9,261),(10,251),(10,371)]

theorem q29L1_closed (m z t r zp : Nat)
 (hmem : (m,z) ∈ q29L1Nodes)
 (hdiv : z=2^t*r)
 (hnext : 2*zp+1=473+m+t+r) :
 (m+t+1,zp) ∈ q29L1Nodes := by
  have hbound : 0<z ∧ z≤463 := by
    simp only [q29L1Nodes, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hmem
    omega
  have hr : 0<r := by
    by_cases he:r=0
    · simp [he] at hdiv
      omega
    · omega
  have hp : 2^t≤z := by
    rw [hdiv]
    exact Nat.le_mul_of_pos_right _ hr
  have ht : t≤8 := by
    by_cases hh : t≤8
    · exact hh
    · have hpow : 2^9≤2^t := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hcases : t=0∨t=1∨t=2∨t=3∨t=4∨t=5∨t=6∨t=7∨t=8 := by omega
  simp only [q29L1Nodes, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨hm,hz⟩
  all_goals simp only [hm,hz] at hdiv hnext ⊢
  all_goals rcases hcases with h|h|h|h|h|h|h|h|h <;> subst t <;> simp_all [q29L1Nodes] <;> omega

#print axioms q29L1_closed

end BB6.Shadow
