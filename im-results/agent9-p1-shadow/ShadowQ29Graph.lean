import ShadowGraphBridge
import ShadowQ29Finite
import ShadowGraphFeeders

namespace BB6.Shadow

theorem q29_l0_reachable_in_nodes (m z : Nat)
    (h : ShadowReach 472 352 m z) :
    (m,z) ∈ q29L0Nodes := by
  induction h with
  | root => decide
  | step m z t r zp hp hd hn ih =>
      exact q29L0_closed m z t r zp ih hd hn

theorem q29_l1_reachable_in_nodes (m z : Nat)
    (h : ShadowReach 473 294 m z) :
    (m,z) ∈ q29L1Nodes := by
  induction h with
  | root => decide
  | step m z t r zp hp hd hn ih =>
      exact q29L1_closed m z t r zp ih hd hn

theorem q29_l0_max_cost (m z : Nat)
    (h : ShadowReach 472 352 m z) : m ≤ 10 := by
  have hm := q29_l0_reachable_in_nodes m z h
  simp only [q29L0Nodes, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm
  omega

theorem q29_l1_max_cost (m z : Nat)
    (h : ShadowReach 473 294 m z) : m ≤ 10 := by
  have hm := q29_l1_reachable_in_nodes m z h
  simp only [q29L1Nodes, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm
  omega

theorem q29_l0_bounded_authentic_cost
    (u b d m : Nat)
    (hu : u+4*29+3=7*2^(16*29))
    (hu1 : 1≤u)
    (hcone : BB6.Agent1Quarter.OddCone (4*u-4) (4*u+9) b d m)
    (hmod : b%4=0) (hcost : m+2≤16*29) : m≤10 := by
  obtain ⟨w,z,alpha,hgraph,_,_,_,_⟩ :=
    bounded_l0_cone_in_shadow_graph 29 u b d m hu hu1 hcone hmod hcost
  exact q29_l0_max_cost m z (by simpa using hgraph)

theorem q29_l1_bounded_authentic_cost
    (u b d m : Nat)
    (hu : u+4*29+3=7*2^(16*29))
    (hu1 : 1≤u)
    (hcone : BB6.Agent1Quarter.OddCone (6*u-2) (2*u+5) b d m)
    (hmod : b%4=0) (hcost : m+2≤16*29) : m≤10 := by
  obtain ⟨w,z,alpha,hgraph,_,_,_,_⟩ :=
    bounded_l1_cone_in_shadow_graph 29 u b d m hu hu1 hcone hmod hcost
  exact q29_l1_max_cost m z (by simpa using hgraph)

#print axioms q29_l0_max_cost
#print axioms q29_l1_max_cost
#print axioms q29_l0_bounded_authentic_cost
#print axioms q29_l1_bounded_authentic_cost
end BB6.Shadow
