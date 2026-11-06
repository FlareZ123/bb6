import ValuationAllParents
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

theorem evenFullCandidates_length_eq (x y v u : Nat) :
    (evenFullCandidates x y v u).length =
      (evenHighExactCandidates x y v).length +
      (directExactCandidates x y).length +
      (zeroExactCandidates x y v u).length := by
  simp [evenFullCandidates,List.length_append,Nat.add_assoc]

theorem oddFullCandidates_length_eq (x y v u : Nat) :
    (oddFullCandidates x y v u).length =
      (oddHighExactCandidates x y v).length +
      (directExactCandidates x y).length +
      (oneExactCandidates x y v u).length := by
  simp [oddFullCandidates,List.length_append,Nat.add_assoc]

/-- The complete even-sum inverse list has at most floor(V/2)+1
entries. If both non-high branches occur, the parity theorem removes
one slot from the high list. -/
theorem evenFullCandidates_length_bound (x y v u : Nat)
    (hy : 5≤y) (hfact : x+y=2^v*(2*u+1)) :
    (evenFullCandidates x y v u).length≤v/2+1 := by
  rw [evenFullCandidates_length_eq]
  by_cases hd : directExactCandidates x y = []
  · have hdlen : (directExactCandidates x y).length=0 := by simp [hd]
    have hhigh := evenHighExactCandidates_length x y v
    have hextra := zeroExactCandidates_length x y v u
    omega
  · by_cases hz : zeroExactCandidates x y v u = []
    · have hzlen : (zeroExactCandidates x y v u).length=0 := by simp [hz]
      have hhigh := evenHighExactCandidates_length x y v
      have hextra := directExactCandidates_length x y
      omega
    · obtain ⟨hv,hx,hv3⟩ :=
        zero_exception_direct_parity x y v u hy hfact hd hz
      have hhigh := evenHighExactCandidates_length_sharp x y v hv hx
      have hdir := directExactCandidates_length x y
      have hextra := zeroExactCandidates_length x y v u
      omega

/-- The complete odd-sum inverse list has at most floor(V/2)+1
entries, with the same one-slot saving when direct and exceptional
parents coexist. -/
theorem oddFullCandidates_length_bound (x y v u : Nat)
    (hy : 5≤y) (hfact : x+y+1=2^v*(2*u+1)) :
    (oddFullCandidates x y v u).length≤v/2+1 := by
  rw [oddFullCandidates_length_eq]
  by_cases hd : directExactCandidates x y = []
  · have hdlen : (directExactCandidates x y).length=0 := by simp [hd]
    have hhigh := oddHighExactCandidates_length x y v
    have hextra := oneExactCandidates_length x y v u
    omega
  · by_cases ho : oneExactCandidates x y v u = []
    · have holen : (oneExactCandidates x y v u).length=0 := by simp [ho]
      have hhigh := oddHighExactCandidates_length x y v
      have hextra := directExactCandidates_length x y
      omega
    · obtain ⟨hv,hx,hv4⟩ :=
        one_exception_direct_parity x y v u hy hfact hd ho
      have hhigh := oddHighExactCandidates_length_sharp x y v hv hx
      have hdir := directExactCandidates_length x y
      have hextra := oneExactCandidates_length x y v u
      omega

/-- Any finite collection of distinct even-sum immediate section
predecessors has cardinality at most floor(V/2)+1. -/
theorem even_preimage_degree_bound (x y v u : Nat)
    (hy : 5≤y) (hS : (x+y)%2=0)
    (hfact : x+y=2^v*(2*u+1))
    (ps : List (Nat × Nat)) (hnd : ps.Nodup)
    (hps : ∀ p∈ps, secNext p=some (x,y)) :
    ps.length≤v/2+1 := by
  have hsub : ps ⊆ evenFullCandidates x y v u := by
    intro p hp
    cases p with
    | mk a k =>
      exact even_sum_parent_mem_fullCandidates a k x y v u hy hS hfact
        (hps (a,k) hp)
  exact Nat.le_trans (hnd.length_le_of_subset hsub)
    (evenFullCandidates_length_bound x y v u hy hfact)

/-- Any finite collection of distinct odd-sum immediate section
predecessors has cardinality at most floor(V/2)+1. -/
theorem odd_preimage_degree_bound (x y v u : Nat)
    (hy : 5≤y) (hS : (x+y)%2=1)
    (hfact : x+y+1=2^v*(2*u+1))
    (ps : List (Nat × Nat)) (hnd : ps.Nodup)
    (hps : ∀ p∈ps, secNext p=some (x,y)) :
    ps.length≤v/2+1 := by
  have hsub : ps ⊆ oddFullCandidates x y v u := by
    intro p hp
    cases p with
    | mk a k =>
      exact odd_sum_parent_mem_fullCandidates a k x y v u hy hS hfact
        (hps (a,k) hp)
  exact Nat.le_trans (hnd.length_le_of_subset hsub)
    (oddFullCandidates_length_bound x y v u hy hfact)

#print axioms even_preimage_degree_bound
#print axioms odd_preimage_degree_bound

end BB6.Agent34Valuation
