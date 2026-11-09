import HeapBridge
namespace BB6.Agent9Heaps

inductive HeapPath : Nat×Nat → Nat×Nat → Prop where
  | refl (x : Nat×Nat) : HeapPath x x
  | step {x y z : Nat×Nat} : HeapPath x y → HeapEdge y z → HeapPath x z

/-- Every unequal node has a legal parent whose pile sum is one smaller. -/
theorem legal_parent (u e : Nat) (hne : u ≠ e) :
    ∃ x : Nat×Nat, HeapEdge x (u,e) ∧ x.1+x.2+1=u+e := by
  by_cases hu : u<e
  · refine ⟨(2*u,e-u-1), ?_, ?_⟩
    · change (2*u)%2=0 ∧ (u,e)=moveL (2*u) (e-u-1) ∨
        (e-u-1)%2=0 ∧ (u,e)=moveR (2*u) (e-u-1)
      left
      constructor
      · omega
      · simp [moveL,Prod.mk.injEq]
        omega
    · simp
      omega
  · have he : e<u := by omega
    refine ⟨(u-e-1,2*e), ?_, ?_⟩
    · change (u-e-1)%2=0 ∧ (u,e)=moveL (u-e-1) (2*e) ∨
        (2*e)%2=0 ∧ (u,e)=moveR (u-e-1) (2*e)
      right
      constructor
      · omega
      · simp [moveR,Prod.mk.injEq]
        omega
    · simp
      omega

/-- Every natural-number heap pair has a finite, strictly sum-decreasing
    unique-predecessor chain back to a diagonal node. -/
theorem diagonal_ancestor (u e : Nat) :
    ∃ a : Nat, HeapPath (a,a) (u,e) := by
  have hmain : ∀ n u e, u+e=n → ∃ a : Nat, HeapPath (a,a) (u,e) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro u e hn
      by_cases heq : u=e
      · subst e
        exact ⟨u, HeapPath.refl (u,u)⟩
      · obtain ⟨⟨a,b⟩,hedge,hcost⟩ := legal_parent u e heq
        have hless : a+b<n := by omega
        obtain ⟨r, hpath⟩ := ih (a+b) hless a b rfl
        exact ⟨r, HeapPath.step hpath hedge⟩
  exact hmain (u+e) u e rfl

/-- Diagonal ancestors are unique: all transfer paths from root to a
    destination agree on their diagonal origin. -/
theorem diagonal_ancestor_unique (a b : Nat) (z : Nat×Nat)
    (pa : HeapPath (a,a) z) (pb : HeapPath (b,b) z) : a=b := by
  induction pa generalizing b with
  | refl =>
      cases pb with
      | refl => rfl
      | step p edge =>
          exact False.elim ((diagonal_no_predecessor a _) edge)
  | step p edge ih =>
      cases pb with
      | refl =>
          exact False.elim ((diagonal_no_predecessor b _) edge)
      | step p' edge' =>
          have hprev := heap_edge_predecessor_unique _ _ _ edge edge'
          subst_vars
          exact ih _ p'

#print axioms diagonal_ancestor_unique

#print axioms legal_parent
#print axioms diagonal_ancestor
end BB6.Agent9Heaps
