import SheepEvenReachInverse

namespace SheepSourceFiniteInverseDAG

/-- A universal source-connected finite inverse-DAG proof rule. An actual
first-even Sheep return from any even x into nodes[i] must have a source
equal to nodes[j] for a strictly greater index j; the finite graph must
avoid the genuine blank-origin even seed 10. Then no target node is
blank-even reachable. This certifies arbitrary finite predecessor DAGs
once their all-parameter inverse completeness has been proved. -/
theorem no_blank_reach_of_finite_inverse_DAG
    (n : Nat) (node : Fin n → Nat)
    (hseed : ∀ i : Fin n, node i ≠ 10)
    (hparent : ∀ i : Fin n, ∀ x : Nat,
        x % 2 = 0 → SheepEven.EvenEdge x (node i) →
        ∃ j : Fin n, i.val < j.val ∧ x = node j) :
    ∀ i : Fin n, ¬ SheepEven.EvenReach 10 (node i) := by
  have aux : ∀ k : Nat, ∀ i : Fin n,
      n - i.val ≤ k → ¬ SheepEven.EvenReach 10 (node i) := by
    intro k
    induction k with
    | zero =>
      intro i hb _
      have hlt := i.isLt
      omega
    | succ k ih =>
      intro i hb hreach
      by_cases hsmall : n - i.val ≤ k
      · exact ih i hsmall hreach
      · have hne : 10 ≠ node i := Ne.symm (hseed i)
        obtain ⟨x, hx, he⟩ :=
          SheepEvenReachInverse.reach_last_edge hreach hne
        have hxeven : x % 2 = 0 :=
          SheepEvenReachInverse.even_reach_preserves_even hx (by decide)
        obtain ⟨j, hij, hnode⟩ := hparent i x hxeven he
        have hjlt := j.isLt
        have hindex : n - j.val ≤ k := by omega
        rw [hnode] at hx
        exact ih j hindex hx
  intro i hreach
  exact aux (n - i.val) i (Nat.le_refl _) hreach

#print axioms no_blank_reach_of_finite_inverse_DAG

end SheepSourceFiniteInverseDAG
