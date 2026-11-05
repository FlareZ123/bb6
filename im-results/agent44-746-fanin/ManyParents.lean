import ExactOdd
set_option maxHeartbeats 0
namespace CascadeAgent44
open CascadeResetInverse

/-- A 3-adic divisibility certificate gives at least M *distinct actual*
    first-return reset ancestors, each from a different odd valuation block.
    No assumption of blank-root reachability is made. -/
theorem many_distinct_reset_parents (u M : Nat)
    (hmod : (2*u+5)%3^(3*M+1)=0) :
    ∃ f : Fin M → Nat, Function.Injective f ∧
      ∀ j : Fin M, ResetParent (f j) u := by
  classical
  let t (j : Fin M) :=
    Classical.choose (every_three_odd_params u M hmod j.val j.isLt)
  have ht (j : Fin M) :
      3*j.val ≤ t j ∧ t j ≤ 3*j.val+2 ∧ OddParam u (t j) :=
    Classical.choose_spec (every_three_odd_params u M hmod j.val j.isLt)
  let f (j : Fin M) :=
    Classical.choose (odd_param_exact_parent u (t j) (ht j).2.2)
  have hf (j : Fin M) : OddParentAt u (f j) (t j) :=
    Classical.choose_spec (odd_param_exact_parent u (t j) (ht j).2.2)
  refine ⟨f,?_,?_⟩
  · intro a b heq
    have hb : OddParentAt u (f a) (t b) := by
      rw [heq]
      exact hf b
    have he := odd_parent_valuation_unique u (f a) (t a) (t b) (hf a) hb
    apply Fin.ext
    have ha := ht a
    have hb := ht b
    omega
  · intro j
    exact odd_parent_at_reset u (f j) (t j) (hf j)

#print axioms many_distinct_reset_parents
end CascadeAgent44
