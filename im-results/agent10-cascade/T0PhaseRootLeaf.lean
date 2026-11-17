import ResetChain

namespace CascadeResetInverse
open CascadeSource CascadeSweep

/-- A target with no ResetParent cannot be reached from the genuine blank root. -/
theorem no_root_reach_of_parentless {e : Nat}
    (he : e ≠ 2)
    (hleaf : ∀ p, ¬ ResetParent p e) :
    ¬ ReachC (2,0) (e,0) := by
  intro hreach
  have hc : ResetChain 2 e := (root_reset_chain_iff e).mp hreach
  cases hc with
  | root =>
      exact he rfl
  | append hr hp =>
      exact hleaf _ hp

/-- If a target has one parent and that parent is itself parentless, the
    target cannot occur on a finite reset-parent chain from blank root 2. -/
theorem no_root_reach_of_unique_parent_leaf {e h : Nat}
    (he : e ≠ 2)
    (hh : h ≠ 2)
    (hunique : ∀ p, ResetParent p e → p = h)
    (hleaf : ∀ p, ¬ ResetParent p h) :
    ¬ ReachC (2,0) (e,0) := by
  intro hreach
  have hc : ResetChain 2 e := (root_reset_chain_iff e).mp hreach
  cases hc with
  | root =>
      exact he rfl
  | append hchain hparent =>
      have hparentEq : _ = h := hunique _ hparent
      rw [hparentEq] at hchain
      cases hchain with
      | root =>
          exact hh rfl
      | append hprior hpriorParent =>
          exact hleaf _ hpriorParent

#print axioms no_root_reach_of_parentless
#print axioms no_root_reach_of_unique_parent_leaf

end CascadeResetInverse
