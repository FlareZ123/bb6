import Parents
import ResetChain

namespace CascadeResetInverse

/-- Decidable exact reset reachability using a complete predecessor list and
    the strict decreasing reset-parent ranking. The explicit comparison
    provides Lean's checked well-founded termination argument. -/
def rootReachBool (u:Nat) : Bool :=
  if u=2 then true else (parents u).any (fun h => if h<u then rootReachBool h else false)
termination_by u
decreasing_by
  omega

/-- Each instance of the exact six-state #746 source-C reset-reachability
    problem is decided by the terminating first-return reverse search. -/
theorem rootReachBool_iff (u:Nat) :
    rootReachBool u=true ↔ ResetChain 2 u := by
  induction u using Nat.strongRecOn with
  | ind u ih =>
    by_cases hu : u=2
    · subst u
      constructor
      · intro _; exact ResetChain.root
      · intro _; rw [rootReachBool.eq_1]; simp
    · have heq : rootReachBool u =
        (parents u).any (fun h => if h<u then rootReachBool h else false) := by
        rw [rootReachBool.eq_1]; simp [hu]
      rw [heq]
      constructor
      · intro hh
        obtain ⟨h,hm,hyes⟩ := List.any_eq_true.mp hh
        have hlt : h<u := parents_strict h u hm
        simp only [if_pos hlt] at hyes
        have hr : ResetChain 2 h := (ih h hlt).mp hyes
        exact ResetChain.append hr ((parents_iff h u).mp hm)
      · intro hr
        cases hr with
        | root => exact False.elim (hu rfl)
        | @append h u' hr hp =>
            have hm : h∈parents u := (parents_iff h u).mpr hp
            have hlt : h<u := parents_strict h u hm
            apply List.any_eq_true.mpr
            refine ⟨h,hm,?_⟩
            simp [hlt,(ih h hlt).mpr hr]

/-- Total terminating executable decision procedure for any fixed #746
    source-C blank-root reset target. Its result is exactly equivalent to
    mathematical reachability in the complete source-Cstep semantics. -/
theorem rootReachBool_source_iff (u:Nat) :
  rootReachBool u=true ↔ CascadeSweep.ReachC (2,0) (u,0) :=
  (rootReachBool_iff u).trans (root_reset_chain_iff u).symm

#print axioms rootReachBool_iff
#print axioms rootReachBool_source_iff
end CascadeResetInverse
