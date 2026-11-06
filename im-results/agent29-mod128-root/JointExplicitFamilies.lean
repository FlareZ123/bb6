import JointNonredundant
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Joint

theorem four_new_high_progressions (n : Nat) :
  newHighClass (109+24*n) (4+8*n) ∧
  newHighClass (17+96*n) (16+32*n) ∧
  newHighClass (121+192*n) (8+64*n) ∧
  newHighClass (3+288*n) (6+32*n) := by
  dsimp [newHighClass]
  omega

theorem four_progressions_prior_allowed (n : Nat) :
  BB6.Agent19Joint.highAllowed (109+24*n) (4+8*n) ∧
  BB6.Agent19Joint.highAllowed (17+96*n) (16+32*n) ∧
  BB6.Agent19Joint.highAllowed (121+192*n) (8+64*n) ∧
  BB6.Agent19Joint.highAllowed (3+288*n) (6+32*n) := by
  obtain ⟨h1,h2,h3,h4⟩ := four_new_high_progressions n
  exact ⟨new_high_class_previously_allowed _ _ h1,
    new_high_class_previously_allowed _ _ h2,
    new_high_class_previously_allowed _ _ h3,
    new_high_class_previously_allowed _ _ h4⟩

#print axioms four_new_high_progressions
#print axioms four_progressions_prior_allowed
end BB6.Agent29Joint
