import BB429OddExcursion
import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

namespace BB429SourceRows
open BB6Coverage BB429PhysicalFrontier BB429OddExcursion

/-- Twelve-slot, kernel-checked row correspondence between the original
    repository physical #429 machine and the zipper simulator.
    This is transition-table correspondence, not yet a raw-run bridge. -/
theorem action_matches_target (state : Fin 6) (symbol : Bool) :
    action state.val symbol =
      (target429 (state,symbol)).map
        (fun move => (move.next.val,move.write,move.right)) := by
  obtain ⟨q,hq⟩ := state
  have hq' : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq' with h0|h1|h2|h3|h4|h5 <;>
    subst q <;> cases symbol <;> decide +revert

#print axioms action_matches_target
end BB429SourceRows
