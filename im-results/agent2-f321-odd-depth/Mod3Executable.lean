import SourceHaltingBridge
import Mod3Source
import Lean.Elab.Tactic.Omega

/-!
Direct Option-valued F321 sourceNext consumer of the proved second-counter
mod-3 invariant. This is the existing executable source-counter semantics,
not a new finite simulator or a complete original six-state-machine proof.
-/

namespace BB6.Agent2F321Mod3
open BB6.Agent31F321Density

theorem sourceNext_nonzero_mod3
    {a d A D:Nat}
    (hs:sourceNext a d=some (A,D))
    (hd:d%3≠0) : D%3≠0 :=
  counter_nonzero_mod3_preserved (move_of_sourceNext_some hs) hd

theorem next_reach_nonzero_mod3
    {n a d:Nat}
    (hr:NextReach 1 1 n a d) : d%3≠0 :=
  source_orbit_nonzero_mod3 (next_reach_to_counter hr)

/-- The executable option-valued source map cannot reach a halting
terminal with second counter divisible by three. -/
theorem no_source_halt_multiple_three (k:Nat) :
    ∀ n, ¬(NextReach 1 1 n (3*k+1) (3*k) ∧
             sourceNext (3*k+1) (3*k)=none) := by
  intro n h
  have hd:=next_reach_nonzero_mod3 h.1
  omega

#print axioms sourceNext_nonzero_mod3
#print axioms next_reach_nonzero_mod3
#print axioms no_source_halt_multiple_three

end BB6.Agent2F321Mod3
