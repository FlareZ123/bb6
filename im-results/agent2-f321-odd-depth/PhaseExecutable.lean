import SourceHaltingBridge
import PhaseSource
import Lean.Elab.Tactic.Omega

/-!
Executable Option-valued sourceNext consumer of the all-time parity-mod3
phase invariant. No physical six-state blank proof is asserted here.
-/
namespace BB6.Agent2F321Phase
open BB6.Agent31F321Density

theorem sourceNext_terminal_requires_one_mod3
    {n a d:Nat}
    (hr:NextReach 1 1 n a d)
    (hn:sourceNext a d=none) : d%3=1 := by
  have ha : a=d+1 := (sourceNext_none_iff a d).mp hn
  subst a
  exact terminal_requires_one_mod3 d n (next_reach_to_counter hr)

theorem sourceNext_no_terminal_outside_one_mod3
    (d:Nat) (hd:d%3≠1) :
    ∀ n, ¬(NextReach 1 1 n (d+1) d ∧
             sourceNext (d+1) d=none) := by
  intro n h
  exact hd (sourceNext_terminal_requires_one_mod3 h.1 h.2)

#print axioms sourceNext_terminal_requires_one_mod3
#print axioms sourceNext_no_terminal_outside_one_mod3

end BB6.Agent2F321Phase
