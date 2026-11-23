import BB429Branch29Small
import BB429Branch29Reflect1024
import Lean.Elab.Tactic.Omega

/-!
# Unconditional all-parameter 29(mod32) reset prestate restriction

No lower bound on q, no finite orbit horizon, no experimental periodicity.
A finite prefix exclusion (rigorously extended to all time by rank
monotonicity) rules out q<21. For all larger q, a symbolic
all-parameter inverse-tree certificate confines q modulo1024 to 38
explicit residue classes. This remains a necessary root restriction,
not a halting decision for the six-state machine.
-/

namespace BB429Branch29All
open BB429Reset31

theorem rooted_29_global (q : Nat)
    (hroot : Reach (32*q+29) (64*q+55)) :
    21≤q ∧
    q%1024 ∈ BB429Branch29Reflect1024.surviving1024 := by
  have hq : 21≤q := by
    by_contra hh
    have hsmall : q<21 := by omega
    exact BB429Branch29Small.no_small_q q hsmall hroot
  exact ⟨hq,
    BB429Branch29Reflect1024.rooted_29_q_38_mod1024
      q hq hroot⟩

#print axioms rooted_29_global
end BB429Branch29All
