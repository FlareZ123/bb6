import Q0Index33Automata
import WeightedTNF

namespace BB6.Agent50Q0Index33

open BB6Coverage
open BB6.Agent13BlankDelay

/-- The sole post-decider open table at q0 sibling-scan index 33:
    1RB1RD 1RC0RE 0LA--- 1LA1LD 0LF0RB 1LF0LC.
    Its only unassigned slot is C1.  The table is the exact R33L0
    certificate table, not a separately reconstructed approximation. -/
abbrev residual : PartialMachine :=
  BB6.Agent50Q0Index33Automata.R33L0.table

def haltCompletion : Machine := fun s => (residual s).getD none

/-- The isolated two-sided automata certificate proves that every completion
    of this residual is nonhalting, including the completion with C1 = halt. -/
theorem residual_never (m : Machine) (hm : compatible residual m) :
    NeverHalts m :=
  BB6.Agent50Q0Index33Automata.R33L0.never m hm

theorem haltCompletion_compatible : compatible residual haltCompletion := by
  intro s t hs
  simp [haltCompletion, hs]

theorem haltCompletion_never : NeverHalts haltCompletion :=
  residual_never haltCompletion haltCompletion_compatible

/-- A genuine proof-carrying Cover leaf for all 25 completions of the
    one-hole residual, at every weighted bound. -/
theorem residual_weighted_bound (B : Nat) :
    ∀ m, compatible residual m → WeightedBound B m := by
  intro m hm
  exact weighted_never B m (residual_never m hm)

theorem residual_cover (B : Nat) : Cover (WeightedBound B) residual :=
  .leaf residual (residual_weighted_bound B)

#print axioms residual_never
#print axioms haltCompletion_never
#print axioms residual_cover

end BB6.Agent50Q0Index33
