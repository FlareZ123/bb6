import HaltSlotFreedom
import CryptidsF287

namespace BB6.F287

open BB6Coverage

/-- State F reading 1 is the unique halting entry of the source-verified
nonhalting six-state A6/F287 table. -/
def haltInput : Slot := (⟨5, by decide⟩, true)

theorem literal_halt_input : expectedRLE haltInput = none := rfl

/-- An actual 11-fixed-slot cylinder: the F/1 transition is unconstrained.
Every one of the 25 possible F/1 replacements is nonhalting on blank,
because source nonhalting proves this halt entry is never consulted. -/
def twentyFiveCylinder : PartialMachine :=
  freeHaltCylinder expectedRLE haltInput

theorem twentyFive_cover (bound : Nat) :
    Cover (DecidedBelow bound) twentyFiveCylinder :=
  freeHaltCylinder_cover bound expectedRLE haltInput
    literal_halt_input literal_never

/-- The full-table cardinality is exactly 25, strengthening the original
one-machine F287 source certificate. This is a simple logical consequence
of the previously known source nonhalting theorem, not a new holdout decision. -/
theorem twentyFive_mass : cylinderMass twentyFiveCylinder = 25 := by
  decide

/-- A uniform all-time semantic statement, not merely a bounded decider. -/
theorem twentyFive_uniform (m : Machine)
    (hm : compatible twentyFiveCylinder m) :
    NeverHalts m := by
  have h := (twentyFive_cover 0).sound m hm
  rcases h with h | ⟨n, hn, _⟩
  · exact h
  · omega

#print axioms literal_halt_input
#print axioms twentyFive_cover
#print axioms twentyFive_mass
#print axioms twentyFive_uniform

end BB6.F287
