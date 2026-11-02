import HaltSlotFreedom

namespace BB6Coverage

/-- No halted input can occur in the live blank run of an all-time
nonhalting machine, even if the table has many halted entries. -/
theorem never_reads_missing (m : Machine) (hlive : NeverHalts m)
    (n : Nat) (c : Config) (hc : run m n blank = some c) :
    m (readSlot c) ≠ none := by
  intro hnone
  have hstop : run m (n+1) blank = none := by
    simp [run, hc, rawStep, hnone]
  have hs := hlive (n+1)
  simp [hstop] at hs

/-- Leaves precisely all original halting transitions unassigned. -/
def freeAllHalts (m : Machine) : PartialMachine :=
  fun s => if m s = none then none else some (m s)

/-- The entire semantically live blank run is independent of the choices
made at all originally halting inputs, simultaneously. -/
theorem freeAllHalts_run (m m' : Machine) (hlive : NeverHalts m)
    (hcompat : compatible (freeAllHalts m) m') (n : Nat) :
    run m n blank = run m' n blank := by
  apply run_agrees_on_prefix
  intro k _ c hc
  have hne := never_reads_missing m hlive k c hc
  have hp : freeAllHalts m (readSlot c) = some (m (readSlot c)) := by
    simp [freeAllHalts, hne]
  exact (hcompat (readSlot c) (m (readSlot c)) hp).symm

/-- A single nonhalting source theorem supplies a certified cylinder with
25^h full machines, where h is the number of original halting inputs. -/
theorem freeAllHalts_cover (bound : Nat) (m : Machine)
    (hlive : NeverHalts m) :
    Cover (DecidedBelow bound) (freeAllHalts m) := by
  apply Cover.leaf
  intro m' hm
  left
  intro n
  rw [← freeAllHalts_run m m' hlive hm n]
  exact hlive n

#print axioms never_reads_missing
#print axioms freeAllHalts_run
#print axioms freeAllHalts_cover

end BB6Coverage
