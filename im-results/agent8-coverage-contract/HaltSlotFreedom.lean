import Frontier

namespace BB6Coverage

/-- A genuine halting transition of a nonhalting source machine cannot be
encountered on any configuration in its infinite blank-tape run. -/
theorem never_reaches_halt_slot (m : Machine) (slot : Slot)
    (hhalt : m slot = none) (hlive : NeverHalts m)
    (n : Nat) (c : Config) (hc : run m n blank = some c) :
    readSlot c ≠ slot := by
  intro heq
  have hnone : run m (n+1) blank = none := by
    simp [run, hc, rawStep, heq, hhalt]
  have hsome := hlive (n+1)
  simp [hnone] at hsome

/-- Source nonhalting is preserved after arbitrarily changing a transition
that was originally halting. This follows from an all-time trace equality,
not a bounded simulation or an assumed list of visited states. -/
theorem neverHalts_change_halt_slot (m m' : Machine) (slot : Slot)
    (hhalt : m slot = none) (hlive : NeverHalts m)
    (heq : ∀ s, s ≠ slot → m' s = m s) : NeverHalts m' := by
  intro n
  have hrun : run m n blank = run m' n blank := by
    apply run_agrees_on_prefix
    intro k _ c hc
    exact (heq (readSlot c) (never_reaches_halt_slot m slot hhalt hlive k c hc)).symm
  rw [← hrun]
  exact hlive n

/-- Fix eleven transitions and leave the known, never-visited halt input
free: a genuine 25-way extension cylinder. -/
def freeHaltCylinder (m : Machine) (slot : Slot) : PartialMachine :=
  fun s => if s = slot then none else some (m s)

/-- A published source proof for one nonhalting machine with a halt input
implies a uniform nonhalting theorem for its 25 full-table modifications. -/
theorem freeHaltCylinder_cover (bound : Nat) (m : Machine) (slot : Slot)
    (hhalt : m slot = none) (hlive : NeverHalts m) :
    Cover (DecidedBelow bound) (freeHaltCylinder m slot) := by
  apply Cover.leaf
  intro m' hm'
  left
  apply neverHalts_change_halt_slot m m' slot hhalt hlive
  intro s hs
  have h : freeHaltCylinder m slot s = some (m s) := by
    simp [freeHaltCylinder, hs]
  exact hm' s (m s) h

#print axioms never_reaches_halt_slot
#print axioms neverHalts_change_halt_slot
#print axioms freeHaltCylinder_cover

end BB6Coverage
