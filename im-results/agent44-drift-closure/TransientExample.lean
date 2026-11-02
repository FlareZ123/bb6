import PrefixDrift

namespace BB6Coverage

/-- A four-transition sparse machine which temporarily reverses direction,
    erases the initial marked cell, then enters a fresh one-way drift. -/
def transientTable : PartialMachine := fun slot =>
  if slot = (0, false) then some (some ⟨true, true, 1⟩)
  else if slot = (1, false) then some (some ⟨false, false, 0⟩)
  else if slot = (0, true) then some (some ⟨false, true, 2⟩)
  else if slot = (2, false) then some (some ⟨true, true, 2⟩)
  else none

def transientWitness : Machine := fun slot => (transientTable slot).getD none

def transientEntry : Config :=
  { state := ⟨2, by decide⟩, head := 1, tape := fun _ => false }

private theorem transient_compat : compatible transientTable transientWitness := by
  intro slot t ht
  simp [transientWitness]
  rw [ht]
  rfl

private theorem transient_three : run transientWitness 3 blank = some transientEntry := by
  simp [run, rawStep, readSlot, blank, applyMove, transientWitness,
    transientTable, transientEntry]
  funext x
  by_cases h : x = 0
  · simp [h]
  · simp [h]

private theorem transient_known :
    ∀ i, i < 3 → ∀ d, run transientWitness i blank = some d →
      transientTable (readSlot d) = some (transientWitness (readSlot d)) := by
  intro i hi d hd
  have hi_cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi_cases with rfl | rfl | rfl
  all_goals
    simp [run, rawStep, readSlot, blank, applyMove,
      transientWitness, transientTable] at hd
    subst d
    simp [transientTable, transientWitness, readSlot]

private theorem transient_closed :
    PartialDriftClosed transientTable (fun s => s = 2) true := by
  intro s hs
  subst s
  exact ⟨true, 2, by decide, rfl⟩

/-- Real all-time nonhalting coverage for 25^8 complete canonical tables
    that are outside either prior zero-writer or fixed-direction class. -/
theorem transient_drift_cover (B : Nat) :
    Cover (DecidedBelow B) transientTable := by
  exact prefix_drift_cover transientTable transientWitness (fun s => s=2)
    true 3 transientEntry B transient_compat transient_known transient_three
    rfl (by intro x hx; rfl) transient_closed

#print axioms transient_drift_cover
#print axioms transient_three
end BB6Coverage
