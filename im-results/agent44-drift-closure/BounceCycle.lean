import LeafRules

namespace BB6Coverage

/-- A/0=1RB, B/0=0LA, A/1=0RB: the marked original cell is
    erased on the return trip, and the full blank configuration repeats. -/
def bounceTable : PartialMachine := fun slot =>
  if slot = (0, false) then some (some ⟨true, true, 1⟩)
  else if slot = (1, false) then some (some ⟨false, false, 0⟩)
  else if slot = (0, true) then some (some ⟨false, true, 1⟩)
  else none

def bounceWitness : Machine := fun slot => (bounceTable slot).getD none

private theorem bounce_compatible : compatible bounceTable bounceWitness := by
  intro slot t ht
  simp [bounceWitness]
  rw [ht]
  rfl

/-- Exact original all-infinite-tape equality, after four genuine steps. -/
private theorem bounce_four : run bounceWitness 4 blank = some blank := by
  simp [run, rawStep, readSlot, blank, applyMove, bounceWitness,
    bounceTable]
  funext x
  by_cases h : x = 0
  · simp [h]
  · simp [h]

private theorem bounce_known :
    ∀ i, i < 4 → ∀ d, run bounceWitness i blank = some d →
      bounceTable (readSlot d) = some (bounceWitness (readSlot d)) := by
  intro i hi d hd
  have hi_cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl
  all_goals
    simp [run, rawStep, readSlot, blank, applyMove,
      bounceWitness, bounceTable] at hd
    subst d
    simp [bounceTable, bounceWitness, readSlot]

/-- A real 25^9-completion coverage certificate obtained by consuming
    Agent 8's original source-checked finite physical-tape cycle leaf. -/
theorem bounce_cover (B : Nat) : Cover (DecidedBelow B) bounceTable := by
  exact cycle_leaf bounceTable bounceWitness blank 0 4 B
    bounce_compatible (by decide) rfl bounce_four
    (by intro i hi x hx; omega) bounce_known

#print axioms bounce_four
#print axioms bounce_known
#print axioms bounce_cover
end BB6Coverage
