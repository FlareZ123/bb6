import RayEntry
namespace BB6Coverage

def turnA : Move := ⟨false,true, ⟨1,by decide⟩⟩
def turnB : Move := ⟨true,false, ⟨2,by decide⟩⟩
def turnC : Move := ⟨true,false, ⟨2,by decide⟩⟩

/-- A0 goes right, B0 turns left, C0 sweeps left forever. The other
    nine entries remain completely unassigned. -/
def turnTable : PartialMachine := fun s =>
  if s = (⟨0,by decide⟩,false) then some (some turnA) else
  if s = (⟨1,by decide⟩,false) then some (some turnB) else
  if s = (⟨2,by decide⟩,false) then some (some turnC) else none

def turnW : Machine := fun s => (turnTable s).getD none
def turnEntry : Config := applyMove (applyMove blank turnA) turnB

theorem turn_witness_compatible : compatible turnTable turnW := by
  intro slot t ht
  change (turnTable slot).getD none = t
  rw [ht]
  rfl

theorem turn_trace_known :
    ∀ i, i < 2 → ∀ d, run turnW i blank = some d →
      turnTable (readSlot d) = some (turnW (readSlot d)) := by
  intro i hi d hd
  have hi_cases : i = 0 ∨ i = 1 := by omega
  rcases hi_cases with rfl | rfl
  · change some blank = some d at hd
    cases hd
    rfl
  · change some (applyMove blank turnA) = some d at hd
    cases hd
    rfl

theorem turn_entry_clean : freshLeft turnEntry := by
  intro x hx
  have h1 : x ≠ 1 := by
    simp [turnEntry,applyMove,turnA,turnB,blank] at hx
    omega
  by_cases hz : x = 0
  · simp [turnEntry, applyMove, turnA, turnB, blank, hz]
  · simp [turnEntry, applyMove, turnA, turnB, blank, hz, h1]

/-- An explicitly constructed finite-entry certificate beyond the zero-step
    monotone ray oracle: the first move is right and the tail is left. -/
theorem turn_example_certificate (bound : Nat) :
    Cover (DecidedBelow bound) turnTable := by
  apply left_entry_leaf turnTable turnW (fun s => s = (⟨2,by decide⟩ : Fin 6))
    2 turnEntry bound turn_witness_compatible
  · rfl
  · exact turn_trace_known
  · rfl
  · exact turn_entry_clean
  · intro s hs
    subst s
    exact ⟨turnC, by decide, rfl, rfl⟩

#print axioms turn_example_certificate
end BB6Coverage
