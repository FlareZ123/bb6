import FiniteDecision
namespace BB6Coverage

/-- All twelve input slots for the six-state two-symbol machine. -/
def allSlots : List Slot :=
  (List.finRange 6).flatMap (fun s => [(s,false),(s,true)])

/-- A branching decision is only permitted at an actually unassigned slot. -/
def findUnassigned (p : PartialMachine) : List Slot → Option Slot
  | [] => none
  | slot :: rest =>
      if p slot = none then some slot else findUnassigned p rest

theorem findUnassigned_sound (p : PartialMachine) (slots : List Slot)
    (s : Slot) (h : findUnassigned p slots = some s) : p s = none := by
  induction slots with
  | nil => simp [findUnassigned] at h
  | cons slot rest ih =>
    by_cases hs : p slot = none
    · simp [findUnassigned, hs] at h
      subst s
      exact hs
    · have hr : findUnassigned p rest = some s := by
        simpa [findUnassigned, hs] using h
      exact ih hr

/-- Bounded exhaustive sparse-table DFS. Every accepted 25-way branch
    must have all 25 actual recursive decision proofs. A false return
    is inconclusive, never evidence of an undecided or diverging machine. -/
def coverSearch (p : PartialMachine) (bound rayLimit : Nat) : Nat → Bool
  | 0 => finiteDecisionOracle p bound rayLimit
  | depth+1 =>
      if finiteDecisionOracle p bound rayLimit = true then true else
        match findUnassigned p allSlots with
        | none => false
        | some slot =>
            choices.all (fun t => coverSearch (refine p slot t) bound rayLimit depth)

/-- Every true Boolean result constructs an actual Cover proof over all
    possible full-table completions, with no unproved discard cases. -/
theorem coverSearch_sound (bound rayLimit depth : Nat) :
    ∀ p : PartialMachine,
      coverSearch p bound rayLimit depth = true → Cover (DecidedBelow bound) p := by
  induction depth with
  | zero =>
    intro p h
    exact finiteDecisionOracle_sound p bound rayLimit h
  | succ depth ih =>
    intro p h
    by_cases hleaf : finiteDecisionOracle p bound rayLimit = true
    · exact finiteDecisionOracle_sound p bound rayLimit hleaf
    · cases hslot : findUnassigned p allSlots with
      | none => simp [coverSearch, hleaf, hslot] at h
      | some slot =>
        have hchildren : choices.all
            (fun t => coverSearch (refine p slot t) bound rayLimit depth) = true := by
          simpa [coverSearch, hleaf, hslot] using h
        have hs : p slot = none := findUnassigned_sound p allSlots slot hslot
        apply Cover.branch p slot hs
        intro t ht
        exact ih (refine p slot t) ((List.all_eq_true.mp hchildren) t ht)

/-- The A/0 slot and all six read-one slots are free; B..F on 0 halt. -/
def oneHoleUniversalTable : PartialMachine := fun slot =>
  if slot.1 = (⟨0, by decide⟩ : Fin 6) then none else
    if slot.2 = false then some none else none

/-- All 25 A/0 actions provably decide within two steps or diverge
    by a permanent blank sweep. Seven input slots remain free in parent. -/
theorem oneHoleUniversalCheck :
    coverSearch oneHoleUniversalTable 2 0 1 = true := by decide

theorem oneHoleUniversalCertificate :
    Cover (DecidedBelow 2) oneHoleUniversalTable :=
  coverSearch_sound 2 0 1 oneHoleUniversalTable oneHoleUniversalCheck

#print axioms findUnassigned_sound
#print axioms coverSearch_sound
#print axioms oneHoleUniversalCertificate
end BB6Coverage
