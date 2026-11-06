import ZeroRowAudit

namespace BB6Coverage

/-- Genuine sparse blank-tape execution, retaining the finite set of
    physically written one-cells. This scanner chooses the first table
    input not yet assigned on the *actual* finite trace. It may select
    a read-one row and is not limited to hypothetical read-zero graphs. -/
def firstUnknownPhysical (p : PartialMachine) :
    Nat → FinRayCfg → Option Slot
  | 0, _ => none
  | n + 1, c =>
      match p (c.state, finiteTape c c.head) with
      | none => some (c.state, finiteTape c c.head)
      | some none => none
      | some (some mv) =>
          firstUnknownPhysical p n (finiteMove c mv)

/-- The trace-derived branch input is actually unassigned. In particular
    no previously written one is mistaken for a blank when branching. -/
theorem firstUnknownPhysical_sound (p : PartialMachine) (n : Nat)
    (c : FinRayCfg) (slot : Slot)
    (h : firstUnknownPhysical p n c = some slot) :
    p slot = none := by
  induction n generalizing c with
  | zero => simp [firstUnknownPhysical] at h
  | succ n ih =>
      cases hp : p (c.state, finiteTape c c.head) with
      | none =>
          simp [firstUnknownPhysical, hp] at h
          subst slot
          exact hp
      | some t =>
          cases t with
          | none => simp [firstUnknownPhysical, hp] at h
          | some mv =>
              have hn :
                  firstUnknownPhysical p n (finiteMove c mv) = some slot := by
                simpa [firstUnknownPhysical, hp] using h
              exact ih (finiteMove c mv) hn

/-- A concrete true blank run: A/0 writes a one and moves right to B,
    B/0 moves back left to A, and the next *physical input* is A/1.
    Only A/0 and B/0 are assigned; the new scanner targets the first
    genuinely missing read-one transition. -/
def readOneReturnTable : PartialMachine := fun slot =>
  if slot = (⟨0, by decide⟩, false) then
    some (some ⟨true, true, ⟨1, by decide⟩⟩)
  else if slot = (⟨1, by decide⟩, false) then
    some (some ⟨false, false, ⟨0, by decide⟩⟩)
  else none

theorem readOneReturnTable_actual_first_unknown :
    firstUnknownPhysical readOneReturnTable 3 finiteBlank =
      some (⟨0, by decide⟩, true) := by decide

/-- The older read-zero control-graph-only split policy sees no free
    slot on this very same partial table, even though the physical tape
    run genuinely demands the unassigned A/1 transition. -/
theorem readOneReturnTable_zero_only_scan_misses :
    scanControlPath readOneReturnTable 6 ⟨0, by decide⟩ = none := by decide

theorem readOneReturnTable_first_unknown_is_free :
    readOneReturnTable (⟨0, by decide⟩, true) = none :=
  firstUnknownPhysical_sound readOneReturnTable 3 finiteBlank _
    readOneReturnTable_actual_first_unknown

/-- The same authentic original-source terminal oracles as before.
    The new policy explores read-one transitions when actually needed.
    Termination of the proof object is by finite branch depth, never a
    conjectural runtime cutoff on the real Turing machine. -/
def physicalTraceAudit (p : PartialMachine) (bound rayLimit scanLimit : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : finiteDecisionOracle p bound rayLimit = true then
        .certified p (finiteDecisionOracle_sound p bound rayLimit h)
      else .unresolved p
  | depth + 1 =>
      if h : finiteDecisionOracle p bound rayLimit = true then
        .certified p (finiteDecisionOracle_sound p bound rayLimit h)
      else
        match hs : firstUnknownPhysical p scanLimit finiteBlank with
        | none => .unresolved p
        | some slot =>
            .branch p slot
              (firstUnknownPhysical_sound p scanLimit finiteBlank slot hs)
              (fun t _ => physicalTraceAudit
                (refine p slot t) bound rayLimit scanLimit depth)

/-- Fully global 25-choice raw-machine audit whose branch-selection policy
    can reach either read-zero or read-one slots on genuine tape states.
    Every undecided table remains explicitly open. -/
def globalPhysicalTraceAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  physicalTraceAudit emptyTable 6 6 12 12

theorem globalPhysicalTraceAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalPhysicalTraceAudit.open m :=
  globalPhysicalTraceAudit.exhaustive m (empty_compatible m)

theorem globalPhysicalTraceAudit_conserves :
    globalPhysicalTraceAudit.report.1 +
      globalPhysicalTraceAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalPhysicalTraceAudit.report_conserves
    _ = 25^12 := by decide

#print axioms firstUnknownPhysical_sound
#print axioms globalPhysicalTraceAudit_exhaustive
#print axioms globalPhysicalTraceAudit_conserves

end BB6Coverage
