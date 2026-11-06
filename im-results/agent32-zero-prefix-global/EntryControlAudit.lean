import ControlPathAudit

namespace BB6Coverage

/-- A genuine two-slot fresh-ray entry. A writes zero and moves into a
    noninitial control state q. That state writes one, reverses direction,
    and continues in the same state, forever traversing fresh cells.
    The right/left ray starts immediately after A's first ordinary step. -/
def reverseTurnTable (q : Fin 6) (dir : Bool) : PartialMachine :=
  fun slot =>
    if slot = (⟨0, by decide⟩, false) then
      some (some ⟨false, dir, q⟩)
    else if slot = (q, false) then
      some (some ⟨true, !dir, q⟩)
    else none

/-- Exactly ten mutually distinct source-cylinder candidates, one for
    each q in B..F and initial direction. They are disjoint at A/0. -/
def reverseTurnCases : List PartialMachine :=
  [reverseTurnTable 1 true, reverseTurnTable 1 false,
   reverseTurnTable 2 true, reverseTurnTable 2 false,
   reverseTurnTable 3 true, reverseTurnTable 3 false,
   reverseTurnTable 4 true, reverseTurnTable 4 false,
   reverseTurnTable 5 true, reverseTurnTable 5 false]

theorem reverseTurnCases_length : reverseTurnCases.length = 10 := by decide

/-- Full original-source finite-tape ray checker certifies each of these
    ten two-slot sparse machines after *one* ordinary blank-root move.
    This is an evaluated finite theorem, not an assumed pattern. -/
theorem reverseTurnCases_check :
    reverseTurnCases.all (fun p => finiteRayOracle p 1) = true := by
  decide

theorem reverseTurnCase_source_cover (p : PartialMachine)
    (h : p ∈ reverseTurnCases) (B : Nat) :
    Cover (DecidedBelow B) p :=
  finiteRayOracle_sound p 1 B
    ((List.all_eq_true.mp reverseTurnCases_check) p h)

/-- Every listed cylinder has precisely ten unassigned input slots. -/
theorem reverseTurnCases_mass :
    reverseTurnCases.all (fun p => decide (cylinderMass p = 25^10)) = true := by
  decide

theorem reverseTurnCase_mass (p : PartialMachine)
    (h : p ∈ reverseTurnCases) :
    cylinderMass p = 25^10 :=
  of_decide_eq_true ((List.all_eq_true.mp reverseTurnCases_mass) p h)

/-- Stronger safe oracle: a finite authenticated prefix may enter a
    blank directed ray even when the earlier zero-state control path has
    mixed write bits and opposite directions. -/
def entryControlOracle (p : PartialMachine) (bound : Nat) : Bool :=
  controlDecisionOracle p bound || finiteRayOracle p 1

theorem entryControlOracle_sound (p : PartialMachine) (bound : Nat)
    (h : entryControlOracle p bound = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hc | he
  · exact controlDecisionOracle_sound p bound hc
  · exact finiteRayOracle_sound p 1 bound he

/-- A globally exhaustive and sound partial audit with genuine prefix-ray
    entry. No unassigned transition is ever assumed to be nonhalting. -/
def entryControlAudit (p : PartialMachine) (bound : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : entryControlOracle p bound = true then
        .certified p (entryControlOracle_sound p bound h)
      else .unresolved p
  | depth + 1 =>
      if h : entryControlOracle p bound = true then
        .certified p (entryControlOracle_sound p bound h)
      else
        match hs : scanControlPath p 6 ⟨0, by decide⟩ with
        | none => .unresolved p
        | some slot =>
            .branch p slot (scanControlPath_sound p 6 ⟨0, by decide⟩ slot hs)
              (fun t _ => entryControlAudit (refine p slot t) bound depth)

def globalEntryControlAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  entryControlAudit emptyTable 6 6

theorem globalEntryControlAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalEntryControlAudit.open m :=
  globalEntryControlAudit.exhaustive m (empty_compatible m)

theorem globalEntryControlAudit_conserves :
    globalEntryControlAudit.report.1 +
      globalEntryControlAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalEntryControlAudit.report_conserves
    _ = 25^12 := by decide

#print axioms reverseTurnCases_check
#print axioms reverseTurnCase_source_cover
#print axioms reverseTurnCase_mass
#print axioms entryControlOracle_sound
#print axioms globalEntryControlAudit_exhaustive
#print axioms globalEntryControlAudit_conserves

end BB6Coverage
