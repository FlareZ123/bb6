import MarkedHaltBranch
import FrontierMass

namespace BB6Coverage

/-- The two physically executed instructions, deliberately leaving the
    actual read-one state-symbol input unresolved. -/
def markedReturnPrefix (q : Fin 6) (dir w0 : Bool) : PartialMachine :=
  fun slot =>
    if slot = initialSlot then some (some ⟨true, dir, q⟩)
    else if slot = (q, false) then some (some ⟨w0, !dir, q⟩)
    else none

theorem markedReturnPrefix_hole (q : Fin 6) (dir w0 : Bool) :
    markedReturnPrefix q dir w0 (q, true) = none := by
  simp [markedReturnPrefix, initialSlot]

def markedReturnPhysicalSlotCheck (q : Fin 6)
    (dir w0 : Bool) : Bool :=
  match finitePartialRun (markedReturnPrefix q dir w0) 2 finiteBlank with
  | none => false
  | some c => decide ((c.state, finiteTape c c.head) = (q, true))

/-- The split at q/1 is the actual *physical* third transition
    after the assigned two-move marked-cell return, for all 20
    concrete q,d,u choices. No hypothetical zero-row shortcut. -/
theorem markedReturnPhysicalSlot_all :
    markedHaltParams.all (fun (q, dir, w0) =>
      markedReturnPhysicalSlotCheck q dir w0) = true := by
  decide

theorem markedReturnPhysicalSlot (q : Fin 6) (dir w0 : Bool)
    (hp : (q, dir, w0) ∈ markedHaltParams) :
    ∃ c : FinRayCfg,
       finitePartialRun (markedReturnPrefix q dir w0) 2 finiteBlank = some c ∧
       (c.state, finiteTape c c.head) = (q, true) := by
  have hc : markedReturnPhysicalSlotCheck q dir w0 = true :=
    (List.all_eq_true.mp markedReturnPhysicalSlot_all) _ hp
  cases hr : finitePartialRun (markedReturnPrefix q dir w0) 2 finiteBlank with
  | none => simp [markedReturnPhysicalSlotCheck, hr] at hc
  | some c =>
      exact ⟨c, rfl, of_decide_eq_true
        (by simpa [markedReturnPhysicalSlotCheck, hr] using hc)⟩

/-- One exact source-certified-or-open q/1 branch, not a
    post hoc list of outcomes. Every one of the 25 genuine
    transition choices has an actual terminal leaf. -/
def markedReadOneChild (p : PartialMachine) (q : Fin 6) :
    FrontierAudit (DecidedBelow 3) p :=
  if hh : finiteHaltCheck p 2 = true then
    .certified p (finiteHaltCheck_sound p 2 3 (by decide) hh)
  else if hn : bothSymbolPrefixCheck p 1 (fun s => s == q) = true then
    .certified p (bothSymbolPrefixCheck_sound p 1
      (fun s => s == q) 3 hn)
  else
    .unresolved p

def markedReadOneLocalAudit (q : Fin 6) (dir w0 : Bool) :
    FrontierAudit (DecidedBelow 3) (markedReturnPrefix q dir w0) :=
  .branch (markedReturnPrefix q dir w0) (q, true)
    (markedReturnPrefix_hole q dir w0)
    (fun t _ => markedReadOneChild
      (refine (markedReturnPrefix q dir w0) (q, true) t) q)

/-- For each of twenty actual marked-return prefixes,
    exactly FIVE q/1 assignments (one halt, four q-self-loop moves)
    are certified, and the other twenty remain open. The report
    counts disjoint compatible full tables, not observed simulations. -/
theorem markedReadOneLocal_massCheck :
    markedHaltParams.all (fun (q, dir, w0) =>
      decide (
        (markedReadOneLocalAudit q dir w0).report.1 = 5 * 25^9 ∧
        (markedReadOneLocalAudit q dir w0).report.2 = 20 * 25^9)) = true := by
  decide

theorem markedReadOneLocal_exact_mass (q : Fin 6) (dir w0 : Bool)
    (hp : (q, dir, w0) ∈ markedHaltParams) :
    (markedReadOneLocalAudit q dir w0).report.1 = 5 * 25^9 ∧
    (markedReadOneLocalAudit q dir w0).report.2 = 20 * 25^9 := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp markedReadOneLocal_massCheck) _ hp)

theorem markedReadOneLocal_exhaustive (q : Fin 6) (dir w0 : Bool)
    (m : Machine) (hm : compatible (markedReturnPrefix q dir w0) m) :
    DecidedBelow 3 m ∨ (markedReadOneLocalAudit q dir w0).open m :=
  (markedReadOneLocalAudit q dir w0).exhaustive m hm

#print axioms markedReturnPrefix_hole
#print axioms markedReturnPhysicalSlot_all
#print axioms markedReturnPhysicalSlot
#print axioms markedReadOneLocal_massCheck
#print axioms markedReadOneLocal_exact_mass
#print axioms markedReadOneLocal_exhaustive

end BB6Coverage
