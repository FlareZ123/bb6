import ZeroPathAudit

namespace BB6Coverage

/-- A rooted read-zero control-path scanner. It is deliberately an
    *enumeration policy*, not a simulation of the machine after writing one:
    such a path may then read a marked cell. All certifications below are
    delegated to original-source sound oracles. -/
def scanControlPath (p : PartialMachine) : Nat → Fin 6 → Option Slot
  | 0, _ => none
  | n + 1, s =>
      match p (s, false) with
      | none => some (s, false)
      | some none => none
      | some (some mv) => scanControlPath p n mv.next

theorem scanControlPath_sound (p : PartialMachine) (n : Nat)
    (start : Fin 6) (slot : Slot)
    (h : scanControlPath p n start = some slot) :
    p slot = none := by
  induction n generalizing start with
  | zero => simp [scanControlPath] at h
  | succ n ih =>
      cases hp : p (start, false) with
      | none =>
          simp [scanControlPath, hp] at h
          subst slot
          exact hp
      | some t =>
          cases t with
          | none => simp [scanControlPath, hp] at h
          | some mv =>
              have hnext : scanControlPath p n mv.next = some slot := by
                simpa [scanControlPath, hp] using h
              exact ih mv.next hnext

/-- The existing original-source ray mask soundness can certify uniform
    directional motion even when visited transitions write ones. -/
def directionalMaskOracle (p : PartialMachine) : Bool :=
  (List.range 64).any (fun u =>
    rayMaskCheck p true (fun s => u.testBit s.val) ||
    rayMaskCheck p false (fun s => u.testBit s.val))

theorem directionalMaskOracle_sound (p : PartialMachine) (bound : Nat)
    (h : directionalMaskOracle p = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
  rcases (Bool.or_eq_true _ _).mp hu with hr | hl
  · exact rayMaskCheck_sound p true (fun s => u.testBit s.val) bound hr
  · exact rayMaskCheck_sound p false (fun s => u.testBit s.val) bound hl

/-- Three separately sound outcomes, each over all completions of a
    sparse table: short raw halt, arbitrary-direction zero-writer closure,
    and any-writer constant-direction ray closure. -/
def controlDecisionOracle (p : PartialMachine) (bound : Nat) : Bool :=
  (finiteHaltOracle p bound || zeroMaskOracle p) || directionalMaskOracle p

theorem controlDecisionOracle_sound (p : PartialMachine) (bound : Nat)
    (h : controlDecisionOracle p bound = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hshort | hray
  · rcases (Bool.or_eq_true _ _).mp hshort with hh | hz
    · exact finiteHaltOracle_sound p bound hh
    · exact zeroMaskOracle_sound p bound hz
  · exact directionalMaskOracle_sound p bound hray

/-- A global partial proof-carrying census over the original 25^12 raw
    six-state tables. Its open leaves are not assigned a halting verdict.
    No unsafe read-zero simulation inference is used after writing one. -/
def controlPathAudit (p : PartialMachine) (bound : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : controlDecisionOracle p bound = true then
        .certified p (controlDecisionOracle_sound p bound h)
      else .unresolved p
  | depth + 1 =>
      if h : controlDecisionOracle p bound = true then
        .certified p (controlDecisionOracle_sound p bound h)
      else
        match hs : scanControlPath p 6 ⟨0, by decide⟩ with
        | none => .unresolved p
        | some slot =>
            .branch p slot (scanControlPath_sound p 6 ⟨0, by decide⟩ slot hs)
              (fun t _ => controlPathAudit (refine p slot t) bound depth)

def globalControlPathAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  controlPathAudit emptyTable 6 6

theorem globalControlPathAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalControlPathAudit.open m :=
  globalControlPathAudit.exhaustive m (empty_compatible m)

theorem globalControlPathAudit_conserves :
    globalControlPathAudit.report.1 + globalControlPathAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalControlPathAudit.report_conserves
    _ = 25^12 := by decide

#print axioms scanControlPath_sound
#print axioms directionalMaskOracle_sound
#print axioms controlDecisionOracle_sound
#print axioms globalControlPathAudit_exhaustive
#print axioms globalControlPathAudit_conserves

end BB6Coverage
