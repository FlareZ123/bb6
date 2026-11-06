import FrontierMass
import FiniteDecision

namespace BB6Coverage

/-- Follow only assigned read-zero, write-zero transitions from the genuine
    initial state. A result is precisely the first genuinely unassigned
    transition on that path. Halt and write-one terminate this scan. -/
def scanZeroPath (p : PartialMachine) : Nat → Fin 6 → Option Slot
  | 0, _ => none
  | n + 1, s =>
      match p (s, false) with
      | none => some (s, false)
      | some none => none
      | some (some mv) =>
          if mv.write then none else scanZeroPath p n mv.next

/-- No guessed branch: an emitted scan slot was truly unassigned. -/
theorem scanZeroPath_sound (p : PartialMachine) (n : Nat) (start : Fin 6)
    (slot : Slot) (h : scanZeroPath p n start = some slot) :
    p slot = none := by
  induction n generalizing start with
  | zero => simp [scanZeroPath] at h
  | succ n ih =>
      cases hp : p (start, false) with
      | none =>
          simp [scanZeroPath, hp] at h
          subst slot
          exact hp
      | some t =>
          cases t with
          | none => simp [scanZeroPath, hp] at h
          | some mv =>
              by_cases hw : mv.write = true
              · simp [scanZeroPath, hp, hw] at h
              · have hn : scanZeroPath p n mv.next = some slot := by
                  simpa [scanZeroPath, hp, Bool.eq_false_iff.mpr hw] using h
                exact ih mv.next hn

/-- A proof-carrying partial global audit. Unlike a fixed-slot DFS, it
    splits the first unassigned read-zero slot on the currently followed
    blank-only control path. A provable early halt or closed zero-writing
    state set becomes an original-source Cover leaf; all other paths
    remain explicitly open. The finite recursion is on the number of
    fresh zero-reading slots, never on a simulated time cutoff. -/
def zeroPathAudit (p : PartialMachine) (bound : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if hh : finiteHaltOracle p bound = true then
        .certified p (finiteHaltOracle_sound p bound hh)
      else if hz : zeroMaskOracle p = true then
        .certified p (zeroMaskOracle_sound p bound hz)
      else .unresolved p
  | depth + 1 =>
      if hh : finiteHaltOracle p bound = true then
        .certified p (finiteHaltOracle_sound p bound hh)
      else if hz : zeroMaskOracle p = true then
        .certified p (zeroMaskOracle_sound p bound hz)
      else
        match hs : scanZeroPath p 6 ⟨0, by decide⟩ with
        | none => .unresolved p
        | some slot =>
            .branch p slot (scanZeroPath_sound p 6 ⟨0, by decide⟩ slot hs)
              (fun t _ => zeroPathAudit (refine p slot t) bound depth)

/-- A concrete global audit over all 25^12 raw six-state tables. This is an
    explicit partial tree and is not a global upper-bound certificate. -/
def globalZeroPathAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  zeroPathAudit emptyTable 6 6

theorem globalZeroPathAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalZeroPathAudit.open m :=
  globalZeroPathAudit.exhaustive m (empty_compatible m)

theorem globalZeroPathAudit_conserves :
    globalZeroPathAudit.report.1 + globalZeroPathAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalZeroPathAudit.report_conserves
    _ = 25^12 := by decide

#print axioms scanZeroPath_sound
#print axioms globalZeroPathAudit_exhaustive
#print axioms globalZeroPathAudit_conserves

end BB6Coverage
