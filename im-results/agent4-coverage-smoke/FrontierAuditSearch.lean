import FrontierMass
import SparsePruneSearch

namespace BB6Coverage

/-- A bounded sparse search with explicit certified and unresolved leaves. -/
def auditSearch (p : PartialMachine) (bound rayLimit : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : finiteDecisionOracle p bound rayLimit = true then
        .certified p (finiteDecisionOracle_sound p bound rayLimit h)
      else .unresolved p
  | depth + 1 =>
      if h : finiteDecisionOracle p bound rayLimit = true then
        .certified p (finiteDecisionOracle_sound p bound rayLimit h)
      else
        match hs : findUnassigned p allSlots with
        | none => .unresolved p
        | some slot =>
          .branch p slot (findUnassigned_sound p allSlots slot hs)
            (fun t _ => auditSearch (refine p slot t) bound rayLimit depth)

theorem auditSearch_conserves (p : PartialMachine) (bound rayLimit depth : Nat) :
    (auditSearch p bound rayLimit depth).report.1 +
      (auditSearch p bound rayLimit depth).report.2 = cylinderMass p :=
  (auditSearch p bound rayLimit depth).report_conserves

theorem auditSearch_exhaustive (p : PartialMachine) (bound rayLimit depth : Nat)
    (m : Machine) (hm : compatible p m) :
    DecidedBelow bound m ∨ (auditSearch p bound rayLimit depth).open m :=
  (auditSearch p bound rayLimit depth).exhaustive m hm

#print axioms auditSearch_conserves
#print axioms auditSearch_exhaustive
end BB6Coverage
