import PhysicalTraceAudit
import Agent3FiniteLasso

namespace BB6Coverage

/-- Search exact finite lasso witnesses at every genuine blank-tape entry
    depth up to entryLimit and positive loop lengths up to periodLimit. -/
def finiteLassoOracle (p : PartialMachine) (entryLimit periodLimit : Nat) : Bool :=
  (List.range (entryLimit + 1)).any (fun entry =>
    (List.range periodLimit).any (fun r =>
      finiteLassoCheck p entry (r + 1)))

theorem finiteLassoOracle_sound (p : PartialMachine)
    (entryLimit periodLimit bound : Nat)
    (h : finiteLassoOracle p entryLimit periodLimit = true) :
    Cover (DecidedBelow bound) p := by
  obtain ⟨entry, _, he⟩ := List.any_eq_true.mp h
  obtain ⟨r, _, hr⟩ := List.any_eq_true.mp he
  exact finiteLassoCheck_sound p entry (r+1) bound
    (by omega) hr

/-- The original finite-halting, pristine tape and fresh-ray certificates
    are retained, adding a source-sound exact full-tape lasso disjunct. -/
def lassoDecisionOracle (p : PartialMachine)
    (bound rayLimit entryLimit periodLimit : Nat) : Bool :=
  finiteDecisionOracle p bound rayLimit ||
    finiteLassoOracle p entryLimit periodLimit

theorem lassoDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit entryLimit periodLimit : Nat)
    (h : lassoDecisionOracle p bound rayLimit entryLimit periodLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hbase | hlasso
  · exact finiteDecisionOracle_sound p bound rayLimit hbase
  · exact finiteLassoOracle_sound p entryLimit periodLimit bound hlasso

/-- The same authentic physical first-unassigned read-zero/read-one search
    as Agent32, with a complete-configuration lasso leaf at each node.
    The recursive budget bounds only certificate discovery; open leaves
    remain explicit and no arbitrary machine is declared nonhalting. -/
def lassoPhysicalTraceAudit (p : PartialMachine)
    (bound rayLimit scanLimit entryLimit periodLimit : Nat) :
    (depth : Nat) → FrontierAudit (DecidedBelow bound) p
  | 0 =>
      if h : lassoDecisionOracle p bound rayLimit entryLimit periodLimit = true then
        .certified p (lassoDecisionOracle_sound p bound rayLimit entryLimit periodLimit h)
      else .unresolved p
  | depth + 1 =>
      if h : lassoDecisionOracle p bound rayLimit entryLimit periodLimit = true then
        .certified p (lassoDecisionOracle_sound p bound rayLimit entryLimit periodLimit h)
      else
        match hs : firstUnknownPhysical p scanLimit finiteBlank with
        | none => .unresolved p
        | some slot =>
            .branch p slot (firstUnknownPhysical_sound p scanLimit finiteBlank slot hs)
              (fun t _ => lassoPhysicalTraceAudit
                (refine p slot t) bound rayLimit scanLimit
                entryLimit periodLimit depth)

def globalLassoPhysicalTraceAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 6 6 12

theorem globalLassoPhysicalTraceAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ globalLassoPhysicalTraceAudit.open m :=
  globalLassoPhysicalTraceAudit.exhaustive m (empty_compatible m)

theorem globalLassoPhysicalTraceAudit_conserves :
    globalLassoPhysicalTraceAudit.report.1 +
      globalLassoPhysicalTraceAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := globalLassoPhysicalTraceAudit.report_conserves
    _ = 25^12 := by decide

/-- An assigned A/1 return is accepted by the general source lasso
    leaf but requires a true read-one branch before that certificate exists. -/
theorem markedReturn_lassoOracle :
    finiteLassoOracle markedReturnTable 2 4 = true := by decide

theorem erasingReturn_lassoOracle :
    finiteLassoOracle erasingReturnTable 2 4 = true := by decide

#print axioms finiteLassoOracle_sound
#print axioms lassoDecisionOracle_sound
#print axioms globalLassoPhysicalTraceAudit_exhaustive
#print axioms globalLassoPhysicalTraceAudit_conserves
end BB6Coverage
