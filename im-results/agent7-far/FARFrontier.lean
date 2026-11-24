import FARBi
import LassoTraceAudit
import FrontierMass
namespace BB6Coverage.FAR

/-- Existing certified leaves and the exact branching structure are retained.
    A formerly open terminal is closed only by a checked FAR certificate. -/
def augment (limit bound : Nat) {p : PartialMachine} :
    FrontierAudit (DecidedBelow bound) p → FrontierAudit (DecidedBelow bound) p
  | .certified p cert => .certified p cert
  | .unresolved p =>
    if h : oracle p limit = true then
      .certified p (.leaf p (fun m hm => Or.inl (oracle_sound p limit h m hm)))
    else .unresolved p
  | .branch p s fresh kids => .branch p s fresh (fun t ht => augment limit bound (kids t ht))

theorem augment_open_subset (limit bound : Nat) {p : PartialMachine}
    (a : FrontierAudit (DecidedBelow bound) p) (m : Machine) :
    (augment limit bound a).open m → a.open m := by
  induction a with
  | certified p cert => simp [augment,FrontierAudit.open]
  | unresolved p => simp [FrontierAudit.open]
  | branch p s fresh kids ih =>
    exact ih (m s) (choices_complete (m s))

def baseline : FrontierAudit (DecidedBelow 6) emptyTable :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4

def depth4 (limit : Nat) : FrontierAudit (DecidedBelow 6) emptyTable :=
  augment limit 6 baseline

theorem depth4_exhaustive (limit : Nat) (m : Machine) :
    DecidedBelow 6 m ∨ (depth4 limit).open m :=
  (depth4 limit).exhaustive m (empty_compatible m)

theorem depth4_conserves (limit : Nat) :
    (depth4 limit).report.1 + (depth4 limit).report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := (depth4 limit).report_conserves
    _ = 25^12 := by decide

/-- Executable implementation of the existing structural mass report.
    The imported report is marked noncomputable despite its finite body. -/
def evalReport {good : Machine → Prop} {p : PartialMachine} :
    FrontierAudit good p → Nat × Nat
  | .certified p _ => (cylinderMass p,0)
  | .unresolved p => (0,cylinderMass p)
  | .branch _ _ _ kids =>
    (choices.attach.map (fun t => evalReport (kids t.val t.property))).foldl
      (fun acc x => (acc.1+x.1,acc.2+x.2)) (0,0)

theorem evalReport_eq {good : Machine → Prop} {p : PartialMachine}
    (a : FrontierAudit good p) : evalReport a = a.report := by
  induction a with
  | certified p cert => rfl
  | unresolved p => rfl
  | branch p s fresh kids ih =>
    simp only [evalReport,FrontierAudit.report]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t.val t.property

#print axioms evalReport_eq
#print axioms augment_open_subset
#print axioms depth4_exhaustive
#print axioms depth4_conserves
end BB6Coverage.FAR
