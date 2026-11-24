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

#print axioms augment_open_subset
#print axioms depth4_exhaustive
#print axioms depth4_conserves
end BB6Coverage.FAR
