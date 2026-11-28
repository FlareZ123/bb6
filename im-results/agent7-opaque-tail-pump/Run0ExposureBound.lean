import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100ExposureBridge
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit

/-- A source-level run0 prefix gives the exact slot queried by the original zipper. -/
theorem zipRead_of_run0 (p : PartialMachine) (n : Nat) (z0 : Z0)
    (h : run0 p n ⟨0,[],[]⟩ = some z0) :
    zipRead p n = some (z0.q,z0.l.headD false) := by
  have hp : (zrun p n start).map project = some z0 := (run_project p n start).trans h
  unfold zipRead
  cases hr : zrun p n start with
  | none => simp [hr] at hp
  | some z =>
    have he : project z = z0 := by simpa [hr] using hp
    exact congrArg (fun u : Z0 => some (u.q,u.l.headD false)) he

/-- Source-checked last-hole exposure bounds all completions: no unrelated
    CanonicalFrontier import or four-hole generated data are necessary. -/
theorem bounded_of_query (p : PartialMachine) (n B : Nat) (s : Slot)
    (hquery : zipRead p n = some s) (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (hhole : p s = none)
    (hweight : weightOK p s n B = true) (hrest : restOK p s = true)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  have h : zipCheck B p (.last n s) = true := by
    simp only [zipCheck,zipQueryOK,hquery,decide_true,Bool.true_and,hhole,hweight,hrest]
  exact (certifiedZip B p (.last n s) hroot hno h).sound m hm

#print axioms zipRead_of_run0
#print axioms bounded_of_query
end BB6.Agent7D100ExposureBridge
