import ZipThreeHoleAudit
import CanonicalFrontier
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50CheckedLateHole
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent47CanonicalFrontier

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

theorem bounded_of_query (p : PartialMachine) (n B : Nat) (s : Slot)
    (hquery : zipRead p n = some s) (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (hhole : p s = none)
    (hweight : weightOK p s n B = true) (hrest : restOK p s = true)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  have h : zipCheck B p (.last n s) = true := by
    simp only [zipCheck,zipQueryOK,hquery,decide_true,Bool.true_and,hhole,hweight,hrest]
  exact (certifiedZip B p (.last n s) hroot hno h).sound m hm

theorem quotient_of_query (p : PartialMachine) (n B : Nat) (s : Slot)
    (hquery : zipRead p n = some s) (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (hhole : p s = none)
    (hweight : weightOK p s n B = true) (hrest : restOK p s = true)
    (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound B m :=
  quotientSafe hroot (bounded_of_query p n B s hquery hroot hno hhole hweight hrest) m hm

def haltCompletion (p : PartialMachine) : Machine := fun s => (p s).getD none

theorem haltCompletion_compatible (p : PartialMachine) : compatible p (haltCompletion p) := by
  intro s t h; simp [haltCompletion,h]

theorem exact_halt (p : PartialMachine) (n : Nat) (s : Slot)
    (hquery : zipRead p n = some s) (hhole : p s = none) : HaltsAfter (haltCompletion p) n := by
  have hq := hquery
  rw [zipRead_eq] at hq
  cases hr : knownRun p n with
  | none => simp [hr] at hq
  | some c =>
    have hs : readSlot c = s := by simpa [hr] using hq
    have hrun := knownRun_sound p (haltCompletion p) (haltCompletion_compatible p) n c hr
    constructor
    · rw [hrun]; rfl
    · rw [run,hrun]; change rawStep (haltCompletion p) c = none
      unfold rawStep haltCompletion
      rw [hs,hhole]; rfl

#print axioms zipRead_of_run0
#print axioms quotient_of_query
#print axioms exact_halt
end BB6.Agent50CheckedLateHole
