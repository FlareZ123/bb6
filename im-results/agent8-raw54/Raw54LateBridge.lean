import Raw54Base
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54.LateBridge
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

theorem zipRead_of_run0 {p : PartialMachine} {n : Nat} {z : Z0}
    (h : run0 p n ⟨0,[],[]⟩ = some z) : zipRead p n = some (z.q,z.l.headD false) := by
  have hh : (zrun p n start).map project = some z := (run_project p n start).trans h
  unfold zipRead
  cases hz : zrun p n start with
  | none => simp [hz] at hh
  | some t =>
    have e : project t = z := by simpa [hz] using hh
    exact congrArg (fun w : Z0 => some (w.q,w.l.headD false)) e

theorem query_of_run0 {p : PartialMachine} {n B : Nat} {z : Z0} {s : Slot}
    (h : run0 p n ⟨0,[],[]⟩ = some z) (hs : (z.q,z.l.headD false) = s)
    (hu : p s = none) (hw : weightOK p s n B = true) : zipQueryOK B p n s = true := by
  rw [zipQueryOK, zipRead_of_run0 h, hs, hu, hw]
  simp

theorem halt_of_query {p : PartialMachine} {n B : Nat} {s : Slot}
    (h : zipQueryOK B p n s = true) (m : Machine) (hc : compatible (refine p s none) m) : HaltsAfter m n := by
  obtain ⟨hread,hhole,_⟩ := zipQueryOK_sound h
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = s := by simpa [hr] using hread
    exact first_hole_halts p n c hr (by simpa [hs] using hhole) m (by simpa [hs] using hc)

theorem query_mono {B C : Nat} {p : PartialMachine} {n : Nat} {s : Slot}
    (h : zipQueryOK B p n s = true) (hBC : B ≤ C) : zipQueryOK C p n s = true := by
  obtain ⟨hr,hu,hw⟩ := zipQueryOK_sound h
  rw [← zipRead_eq] at hr
  have hw' : weightOK p s n C = true := by
    apply List.all_eq_true.mpr
    intro d hd
    exact decide_eq_true (Nat.le_trans (weightOK_sound p s n B hw d hd) hBC)
  rw [zipQueryOK,hr,hu,hw']
  simp

theorem last_mono {B C : Nat} {p : PartialMachine} {n : Nat} {s : Slot}
    (h : zipCheck B p (.last n s) = true) (hBC : B ≤ C) : zipCheck C p (.last n s) = true := by
  have h' : zipQueryOK B p n s = true ∧ restOK p s = true := by
    simpa only [zipCheck, Bool.and_eq_true] using h
  have hnew : zipQueryOK C p n s = true ∧ restOK p s = true := ⟨query_mono h'.1 hBC,h'.2⟩
  simpa only [zipCheck, Bool.and_eq_true] using hnew

#print axioms query_of_run0
#print axioms halt_of_query
end BB6.Agent8Raw54.LateBridge
