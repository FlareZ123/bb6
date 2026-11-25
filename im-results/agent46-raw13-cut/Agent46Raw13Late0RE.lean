import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Late0RE
open BB6Coverage Agent31Pump Agent50Zipper
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

theorem firstQuery : (run0 table 21268 ⟨0,[],[]⟩).map (fun z => (z.q,z.l.headD false)) = some (5,false) := by decide

theorem read_exact : zipRead table 21268 = some (5,false) := by
  have h := run_project table 21268 Agent31Pump.start
  change (zrun table 21268 Agent31Pump.start).map project = run0 table 21268 ⟨0,[],[]⟩ at h
  have hp := congrArg (fun o : Option Z0 => o.map (fun z => (z.q,z.l.headD false))) h
  rw [firstQuery] at hp
  have hmap : ((zrun table 21268 Agent31Pump.start).map project).map
      (fun z => (z.q,z.l.headD false)) = zipRead table 21268 := by
    unfold zipRead
    cases zrun table 21268 Agent31Pump.start <;> rfl
  exact hmap.symm.trans hp

theorem checked : zipCheck 21269 table (.last 21268 (5,false)) = true := by
  simp only [zipCheck, zipQueryOK, read_exact] <;> decide

theorem bound : ∀ m, compatible table m → WeightedBound 21269 m := by
  have hv : zipQueryOK 21269 table 21268 (5,false) = true ∧ restOK table (5,false) = true := by
    simpa only [zipCheck, Bool.and_eq_true] using checked
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
  cases hr : knownRun table 21268 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [hr] using hread
    exact last_hole_sound 21269 table 21268 c (by decide) hr
      (by simpa [hs] using hhole)
      (by simpa [hs] using restOK_sound table (5,false) hv.2)
      (by simpa [hs] using weightOK_sound table (5,false) 21268 21269 hw)

#print axioms firstQuery
#print axioms bound
end BB6Coverage.Agent31Pump.Raw13Late0RE
