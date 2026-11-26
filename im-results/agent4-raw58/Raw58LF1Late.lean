import Raw58LF1Compressed
import ZipThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF1Sweep
open BB6Coverage Agent31Pump
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

-- Literal computations in the compressed, source-proved sweep evaluator.
theorem eval86 : blankCompressed .v86 1193 = .hole 3055744 := by rfl
theorem eval109 : blankCompressed .v109 1193 = .hole 2298758 := by rfl
theorem eval122 : blankCompressed .v122 1193 = .hole 2295586 := by rfl

def queryTime : V → Nat
  | .v86 => 3055744
  | .v109 => 2298758
  | .v122 => 2295586

theorem readExact (v : V) :
    (run0 (table v) (queryTime v) ⟨0,[],[]⟩).map read0 = some (1,true) := by
  cases v
  · have h := blankCompressed_sound .v86 1193
    rw [eval86] at h
    exact h
  · have h := blankCompressed_sound .v109 1193
    rw [eval109] at h
    exact h
  · have h := blankCompressed_sound .v122 1193
    rw [eval122] at h
    exact h

theorem zipReadExact (v : V) :
    BB6Coverage.Agent10ZipAudit.zipRead (table v) (queryTime v) = some (1,true) := by
  have h := readExact v
  have hp := run_project (table v) (queryTime v) Agent31Pump.start
  change (Agent50Zipper.zrun (table v) (queryTime v) Agent31Pump.start).map project =
    run0 (table v) (queryTime v) ⟨0,[],[]⟩ at hp
  rw [← hp] at h
  unfold BB6Coverage.Agent10ZipAudit.zipRead
  cases hz : Agent50Zipper.zrun (table v) (queryTime v) Agent31Pump.start with
  | none => simp [hz] at h
  | some z => simpa only [hz, Option.map_some,read0,project] using h

-- The literal table is checked by tableOK at the consuming tree leaf.
-- The final-hole theorem of certifiedZip handles *every* completion.
theorem lastCheck (v : V) (B : Nat) (hB : queryTime v + 6 ≤ B) :
    zipCheck B (table v) (.last (queryTime v) (1,true)) = true := by
  have hw : weightOK (table v) (1,true) (queryTime v) B = true := by
    unfold weightOK
    apply List.all_eq_true.mpr
    intro d hd
    unfold possibleDelays at hd
    have hd6 := List.mem_range.mp (List.mem_filter.mp hd).1
    exact decide_eq_true (by omega)
  change (zipQueryOK B (table v) (queryTime v) (1,true) && restOK (table v) (1,true)) = true
  unfold zipQueryOK
  rw [zipReadExact v,hw]
  cases v <;> rfl

#print axioms readExact
#print axioms zipReadExact
#print axioms lastCheck
end BB6Coverage.Agent4LF1Sweep
