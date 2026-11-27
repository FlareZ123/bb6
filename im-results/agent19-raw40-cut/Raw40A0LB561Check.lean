import Raw40A0LB561
import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A0LB561
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay
open BB6Coverage.Agent10ZipAudit BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent50TNFPilot

theorem read_query : zipRead table 75493793 = some (4,false) := by
  have hz : (zrun table 75493793 start).map project = some ⟨4,false::U 12290,[]⟩ := (run_project table 75493793 start).trans query
  cases h : zrun table 75493793 start with
  | none => simp [h] at hz
  | some z =>
    have hq : project z = ⟨4,false::U 12290,[]⟩ := by simpa only [h,Option.map_some,Option.some.injEq] using hz
    have hq1 := congrArg Z0.q hq
    have hl := congrArg Z0.l hq
    change z.q = 4 at hq1
    change z.l = false::U 12290 at hl
    simp only [zipRead,h,Option.map_some,hq1,hl,List.headD_cons]

theorem checked (cut : Nat) : canonicalCheck 75493794 table cut (.closed .laste 75493793 (4,false)) = true) := by
  simp only  canonicalChec,pPrefilChec_eq,ziplChec,zipQquerOK, read_quer]
  decide +kernel

#print axiomsm checke
ende BB6.Agent19Raw40.A0LB561