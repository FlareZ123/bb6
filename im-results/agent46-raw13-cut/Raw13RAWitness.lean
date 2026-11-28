import Raw13Coupled6OneRAPackedCover
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Agent50Zipper Raw13Coupled6OneRAHierarchy BB6.Agent13BlankDelay BB6.Agent50TNFPilot Agent10ZipAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_assigned_halt : weightedTNFNoAssignedHalt p := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem packed_halts {out : PZ} (h : PackedOK ⟨0,0,0⟩ count out) (hq : out.q=5) (hl : out.l%2=0) :
    HaltsAfter (weightedTNFDefaultCompletion p) count := by
  obtain ⟨w,hr,he⟩ := h (A [] []) rfl
  have hq' : w.q=5 := (congrArg PZ.q he).trans hq
  have hl' : w.l.headD false=false := by
    rw [←pack_head,show pack w.l=out.l from congrArg PZ.l he,hl]
    rfl
  have hz : (zrun p count start).map project = some w := (run_project p count start).trans hr
  apply (weightedTNF_halt_iff_firstHole p no_assigned_halt count).2
  cases hx : zrun p count start with
  | none => simp [hx] at hz
  | some z =>
    simp only [hx,Option.map_some,Option.some.injEq] at hz
    subst w
    have hs : readSlot (embed z)=hole := by
      rw [read_embed]
      exact Prod.ext hq' hl'
    have hk : BB6.Agent13BlankDelay.knownRun p count=some (embed z) := by rw [knownRun_zip,hx]; rfl
    exact ⟨embed z,hk,by rw [hs]; decide⟩
#print axioms packed_halts
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
