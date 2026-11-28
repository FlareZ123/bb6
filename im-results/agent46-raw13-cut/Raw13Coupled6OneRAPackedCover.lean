import Raw13Coupled6OneRAPacked
import Raw13Coupled6OneRACover
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy BB6.Agent13BlankDelay
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem packed_cover {out : PZ} (h : PackedOK ⟨0,0,0⟩ count out) (hq : out.q=5) (hl : out.l%2=0) : Cover (WeightedBound bound) p := by
  obtain ⟨w,hr,he⟩ := h (A [] []) rfl
  have hq' : w.q=5 := (congrArg PZ.q he).trans hq
  have hl' : w.l.headD false=false := by
    rw [←pack_head,show pack w.l=out.l from congrArg PZ.l he,hl]
    rfl
  exact cover_of_macro ⟨w,hr,zrefl w⟩ hq' hl' (by decide)

#print axioms packed_cover
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
