import Raw13Coupled6OneRAFast
import ZipAuditCore
import TNFPilot
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Agent50Zipper Raw13Coupled6OneRAHierarchy BB6.Agent13BlankDelay BB6.Agent50TNFPilot Agent10ZipAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def count : Nat := 44423003584937617011264491060
def hole : Slot := (5,false)
def bound : Nat := count+1

theorem cover_of_macro {n B : Nat} {out : Z0}
    (h : MacroOK (A [] []) n out) (hq : out.q=5) (hl : out.l.headD false=false)
    (hw : weightOK p hole n B=true) : Cover (WeightedBound B) p := by
  obtain ⟨w,hr,he⟩ := h
  have hz : (zrun p n start).map project = some w := (run_project p n start).trans hr
  cases hx : zrun p n start with
  | none => simp [hx] at hz
  | some z =>
    simp only [hx,Option.map_some,Option.some.injEq] at hz
    subst w
    have hs : readSlot (embed z)=hole := by
      rw [read_embed]
      have h1 := he.1.trans hq
      have h2 := (tape_head he.2.1).trans hl
      exact Prod.ext h1 h2
    have hk : BB6.Agent13BlankDelay.knownRun p n=some (embed z) := by rw [knownRun_zip,hx]; rfl
    refine .leaf p (last_hole_sound B p n (embed z) (by decide) hk ?_ ?_ ?_)
    · rw [hs]; rfl
    · rw [hs]; exact restOK_sound p hole (by decide)
    · rw [hs]; exact weightOK_sound p hole n B hw

theorem cover_of_replay (h : (replay 25611 (A [] [])).map (fun (n,z) => (n,z.q,z.l.headD false)) = some (count,5,false)) : Cover (WeightedBound bound) p := by
  cases hr : replay 25611 (A [] []) with
  | none => simp [hr] at h
  | some a =>
    obtain ⟨n,z⟩ := a
    simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,hq,hl⟩ := h
    exact cover_of_macro (replay_sound hr) hq hl (by decide)

#eval possibleDelays (refine p hole none) 0
#print axioms cover_of_replay
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
