import Hybrid
import ZipThreeHoleAudit
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot

theorem read_of_run0 {p : PartialMachine} {n : Nat} {z : Z0}
    (h : run0 p n ⟨0,[],[]⟩ = some z) :
    (knownRun p n).map readSlot = some (z.q,z.l.headD false) := by
  have hh : (zrun p n BB6Coverage.Agent31Pump.start).map project = some z := (run_project p n _).trans h
  cases hz : zrun p n BB6Coverage.Agent31Pump.start with
  | none => simp [hz] at hh
  | some v =>
    have he : project v = z := by simpa [hz] using hh
    subst z
    simp [knownRun_zip,hz,read_embed,project]

theorem last_of_read (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hr : (knownRun p n).map readSlot = some s)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hh : p s = none) (hrest : restOK p s = true) (hw : weightOK p s n B = true) : Cover (WeightedBound B) p := by
  cases h : knownRun p n with
  | none => simp [h] at hr
  | some c =>
    have hs : readSlot c = s := by simpa [h] using hr
    apply Cover.leaf
    exact (WeightedTNFCertificate.lastHole hf (support6 p) (by decide) h
      (by simpa [hs] using hh) (by simpa [hs] using restOK_sound p s hrest)
      (by simpa [hs] using weightOK_sound p s n B hw)).sound

end BB6.Agent4E0OneLCLate
