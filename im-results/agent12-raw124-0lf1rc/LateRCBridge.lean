import PackedRC
import Raw124FastAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12PackedRC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent8TNFPath

theorem bounded_of_query (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hread : (knownRun p n).map readSlot = some s)
    (hhole : p s = none) (hrest : restOK p s = true) (hw : weightOK p s n B = true) :
    ∀ m, compatible p m → WeightedBound B m := by
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = s := by simpa [hr] using hread
    exact last_hole_sound B p n c hroot hr
      (by simpa [hs] using hhole)
      (by simpa [hs] using restOK_sound p s hrest)
      (by simpa [hs] using weightOK_sound p s n B hw)
#print axioms bounded_of_query
end BB6.Agent12PackedRC
