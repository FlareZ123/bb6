import FastThreeHoleAudit
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit
namespace BB6.Agent6ChunkSupport
theorem firstHoleHaltCover (B : Nat) (p : PartialMachine) (s : Slot) (n : Nat)
 (h : queryOK B p n s = true) (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hb : n+6 ≤ B) :
 Cover (WeightedBound B) (refine p s none) := by
  obtain ⟨hr,hu,_⟩ := queryOK_sound h
  cases he : knownRun p n with
  | none => simp [he] at hr
  | some c =>
    have hs : readSlot c = s := by simpa [he] using hr
    have hh : p (readSlot c) = none := by rw [hs]; exact hu
    have hw : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0, d+n+1 ≤ B := by
      intro d hd
      have hd6 : d < 6 := by unfold possibleDelays at hd; exact List.mem_range.mp (List.mem_filter.mp hd).1
      omega
    apply Cover.leaf
    simpa only [hs] using first_hole_weighted_halt B p n c hf he hh hw
#print axioms firstHoleHaltCover
end BB6.Agent6ChunkSupport
