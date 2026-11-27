import OneLCLateCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot

/-- Exact first-hole witnesses, including a realizable pre-first-one delay. -/
theorem last_witness (p : PartialMachine) (n d : Nat) (s : Slot)
    (hr : (knownRun p n).map readSlot = some s)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hu : p s = none) (hd : d ∈ possibleDelays (refine p s none) 0) :
    ∃ m : Machine, compatible p m ∧ HaltsAfter m n ∧ d ∈ delays (zeroNext m) 0 := by
  have hff := refine_preserves_firstOne p s none hu hf
  obtain ⟨m,hc,hdelay⟩ := possible_delay_realized (refine p s none) 0 d (firstOne_terminal _ hff) hd
  have hh : HaltsAfter m n := by
    cases h : knownRun p n with
    | none => simp [h] at hr
    | some c =>
      have hs : readSlot c = s := by simpa [h] using hr
      exact first_hole_halts p n c h (by simpa [hs] using hu) m (by simpa [hs] using hc)
  exact ⟨m,refine_preserves_compat p m s none hu hc,hh,hdelay⟩

/-- The exact local weighted bound of a last-hole leaf, if a maximizing delay
is realizable. Neither proof relies on numerical re-simulation of the run. -/
theorem exact_last (p : PartialMachine) (n d : Nat) (s : Slot)
    (hr : (knownRun p n).map readSlot = some s)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hu : p s = none) (hrest : restOK p s = true)
    (hd : d ∈ possibleDelays (refine p s none) 0)
    (hw : weightOK p s n (d+n+1) = true) :
    Cover (WeightedBound (d+n+1)) p ∧
    (∀ B, Cover (WeightedBound B) p → d+n+1 ≤ B) ∧
    (∃ m : Machine, HaltsAfter m (d+n)) := by
  refine ⟨last_of_read (d+n+1) p n s hr hf hu hrest hw, ?_, ?_⟩
  · intro B h
    obtain ⟨m,hc,hh,hdelay⟩ := last_witness p n d s hr hf hu hd
    exact h.sound m hc n d hh hdelay
  · obtain ⟨m,hc,hh,hdelay⟩ := last_witness p n d s hr hf hu hd
    exact weighted_first_one_realized m d n (hc initialSlot _ hf) hh hdelay
#print axioms exact_last
end BB6.Agent4E0OneLCLate
