import OneLCSweep3158
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate.H3158Sweep
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent4E0OneLCLate

def halted : PartialMachine := refine p (5,true) none

theorem exactCover : Cover (WeightedBound 204887) p :=
  last_of_read 204887 p 204884 (5,true) read (by decide) (by decide) (by decide) (by decide)

theorem delaySet : possibleDelays halted 0 = [0,1,2] := by decide +kernel

theorem normalizedWitness : ∃ m : Machine, compatible halted m ∧ HaltsAfter m 204884 ∧ 2 ∈ delays (zeroNext m) 0 := by
  have hf : halted initialSlot = some (some ⟨true,true,1⟩) := by decide
  obtain ⟨m,hc,hd⟩ := possible_delay_realized halted 0 2 (firstOne_terminal halted hf) (by rw [delaySet]; decide)
  have hh : HaltsAfter m 204884 := by
    have hread := read
    cases hr : knownRun p 204884 with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = (5,true) := by simpa [hr] using hread
      exact first_hole_halts p 204884 c hr (by rw [hs]; decide) m (by simpa [halted,hs] using hc)
  exact ⟨m,hc,hh,hd⟩

theorem attained : ∃ m : Machine, HaltsAfter m 204886 := by
  obtain ⟨m,hc,hh,hd⟩ := normalizedWitness
  exact weighted_first_one_realized m 2 204884 (hc initialSlot _ (by decide)) hh hd

theorem noSmallerWeight (B : Nat) (h : Cover (WeightedBound B) p) : 204887 ≤ B := by
  obtain ⟨m,hc,hh,hd⟩ := normalizedWitness
  have hp : compatible p m := refine_preserves_compat p m (5,true) none (by decide) hc
  exact h.sound m hp 204884 2 hh hd
#print axioms exactCover
#print axioms attained
#print axioms noSmallerWeight
end BB6.Agent4E0OneLCLate.H3158Sweep
