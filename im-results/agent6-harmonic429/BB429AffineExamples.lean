import BB429AffineReplay

namespace BB429AffinePump

/-- The first reset phase is longer than the earlier manually located subphase. -/
theorem full26Phase : BB429.run 123541308 (0,402653204) = some (0,805306356) := by
  exact blockNext_sound ⟨27,4575604,22⟩ _ _ (by decide)

/-- Exact finite transfer across the successive 26, nested, +204, +112, +228,
    +136 and +252 phases, from the stated prepared accelerator configuration. -/
def exampleBlocks : List Block := [
  ⟨27,4575604,22⟩,
  ⟨29,1,0⟩,
  ⟨25,1458887,23⟩,
  ⟨56,657930,51⟩,
  ⟨27,1,0⟩,
  ⟨31,871543,28⟩,
  ⟨60,119477,57⟩,
  ⟨35,51540,34⟩,
  ⟨64,7005,63⟩,
  ⟨39,2762,40⟩
]

theorem example_transfer : BB429.run 233404010 (0,402653204) = some (0,1207812076) := by
  have h : total exampleBlocks = 233404010 := by decide
  rw [← h]
  exact replay_sound exampleBlocks _ _ (by decide)

/-- Correction to the earlier scan-only +136 phase: every cycle has 35 steps. -/
theorem return136_full : BB429.run 1803900 (0,1198595456) = some (0,1205604896) := by
  exact blockNext_sound ⟨35,51540,34⟩ _ _ (by decide)

#print axioms full26Phase
#print axioms example_transfer
#print axioms return136_full
end BB429AffinePump
