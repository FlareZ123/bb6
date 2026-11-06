import BB429SurvivorCount1

namespace BB429SurvivorMask
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Source-kernel exact surviving lift count in block 8. -/
theorem block_count8 : (survivorsAt 8).length = 10 := by decide

/-- Source-kernel exact surviving lift count in block 9. -/
theorem block_count9 : (survivorsAt 9).length = 22 := by decide

/-- Source-kernel exact surviving lift count in block 10. -/
theorem block_count10 : (survivorsAt 10).length = 18 := by decide

/-- Source-kernel exact surviving lift count in block 11. -/
theorem block_count11 : (survivorsAt 11).length = 14 := by decide
end BB429SurvivorMask
