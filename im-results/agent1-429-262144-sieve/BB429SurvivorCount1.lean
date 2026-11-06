import BB429SurvivorCount0

namespace BB429SurvivorMask
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Source-kernel exact surviving lift count in block 4. -/
theorem block_count4 : (survivorsAt 4).length = 14 := by decide

/-- Source-kernel exact surviving lift count in block 5. -/
theorem block_count5 : (survivorsAt 5).length = 17 := by decide

/-- Source-kernel exact surviving lift count in block 6. -/
theorem block_count6 : (survivorsAt 6).length = 16 := by decide

/-- Source-kernel exact surviving lift count in block 7. -/
theorem block_count7 : (survivorsAt 7).length = 17 := by decide
end BB429SurvivorMask
