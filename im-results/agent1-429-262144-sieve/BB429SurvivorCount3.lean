import BB429SurvivorCount2

namespace BB429SurvivorMask
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Source-kernel exact surviving lift count in block 12. -/
theorem block_count12 : (survivorsAt 12).length = 10 := by decide

/-- Source-kernel exact surviving lift count in block 13. -/
theorem block_count13 : (survivorsAt 13).length = 17 := by decide

/-- Source-kernel exact surviving lift count in block 14. -/
theorem block_count14 : (survivorsAt 14).length = 13 := by decide

/-- Source-kernel exact surviving lift count in block 15. -/
theorem block_count15 : (survivorsAt 15).length = 13 := by decide
end BB429SurvivorMask
