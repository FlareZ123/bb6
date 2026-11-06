import BB429SurvivorBase

namespace BB429SurvivorMask
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Source-kernel exact surviving lift count in block 0. -/
theorem block_count0 : (survivorsAt 0).length = 25 := by decide

/-- Source-kernel exact surviving lift count in block 1. -/
theorem block_count1 : (survivorsAt 1).length = 15 := by decide

/-- Source-kernel exact surviving lift count in block 2. -/
theorem block_count2 : (survivorsAt 2).length = 9 := by decide

/-- Source-kernel exact surviving lift count in block 3. -/
theorem block_count3 : (survivorsAt 3).length = 25 := by decide
end BB429SurvivorMask
