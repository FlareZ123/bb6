import Raw122D104Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M104
theorem entryS0 : run0 table 256 (entryC0) = some (entryC1) := by rfl

theorem entryS1 : run0 table 256 (entryC1) = some (entryC2) := by rfl

theorem entryS2 : run0 table 202 (entryC2) = some (entryC3) := by rfl

theorem growthS0 (n : Nat) : run0 table 256 (growthC0 n) = some (growthC1 n) := by rfl

theorem growthS1 (n : Nat) : run0 table 256 (growthC1 n) = some (growthC2 n) := by rfl
end M104
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
