import Raw122D15Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M15
theorem entryS35 : run0 table 256 (entryC35) = some (entryC36) := by rfl

theorem entryS36 : run0 table 122 (entryC36) = some (entryC37) := by rfl

theorem growthS0 (n : Nat) : run0 table 256 (growthC0 n) = some (growthC1 n) := by rfl

theorem growthS1 (n : Nat) : run0 table 256 (growthC1 n) = some (growthC2 n) := by rfl

theorem growthS2 (n : Nat) : run0 table 256 (growthC2 n) = some (growthC3 n) := by rfl
end M15
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
