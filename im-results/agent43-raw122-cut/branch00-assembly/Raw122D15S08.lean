import Raw122D15Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M15
theorem growthS3 (n : Nat) : run0 table 256 (growthC3 n) = some (growthC4 n) := by rfl

theorem growthS4 (n : Nat) : run0 table 110 (growthC4 n) = some (growthC5 n) := by rfl
end M15
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
