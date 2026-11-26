import Raw122D104Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M104
theorem growthS2 (n : Nat) : run0 table 76 (growthC2 n) = some (growthC3 n) := by rfl
end M104
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
