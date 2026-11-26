import Raw122D90Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M90
theorem growthS1 (n : Nat) : run0 table 256 (growthC1 n) = some (growthC2 n) := by rfl

theorem growthS2 (n : Nat) : run0 table 179 (growthC2 n) = some (growthC3 n) := by rfl
end M90
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
