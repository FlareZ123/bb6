import Raw122D104S00
import Raw122D104S01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M104
theorem entryJ0 : run0 table 256 (entryC0) = some (entryC1) := entryS0

theorem entryJ1 : run0 table 512 (entryC0) = some (entryC2) := @join0 table 256 256 (entryC0) (entryC1) (entryC2) (entryJ0) (entryS1)

theorem entryJ2 : run0 table 714 (entryC0) = some (entryC3) := @join0 table 512 202 (entryC0) (entryC2) (entryC3) (entryJ1) (entryS2)

theorem growthJ0 (n : Nat) : run0 table 256 (growthC0 n) = some (growthC1 n) := growthS0 n

theorem growthJ1 (n : Nat) : run0 table 512 (growthC0 n) = some (growthC2 n) := @join0 table 256 256 (growthC0 n) (growthC1 n) (growthC2 n) (growthJ0 n) (growthS1 n)

theorem growthJ2 (n : Nat) : run0 table 588 (growthC0 n) = some (growthC3 n) := @join0 table 512 76 (growthC0 n) (growthC2 n) (growthC3 n) (growthJ1 n) (growthS2 n)
end M104
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
