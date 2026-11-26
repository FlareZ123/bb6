import Raw122D15Join
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M15
theorem entry : run0 table 9338 ⟨0,[],[]⟩ = some (family 0) := entryJ36

theorem growth (n : Nat) : run0 table 1134 (family n) = some (family (n+1)) := growthJ4 n

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9338 (fun _ => 1134) entry (by intro n; decide) growth m hm

#print axioms never
end M15
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
