import Raw122D90Join
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M90
theorem entry : run0 table 812 ⟨0,[],[]⟩ = some (family 0) := entryJ3

theorem growth (n : Nat) : run0 table 691 (family n) = some (family (n+1)) := growthJ2 n

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 812 (fun _ => 691) entry (by intro n; decide) growth m hm

#print axioms never
end M90
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
