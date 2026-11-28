import D100Countdown
namespace BB6.Agent7D100Countdown
open BB6Coverage BB6Coverage.Agent31Pump

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 153 cost entry positive growth m hm

#print axioms never
end BB6.Agent7D100Countdown
