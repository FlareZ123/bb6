import Raw78Growth
namespace BB6.Agent8Raw78Growth
open BB6Coverage BB6Coverage.Agent31Pump
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 111 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent8Raw78Growth
