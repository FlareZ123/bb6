import Raw112CarryRoot

namespace BB6Coverage.Agent31Pump.Raw112CarryRoot
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Raw115CounterBase Raw112CarrySweeps

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table family (fun _ => True) 0 trivial 382 entry
    (fun n _ => by obtain ⟨t,ht,h⟩ := growth n; exact ⟨n+1,t,trivial,ht,h⟩) m hm

#print axioms never
end BB6Coverage.Agent31Pump.Raw112CarryRoot
