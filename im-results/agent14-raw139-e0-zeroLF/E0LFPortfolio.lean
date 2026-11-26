import E0LFResidualCycles
import E0LFResidual10338
import E0LFResidual2040
import E0LFResidual9015
import E0LFResidual3002
import E0LFResidual4125
import E0LFResidual1307
import E0LF3863Packed

namespace BB6.Agent14E0LFPortfolio
open BB6Coverage

def closedRows : List PartialMachine := [
  BB6.Agent3E0LFResidual1307.ctr,
  BB6Coverage.Agent14E0LFResidual2040.ctr,
  BB6.Agent3E0LFResidual3002.ctr,
  BB6.Agent14E0LF3863.ctr,
  BB6.Agent14E0LFResidualCycles.p3864,
  BB6.Agent3E0LFResidual4125.ctr,
  BB6.Agent14E0LFResidualCycles.p4344,
  BB6.Agent14E0LFResidual9015.ctr,
  BB6Coverage.Agent14E0LFResidual10338.ctr,
  BB6.Agent14E0LFResidualCycles.p11287]

theorem closedRows_never (p : PartialMachine) (hp : p ∈ closedRows)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  simp only [closedRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h <;> subst p
  · exact BB6.Agent3E0LFResidual1307.never m hm
  · exact BB6Coverage.Agent14E0LFResidual2040.never m hm
  · exact BB6.Agent3E0LFResidual3002.never m hm
  · exact BB6.Agent14E0LF3863.never m hm
  · exact BB6.Agent14E0LFResidualCycles.never3864 m hm
  · exact BB6.Agent3E0LFResidual4125.never m hm
  · exact BB6.Agent14E0LFResidualCycles.never4344 m hm
  · exact BB6.Agent14E0LFResidual9015.never m hm
  · exact BB6Coverage.Agent14E0LFResidual10338.never m hm
  · exact BB6.Agent14E0LFResidualCycles.never11287 m hm

#print axioms closedRows_never
end BB6.Agent14E0LFPortfolio
