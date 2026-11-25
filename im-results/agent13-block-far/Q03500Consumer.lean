import BlockFARBridge
import Q03500Sweep

namespace BB6Q03500
def sourceTable : BB6Coverage.PartialMachine :=
  BB6BlockFAR.partialTable machine

theorem source_never (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible sourceTable m) :
    BB6Coverage.NeverHalts m :=
  BB6BlockFAR.transfer_never machine m hm never

theorem cover (B : Nat) :
    BB6Coverage.Cover (BB6Coverage.DecidedBelow B) sourceTable :=
  .leaf sourceTable (fun m hm => Or.inl (source_never m hm))

#print axioms source_never
#print axioms cover
end BB6Q03500
