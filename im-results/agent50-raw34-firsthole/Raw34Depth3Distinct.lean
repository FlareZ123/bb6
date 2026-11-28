import Raw34Depth3All
import Raw34Depth2SideCycles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Depth3
open BB6Coverage

def signature (w : Witness) :=
  (w.first,w.secondSlot,w.second,w.thirdSlot,w.third)

/-- No repeated literal three-slot transition assignment in any of the 1206
    accepted depth-three cylinders. Distinct signatures imply their cylinders
    are pairwise disjoint, since each follows the exact first-blank-query tree.
-/
theorem distinct :
    (witnesses.map signature).Nodup := by decide

theorem no_first_level :
    witnesses.all (fun w =>
      !((BB6.Agent50Raw34Eleven.witnesses.map (·.move)).contains w.first)) = true := by
  decide

theorem no_second_level :
    witnesses.all (fun w =>
      !((BB6.Agent50Raw34Depth2.witnesses.map
        (fun z => (z.first,z.slot,z.second))).contains
          (w.first,w.secondSlot,w.second))) = true := by
  decide

#print axioms distinct
#print axioms no_first_level
#print axioms no_second_level
end BB6.Agent50Raw34Depth3
