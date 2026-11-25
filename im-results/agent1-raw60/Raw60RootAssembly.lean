import Raw60RootProgress
import Raw60A0RCData
import Raw60A0REData
import Raw60A0LBData
import Raw60A0RFData
import Raw60A1LAData
import Raw60A1LBData
import Raw60A1LCData
import Raw60A1RFData
import Raw60A0LDData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier

theorem parent_four_choices (m : Machine) (hm : compatible parent m) :
    WeightedBound 1175 m ∨ ∃ mv ∈ remaining4, compatible (child mv) m :=
  parent_reduced4 BB6.Agent1Raw60A0RC.all_closed
    BB6.Agent1Raw60A0RE.all_closed
    BB6.Agent1Raw60A0LB.all_closed
    BB6.Agent1Raw60A0RF.all_closed
    BB6.Agent1Raw60A1LA.all_closed
    BB6.Agent1Raw60A1LB.all_closed
    BB6.Agent1Raw60A1LC.all_closed
    BB6.Agent1Raw60A1RF.all_closed
    BB6.Agent1Raw60A0LD.all_closed m hm

theorem parent_scoreB (B : Nat) (hB : 1175 ≤ B)
    (tail : ∀ mv ∈ remaining5, ∀ m, compatible (child mv) m → WeightedBound B m)
    (m : Machine) (hm : compatible parent m) : WeightedBound B m := by
  rcases parent_five_choices m hm with hb | ⟨mv,hr,hc⟩
  · exact lift hB hb
  · exact tail mv hr m hc

#print axioms parent_five_choices
#print axioms parent_scoreB
end BB6.Agent1Raw60Root
