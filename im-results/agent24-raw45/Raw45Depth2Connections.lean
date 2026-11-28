import Raw45Depth2Parent124
import Raw45CutBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Depth2Connections
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay
namespace P124 := BB6.Agent24Raw45Depth2Parent124
namespace P96 := BB6.Agent24Raw45FullChild

def raw45 : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | _ => none

theorem root_query_B1 : zipQueryOK 119 raw45 6 (1,true) = true := by decide +kernel

def b1_1RE := refine raw45 (1,true) (some ⟨true,true,4⟩)
theorem b1_1RE_query_E1 : zipQueryOK 119 b1_1RE 7 (4,true) = true := by decide +kernel

theorem parent124_is_depth2 :
    P124.parent =
      refine b1_1RE (4,true) (some ⟨false,false,4⟩) := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

def b1_0LA := refine raw45 (1,true) (some ⟨false,false,0⟩)
theorem b1_0LA_query_A1 : zipQueryOK 119 b1_0LA 7 (0,true) = true := by decide +kernel

theorem exact96_parent_is_depth2 :
    P96.parent =
      refine b1_0LA (0,true) (some ⟨false,false,2⟩) := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

#print axioms root_query_B1
#print axioms b1_1RE_query_E1
#print axioms parent124_is_depth2
#print axioms exact96_parent_is_depth2
end BB6.Agent24Raw45Depth2Connections
