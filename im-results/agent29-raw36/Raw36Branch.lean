import Raw36SymmetryCut
import Raw36Kid00
import Raw36Kid01
import Raw36Kid02
import Raw36Kid03
import Raw36Kid04
import Raw36Kid06
import Raw36Kid07
import Raw36Kid08
import Raw36Kid09
import Raw36Kid10
import Raw36Kid12
import Raw36Kid13
import Raw36Kid14
import Raw36Kid15
import Raw36Kid16
import Raw36Kid18
import Raw36Kid19
import Raw36Kid20
import Raw36Kid21
import Raw36Kid22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

theorem children_bound : ∀ mv ∈ representatives, ∀ m,
    compatible (child mv) m → WeightedBound 1022 m := by
  intro mv hmv m hm
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact kid00_bound m hm
  · exact kid06_bound m hm
  · exact kid12_bound m hm
  · exact kid18_bound m hm
  · exact kid01_bound m hm
  · exact kid07_bound m hm
  · exact kid13_bound m hm
  · exact kid19_bound m hm
  · exact kid02_bound m hm
  · exact kid08_bound m hm
  · exact kid14_bound m hm
  · exact kid20_bound m hm
  · exact kid03_bound m hm
  · exact kid09_bound m hm
  · exact kid15_bound m hm
  · exact kid21_bound m hm
  · exact kid04_bound m hm
  · exact kid10_bound m hm
  · exact kid16_bound m hm
  · exact kid22_bound m hm
  · exact False.elim ((by decide : (⟨false,false,5⟩ : Move) ∉ representatives) hmv)
  · exact False.elim ((by decide : (⟨false,true,5⟩ : Move) ∉ representatives) hmv)
  · exact False.elim ((by decide : (⟨true,false,5⟩ : Move) ∉ representatives) hmv)
  · exact False.elim ((by decide : (⟨true,true,5⟩ : Move) ∉ representatives) hmv)

theorem branch_bound (m : Machine) (hm : compatible branch m) : WeightedBound 1022 m :=
  branch_bound_from_twenty 1022 (by decide) children_bound m hm

theorem branch_cover : Cover (WeightedBound 1022) branch :=
  Cover.leaf branch branch_bound
#print axioms children_bound
#print axioms branch_bound
#print axioms branch_cover
end BB6.Agent29Raw36
