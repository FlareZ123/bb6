import Raw58LF1Data
import Raw58LF1Kid00Weight
import Raw58LF1Kid01Weight
import Raw58LF1Kid02Weight
import Raw58LF1Kid03Weight
import Raw58LF1Kid04Weight
import Raw58LF1Kid05Weight
import Raw58LF1Kid06Weight
import Raw58LF1Kid07Weight
import Raw58LF1Kid08Weight
import Raw58LF1Kid09Weight
import Raw58LF1Kid10Weight
import Raw58LF1Kid11Weight
import Raw58LF1Kid12Weight
import Raw58LF1Kid13Weight
import Raw58LF1Kid14Weight
import Raw58LF1Kid15Weight
import Raw58LF1Kid16Weight
import Raw58LF1Kid17Weight
import Raw58LF1Kid18Weight
import Raw58LF1Kid19Weight
import Raw58LF1Kid20Weight
import Raw58LF1Kid21Weight
import Raw58LF1Kid22Weight
import Raw58LF1Kid23Weight
import ZipWeightTighten

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option profiler true
namespace BB6.Agent4Raw58LF1
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent4ZipWeightTighten

theorem kids_weights (mv : Move) : weights 3055746 (child mv) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact check00_weight
  · exact check06_weight
  · exact check12_weight
  · exact check18_weight
  · exact check01_weight
  · exact check07_weight
  · exact check13_weight
  · exact check19_weight
  · exact check02_weight
  · exact check08_weight
  · exact check14_weight
  · exact check20_weight
  · exact check03_weight
  · exact check09_weight
  · exact check15_weight
  · exact check21_weight
  · exact check04_weight
  · exact check10_weight
  · exact check16_weight
  · exact check22_weight
  · exact check05_weight
  · exact check11_weight
  · exact check17_weight
  · exact check23_weight

theorem weights_checked : weights 3055746 parent tree = true := by
  change (queryWeight 3055746 parent 8 (5,false) && allMoves (fun mv => weights 3055746 (child mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by rfl, allMoves_of _ kids_weights⟩

theorem tree_sharp : zipCheck 3055746 parent tree = true :=
  transfer 3055750 3055746 parent tree tree_checked weights_checked

theorem bound : ∀ m, compatible parent m → WeightedBound 3055746 m :=
  (certifiedZip 3055746 parent tree parent_root parent_nohalt tree_sharp).sound


#print axioms weights_checked
#print axioms bound
end BB6.Agent4Raw58LF1
