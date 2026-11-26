import Raw122Kid17_00
import Raw122Kid17_01
import Raw122Kid17_02
import Raw122Kid17_03
import Raw122Kid17_04
import Raw122Kid17_05
import Raw122Kid17_06
import Raw122Kid17_07
import Raw122Kid17_08
import Raw122Kid17_09
import Raw122Kid17_10
import Raw122Kid17_11
import Raw122Kid17_12
import Raw122Kid17_13
import Raw122Kid17_14
import Raw122Kid17_15
import Raw122Kid17_16
import Raw122Kid17_17
import Raw122Kid17_18
import Raw122Kid17_19
import Raw122Kid17_20
import Raw122Kid17_21
import Raw122Kid17_22
import Raw122Kid17_23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def kids17 : Move → PartialAudit := byPartialMove [kid17_00,kid17_01,kid17_02,kid17_03,kid17_04,kid17_05,kid17_06,kid17_07,kid17_08,kid17_09,kid17_10,kid17_11,kid17_12,kid17_13,kid17_14,kid17_15,kid17_16,kid17_17,kid17_18,kid17_19,kid17_20,kid17_21,kid17_22,kid17_23]
theorem kids17_checked (mv : Move) :
    partialCheck 7014 (refine (child ⟨true,false,5⟩) (5,false) (some mv)) (kids17 mv) = true := by

  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact kid17_00_checked
  · exact kid17_06_checked
  · exact kid17_12_checked
  · exact kid17_18_checked
  · exact kid17_01_checked
  · exact kid17_07_checked
  · exact kid17_13_checked
  · exact kid17_19_checked
  · exact kid17_02_checked
  · exact kid17_08_checked
  · exact kid17_14_checked
  · exact kid17_20_checked
  · exact kid17_03_checked
  · exact kid17_09_checked
  · exact kid17_15_checked
  · exact kid17_21_checked
  · exact kid17_04_checked
  · exact kid17_10_checked
  · exact kid17_16_checked
  · exact kid17_22_checked
  · exact kid17_05_checked
  · exact kid17_11_checked
  · exact kid17_17_checked
  · exact kid17_23_checked
def branch17 : PartialAudit := .split 9 (5,false) kids17
theorem branch17_checked : partialCheck 7014 (child ⟨true,false,5⟩) branch17 = true := by
  change (zipQueryOK 7014 (child ⟨true,false,5⟩) 9 (5,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014
      (refine (child ⟨true,false,5⟩) (5,false) (some mv)) (kids17 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids17_checked⟩

end BB6.Agent43Raw122
