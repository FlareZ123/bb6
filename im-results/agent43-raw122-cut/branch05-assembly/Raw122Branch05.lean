import Raw122Kid05_00
import Raw122Kid05_01
import Raw122Kid05_02
import Raw122Kid05_03
import Raw122Kid05_04
import Raw122Kid05_05
import Raw122Kid05_06
import Raw122Kid05_07
import Raw122Kid05_08
import Raw122Kid05_09
import Raw122Kid05_10
import Raw122Kid05_11
import Raw122Kid05_12
import Raw122Kid05_13
import Raw122Kid05_14
import Raw122Kid05_15
import Raw122Kid05_16
import Raw122Kid05_17
import Raw122Kid05_18
import Raw122Kid05_19
import Raw122Kid05_20
import Raw122Kid05_21
import Raw122Kid05_22
import Raw122Kid05_23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def kids05 : Move → PartialAudit := byPartialMove [kid05_00,kid05_01,kid05_02,kid05_03,kid05_04,kid05_05,kid05_06,kid05_07,kid05_08,kid05_09,kid05_10,kid05_11,kid05_12,kid05_13,kid05_14,kid05_15,kid05_16,kid05_17,kid05_18,kid05_19,kid05_20,kid05_21,kid05_22,kid05_23]
theorem kids05_checked (mv : Move) :
    partialCheck 7014 (refine (child ⟨false,false,5⟩) (5,false) (some mv)) (kids05 mv) = true := by

  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact kid05_00_checked
  · exact kid05_06_checked
  · exact kid05_12_checked
  · exact kid05_18_checked
  · exact kid05_01_checked
  · exact kid05_07_checked
  · exact kid05_13_checked
  · exact kid05_19_checked
  · exact kid05_02_checked
  · exact kid05_08_checked
  · exact kid05_14_checked
  · exact kid05_20_checked
  · exact kid05_03_checked
  · exact kid05_09_checked
  · exact kid05_15_checked
  · exact kid05_21_checked
  · exact kid05_04_checked
  · exact kid05_10_checked
  · exact kid05_16_checked
  · exact kid05_22_checked
  · exact kid05_05_checked
  · exact kid05_11_checked
  · exact kid05_17_checked
  · exact kid05_23_checked
def branch05 : PartialAudit := .split 9 (5,false) kids05
theorem branch05_checked : partialCheck 7014 (child ⟨false,false,5⟩) branch05 = true := by
  change (zipQueryOK 7014 (child ⟨false,false,5⟩) 9 (5,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014
      (refine (child ⟨false,false,5⟩) (5,false) (some mv)) (kids05 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids05_checked⟩

end BB6.Agent43Raw122
