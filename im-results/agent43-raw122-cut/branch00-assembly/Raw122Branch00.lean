import Raw122Kid00_00
import Raw122Kid00_01
import Raw122Kid00_02
import Raw122Kid00_03
import Raw122Kid00_04
import Raw122Kid00_05
import Raw122Kid00_06
import Raw122Kid00_07
import Raw122Kid00_08
import Raw122Kid00_09
import Raw122Kid00_10
import Raw122Kid00_11
import Raw122Kid00_12
import Raw122Kid00_13
import Raw122Kid00_14
import Raw122Kid00_15
import Raw122Kid00_16
import Raw122Kid00_17
import Raw122Kid00_18
import Raw122Kid00_19
import Raw122Kid00_20
import Raw122Kid00_21
import Raw122Kid00_22
import Raw122Kid00_23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def kids00 : Move → PartialAudit := byPartialMove [kid00_00,kid00_01,kid00_02,kid00_03,kid00_04,kid00_05,kid00_06,kid00_07,kid00_08,kid00_09,kid00_10,kid00_11,kid00_12,kid00_13,kid00_14,kid00_15,kid00_16,kid00_17,kid00_18,kid00_19,kid00_20,kid00_21,kid00_22,kid00_23]
theorem kids00_checked (mv : Move) :
    partialCheck 7014 (refine (child ⟨false,false,0⟩) (0,true) (some mv)) (kids00 mv) = true := by

  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact kid00_00_checked
  · exact kid00_06_checked
  · exact kid00_12_checked
  · exact kid00_18_checked
  · exact kid00_01_checked
  · exact kid00_07_checked
  · exact kid00_13_checked
  · exact kid00_19_checked
  · exact kid00_02_checked
  · exact kid00_08_checked
  · exact kid00_14_checked
  · exact kid00_20_checked
  · exact kid00_03_checked
  · exact kid00_09_checked
  · exact kid00_15_checked
  · exact kid00_21_checked
  · exact kid00_04_checked
  · exact kid00_10_checked
  · exact kid00_16_checked
  · exact kid00_22_checked
  · exact kid00_05_checked
  · exact kid00_11_checked
  · exact kid00_17_checked
  · exact kid00_23_checked
def branch00 : PartialAudit := .split 8 (0,true) kids00
theorem branch00_checked : partialCheck 7014 (child ⟨false,false,0⟩) branch00 = true := by
  change (zipQueryOK 7014 (child ⟨false,false,0⟩) 8 (0,true) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014
      (refine (child ⟨false,false,0⟩) (0,true) (some mv)) (kids00 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids00_checked⟩

end BB6.Agent43Raw122
