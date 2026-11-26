import Raw122Kid16_00
import Raw122Kid16_01
import Raw122Kid16_02
import Raw122Kid16_03
import Raw122Kid16_04
import Raw122Kid16_05
import Raw122Kid16_06
import Raw122Kid16_07
import Raw122Kid16_08
import Raw122Kid16_09
import Raw122Kid16_10
import Raw122Kid16_11
import Raw122Kid16_12
import Raw122Kid16_13
import Raw122Kid16_14
import Raw122Kid16_15
import Raw122Kid16_16
import Raw122Kid16_17
import Raw122Kid16_18
import Raw122Kid16_19
import Raw122Kid16_20
import Raw122Kid16_21
import Raw122Kid16_22
import Raw122Kid16_23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit

def kids16 : Move → PartialAudit := byPartialMove [kid16_00,kid16_01,kid16_02,kid16_03,kid16_04,kid16_05,kid16_06,kid16_07,kid16_08,kid16_09,kid16_10,kid16_11,kid16_12,kid16_13,kid16_14,kid16_15,kid16_16,kid16_17,kid16_18,kid16_19,kid16_20,kid16_21,kid16_22,kid16_23]
theorem kids16_checked (mv : Move) :
    partialCheck 7014 (refine (child ⟨true,false,4⟩) (5,false) (some mv)) (kids16 mv) = true := by

  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact kid16_00_checked
  · exact kid16_06_checked
  · exact kid16_12_checked
  · exact kid16_18_checked
  · exact kid16_01_checked
  · exact kid16_07_checked
  · exact kid16_13_checked
  · exact kid16_19_checked
  · exact kid16_02_checked
  · exact kid16_08_checked
  · exact kid16_14_checked
  · exact kid16_20_checked
  · exact kid16_03_checked
  · exact kid16_09_checked
  · exact kid16_15_checked
  · exact kid16_21_checked
  · exact kid16_04_checked
  · exact kid16_10_checked
  · exact kid16_16_checked
  · exact kid16_22_checked
  · exact kid16_05_checked
  · exact kid16_11_checked
  · exact kid16_17_checked
  · exact kid16_23_checked
def branch16 : PartialAudit := .split 9 (5,false) kids16
theorem branch16_checked : partialCheck 7014 (child ⟨true,false,4⟩) branch16 = true := by
  change (zipQueryOK 7014 (child ⟨true,false,4⟩) 9 (5,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv => partialCheck 7014
      (refine (child ⟨true,false,4⟩) (5,false) (some mv)) (kids16 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids16_checked⟩

end BB6.Agent43Raw122
