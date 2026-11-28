import Raw45CutBase
import Raw45CutPart04
import Raw45CutPart05
import Raw45CutPart10
import Raw45CutPart11
import Raw45CutPart16
import Raw45CutPart17
import Raw45CutPart22
import Raw45CutPart23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45FullChild
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid00 : Audit :=
.cycle 0 9 false (3)

theorem kid00_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,false,0⟩)) kid00 = true := by decide +kernel



def kid01 : Audit :=
.cycle 17 1 false (-1)

theorem kid01_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,false,1⟩)) kid01 = true := by decide +kernel



def kid02 : Audit :=
.cycle 10 1 false (0)

theorem kid02_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,false,2⟩)) kid02 = true := by decide +kernel



def kid03 : Audit :=
.cycle 9 1 false (-1)

theorem kid03_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,false,3⟩)) kid03 = true := by decide +kernel



def kid06 : Audit :=
.cycle 0 12 true (0)

theorem kid06_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,true,0⟩)) kid06 = true := by decide +kernel



def kid07 : Audit :=
.cycle 1 11 true (0)

theorem kid07_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,true,1⟩)) kid07 = true := by decide +kernel



def kid08 : Audit :=
.cycle 10 1 false (2)

theorem kid08_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,true,2⟩)) kid08 = true := by decide +kernel



def kid09 : Audit :=
.cycle 9 1 false (1)

theorem kid09_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨false,true,3⟩)) kid09 = true := by decide +kernel



def kid12 : Audit :=
.cycle 13 1 false (-1)

theorem kid12_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,false,0⟩)) kid12 = true := by decide +kernel



def kid13 : Audit :=
.cycle 18 1 false (-2)

theorem kid13_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,false,1⟩)) kid13 = true := by decide +kernel



def kid14 : Audit :=
.cycle 1 13 true (-1)

theorem kid14_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,false,2⟩)) kid14 = true := by decide +kernel



def kid15 : Audit :=
.cycle 9 1 false (-1)

theorem kid15_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,false,3⟩)) kid15 = true := by decide +kernel



def kid18 : Audit :=
.cycle 0 12 true (0)

theorem kid18_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,true,0⟩)) kid18 = true := by decide +kernel



def kid19 : Audit :=
.cycle 1 11 true (0)

theorem kid19_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,true,1⟩)) kid19 = true := by decide +kernel



def kid20 : Audit :=
.cycle 16 1 false (0)

theorem kid20_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,true,2⟩)) kid20 = true := by decide +kernel



def kid21 : Audit :=
.cycle 14 1 false (0)

theorem kid21_checked :
  zipCheck 96 (refine parent (2,true) (some ⟨true,true,3⟩)) kid21 = true := by decide +kernel



def kids : Move → Audit := byMove [kid00,kid01,kid02,kid03,kid04,kid05,kid06,kid07,kid08,kid09,kid10,kid11,kid12,kid13,kid14,kid15,kid16,kid17,kid18,kid19,kid20,kid21,kid22,kid23]
def tree : Audit := .split 8 (2,true) kids

theorem kids_checked (mv : Move) :
  zipCheck 96 (refine parent (2,true) (some mv)) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact kid00_checked
  · exact kid06_checked
  · exact kid12_checked
  · exact kid18_checked
  · exact kid01_checked
  · exact kid07_checked
  · exact kid13_checked
  · exact kid19_checked
  · exact kid02_checked
  · exact kid08_checked
  · exact kid14_checked
  · exact kid20_checked
  · exact kid03_checked
  · exact kid09_checked
  · exact kid15_checked
  · exact kid21_checked
  · exact kid04_checked
  · exact kid10_checked
  · exact kid16_checked
  · exact kid22_checked
  · exact kid05_checked
  · exact kid11_checked
  · exact kid17_checked
  · exact kid23_checked

theorem checked : zipCheck 96 parent tree = true := by
  change (zipQueryOK 96 parent 8 (2,true) && allMoves (fun mv => zipCheck 96 (refine parent (2,true) (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide, allMoves_of _ kids_checked⟩

theorem weighted_bound (m : Machine) (hm : compatible parent m) : WeightedBound 96 m :=
  (certifiedZip 96 parent tree parent_root parent_nohalt checked).sound m hm

#print axioms checked

#print axioms weighted_bound


end BB6.Agent24Raw45FullChild
