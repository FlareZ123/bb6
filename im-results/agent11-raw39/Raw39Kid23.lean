import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid23_part1 : Audit := .cycle 1 9 true (1)
theorem kid23_part1_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,0⟩)) (kid23_part1) = true := by rfl

def kid23_part2 : Audit := .cycle 7 2 true (3)
theorem kid23_part2_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,1⟩)) (kid23_part2) = true := by rfl

def kid23_part4 : Audit := .cycle 1 10 true (1)
theorem kid23_part4_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part4) = true := by rfl

def kid23_part5 : Audit := .cycle 1 12 true (1)
theorem kid23_part5_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part5) = true := by rfl

def kid23_part6 : Audit := .cycle 21 1 false (1)
theorem kid23_part6_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part6) = true := by rfl

def kid23_part7 : Audit := .cycle 0 11 true (0)
theorem kid23_part7_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part7) = true := by rfl

def kid23_part9 : Audit := .cycle 0 11 true (0)
theorem kid23_part9_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part9) = true := by rfl

def kid23_part10 : Audit := .cycle 1 10 true (1)
theorem kid23_part10_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part10) = true := by rfl

def kid23_part11 : Audit := .cycle 21 1 false (1)
theorem kid23_part11_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part11) = true := by rfl

def kid23_part12 : Audit := .cycle 1 13 true (0)
theorem kid23_part12_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part12) = true := by rfl

def kid23_part13 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 15 11 false (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 25 1 false (1),
.cycle 13 6 false (2),
.last 13 (5,true),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 15 3 false (0)
])
theorem kid23_part13_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part13) = true := by rfl

def kid23_part14 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (4),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 16 1 false (0),
.cycle 21 1 false (-3),
.cycle 19 1 false (-3),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 30 1 false (-2),
.cycle 1 13 false (4),
.cycle 25 1 false (-1),
.cycle 1 16 true (-1),
.cycle 13 1 true (-1),
.cycle 11 3 false (1)
])
theorem kid23_part14_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part14) = true := by rfl

def kid23_part15 : Audit := .cycle 0 11 true (0)
theorem kid23_part15_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part15) = true := by rfl

def kid23_part16 : Audit := .cycle 1 10 true (1)
theorem kid23_part16_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part16) = true := by rfl

def kid23_part17 : Audit := .split 19 (5,true) (byMove [
.cycle 1 32 true (0),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.cycle 7 15 true (0),
.cycle 0 23 true (0),
.cycle 24 1 false (0),
.cycle 1 20 true (0),
.last 23 (4,false),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 10 10 true (0),
.cycle 2 29 true (0),
.cycle 20 13 true (2),
.cycle 18 2 true (2),
.cycle 1 24 true (0),
.cycle 5 15 true (0),
.last 22 (4,false),
.cycle 24 1 false (0),
.cycle 1 20 true (0),
.cycle 1 31 true (0),
.cycle 2 28 true (0),
.cycle 0 21 true (0),
.last 29 (4,false),
.cycle 20 11 true (2)
])
theorem kid23_part17_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part17) = true := by rfl

def kid23_part18 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 27 1 false (3),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.last 39 (4,false),
.cycle 11 8 true (0),
.cycle 3 15 true (0),
.last 18 (4,false),
.cycle 2 17 true (0),
.cycle 31 1 false (3),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 1 19 true (0),
.cycle 0 20 true (0),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 1 20 true (0),
.last 18 (4,false),
.cycle 29 1 false (3)
])
theorem kid23_part18_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part18) = true := by rfl

def kid23_part19 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 11 1 true (3),
.last 21 (5,true),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 18 1 false (4),
.last 19 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 21 3 false (2)
])
theorem kid23_part19_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part19) = true := by rfl

def kid23_part20 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (0),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 33 1 false (3),
.cycle 24 1 false (0),
.cycle 0 20 true (0),
.last 43 (4,false),
.cycle 12 8 true (0),
.cycle 3 17 true (0),
.last 20 (4,false),
.cycle 2 19 true (0),
.cycle 37 1 false (3),
.cycle 18 2 true (2),
.cycle 24 1 false (2),
.cycle 1 21 true (0),
.last 22 (4,false),
.cycle 24 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 1 22 true (0),
.last 20 (4,false),
.cycle 35 1 false (3)
])
theorem kid23_part20_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part20) = true := by rfl

def kid23_part21 : Audit := .cycle 17 5 false (2)
theorem kid23_part21_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part21) = true := by rfl

def kid23_part22 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (0),
.last 19 (4,false),
.last 17 (4,false),
.cycle 0 17 true (0),
.cycle 16 3 false (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 9 18 true (0),
.cycle 14 8 true (0),
.cycle 22 3 false (2),
.last 16 (4,false),
.cycle 24 3 false (2),
.cycle 19 3 false (1),
.cycle 14 2 true (0),
.last 17 (4,false),
.cycle 1 17 true (0),
.cycle 16 3 false (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 17 3 false (1)
])
theorem kid23_part22_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part22) = true := by rfl

def kid23_part23 : Audit := .cycle 0 13 true (0)
theorem kid23_part23_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part23) = true := by rfl

def kid23_part24 : Audit := .cycle 18 1 false (0)
theorem kid23_part24_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part24) = true := by rfl

def kid23_part25 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.last 91 (5,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 1 15 true (1),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 19 (5,true),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid23_part25_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part25) = true := by rfl

def kid23_part26 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (5,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 19 1 false (1),
.cycle 16 1 false (0),
.cycle 21 1 false (-3),
.cycle 19 1 false (-3),
.last 20 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (5,true),
.cycle 0 17 true (-1),
.last 20 (5,true),
.last 20 (5,true),
.last 17 (5,true),
.cycle 11 3 false (1)
])
theorem kid23_part26_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part26) = true := by rfl

def kid23_part27 : Audit := .cycle 0 11 true (0)
theorem kid23_part27_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part27) = true := by rfl

def kid23_part28 : Audit := .cycle 1 10 true (1)
theorem kid23_part28_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part28) = true := by rfl

def kid23_part29 : Audit := .cycle 2 9 true (1)
theorem kid23_part29_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part29) = true := by rfl

def kid23_part30 : Audit := .cycle 1 13 true (1)
theorem kid23_part30_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part30) = true := by rfl

def kid23_part31 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 15 15 false (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 13 10 true (-2),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2)
])
theorem kid23_part31_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part31) = true := by rfl

def kid23_part32 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 15 13 false (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 29 1 false (1),
.cycle 15 8 false (2),
.last 15 (5,true),
.cycle 0 28 true (-2),
.cycle 1 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 17 3 false (1)
])
theorem kid23_part32_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part32) = true := by rfl

def kid23_part8 : Audit := .split 10 (4,true) (byMove [(kid23_part9),(kid23_part10),(kid23_part11),(kid23_part12),(kid23_part13),(kid23_part14),(kid23_part15),(kid23_part16),(kid23_part17),(kid23_part18),(kid23_part19),(kid23_part20),(kid23_part21),(kid23_part22),(kid23_part23),(kid23_part24),(kid23_part25),(kid23_part26),(kid23_part27),(kid23_part28),(kid23_part29),(kid23_part30),(kid23_part31),(kid23_part32)])

theorem kid23_part8_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part8) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part9),(kid23_part10),(kid23_part11),(kid23_part12),(kid23_part13),(kid23_part14),(kid23_part15),(kid23_part16),(kid23_part17),(kid23_part18),(kid23_part19),(kid23_part20),(kid23_part21),(kid23_part22),(kid23_part23),(kid23_part24),(kid23_part25),(kid23_part26),(kid23_part27),(kid23_part28),(kid23_part29),(kid23_part30),(kid23_part31),(kid23_part32)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part9_checked

  · exact kid23_part15_checked

  · exact kid23_part21_checked

  · exact kid23_part27_checked

  · exact kid23_part10_checked

  · exact kid23_part16_checked

  · exact kid23_part22_checked

  · exact kid23_part28_checked

  · exact kid23_part11_checked

  · exact kid23_part17_checked

  · exact kid23_part23_checked

  · exact kid23_part29_checked

  · exact kid23_part12_checked

  · exact kid23_part18_checked

  · exact kid23_part24_checked

  · exact kid23_part30_checked

  · exact kid23_part13_checked

  · exact kid23_part19_checked

  · exact kid23_part25_checked

  · exact kid23_part31_checked

  · exact kid23_part14_checked

  · exact kid23_part20_checked

  · exact kid23_part26_checked

  · exact kid23_part32_checked

def kid23_part33 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 16 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,true),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 25 1 false (1),
.cycle 13 6 false (2),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 16 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 20 1 false (-2)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (3),
.cycle 3 15 true (0),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 19 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (4,true),
.last 20 (4,true),
.cycle 11 1 true (3),
.last 22 (4,true),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 4 15 true (0),
.last 14 (4,true),
.cycle 27 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 29 1 false (1)
]),
.cycle 2 19 true (0),
.cycle 17 5 false (2),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 16 1 false (-2),
.cycle 1 12 true (1),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 16 1 false (-2),
.cycle 1 12 true (1),
.last 16 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 10 3 true (2),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2)
]),
.cycle 17 1 false (-1)
])
theorem kid23_part33_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part33) = true := by rfl

def kid23_part34 : Audit := .cycle 0 10 true (0)
theorem kid23_part34_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part34) = true := by rfl

def kid23_part35 : Audit := .cycle 1 9 true (1)
theorem kid23_part35_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part35) = true := by rfl

def kid23_part36 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 9 9 true (2),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 37 1 false (3),
.cycle 33 1 false (3),
.cycle 0 20 true (0),
.last 20 (4,false),
.last 20 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 9 true (2),
.cycle 3 16 true (1),
.last 19 (4,false),
.cycle 2 18 true (1),
.cycle 6 13 true (2),
.cycle 9 14 true (2),
.cycle 53 1 false (9),
.cycle 1 20 true (1),
.last 20 (4,false),
.last 20 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (2)
]),
.cycle 41 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 8 true (2),
.cycle 3 15 true (1),
.split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 28 (4,true),
.cycle 11 8 true (2),
.cycle 18 1 true (6),
.cycle 10 10 true (2),
.cycle 7 13 true (2),
.cycle 9 11 true (2),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (4,true),
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.last 30 (4,true)
]),
.cycle 2 17 true (1),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 64, 47, 64],[2, 32, 4, 1, 64, 5, 64],80⟩,
.cycle 1 19 true (1),
.split 18 (4,true) (byMove [
.cycle 9 12 true (2),
.cycle 0 24 true (0),
.cycle 0 22 true (0),
.cycle 7 14 true (2),
.last 20 (4,false),
.last 20 (4,false),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 2048, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 2, 4096, 128, 2048, 4, 1, 2, 2048, 4096],5136⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 2052, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 0 20 true (0),
.last 20 (4,false),
.last 20 (4,false),
.cycle 15 4 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 2052, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 43 1 false (9),
.cycle 5 14 true (1),
.last 20 (4,false),
.last 20 (4,false),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 9 10 true (2),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 17 2 true (4)
]),
.cycle 32 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.split 18 (4,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 9 10 true (2),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 9 true (2),
.cycle 3 16 true (1),
.cycle 18 1 true (6),
.cycle 2 18 true (1),
.cycle 6 13 true (2),
.cycle 16 3 true (4),
.last 30 (4,true),
.cycle 1 20 true (1),
.last 19 (4,true),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (2)
]),
.cycle 8 10 true (2)
])
theorem kid23_part36_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part36) = true := by rfl

def kid23_part37 : Audit := .cycle 3 7 true (1)
theorem kid23_part37_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part37) = true := by rfl

def kid23_part38 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 17 1 false (1),
.last 21 (5,true),
.cycle 21 7 false (2),
.last 19 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 21 1 false (1)
]),
.cycle 29 1 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (5,true) (byMove [
.cycle 9 13 true (2),
.last 42 (4,true),
.last 38 (4,true),
.cycle 7 15 true (2),
.last 20 (4,true),
.cycle 45 1 false (1),
.cycle 1 20 true (1),
.cycle 1 35 true (1),
.last 33 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 2 29 true (1),
.cycle 6 17 true (2),
.cycle 18 2 true (4),
.last 21 (4,true),
.cycle 5 15 true (1),
.last 20 (4,true),
.cycle 34 1 false (0),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 9 11 true (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 8 13 true (2)
]),
.split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 9 9 true (2),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 41 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 11 8 true (2),
.cycle 3 15 true (1),
.cycle 10 8 true (2),
.cycle 2 17 true (1),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.last 19 (4,true),
.cycle 1 19 true (1),
.last 18 (4,true),
.cycle 32 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 8 10 true (2)
]),
.cycle 10 1 true (4),
.split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 9 11 true (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 45 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (2),
.cycle 3 17 true (1),
.cycle 10 10 true (2),
.cycle 2 19 true (1),
.cycle 6 14 true (2),
.cycle 18 2 true (4),
.last 21 (4,true),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 34 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.cycle 8 12 true (2)
]),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.last 19 (5,true),
.cycle 1 21 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 25 (5,true),
.cycle 1 14 true (1),
.cycle 26 1 false (6),
.last 13 (5,true),
.last 15 (5,true),
.last 25 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 13 3 true (3),
.last 13 (5,true)
]),
.split 21 (5,true) (byMove [
.cycle 37 1 false (1),
.cycle 31 1 false (1),
.cycle 29 1 false (1),
.cycle 7 17 true (0),
.last 22 (4,true),
.cycle 26 1 false (0),
.cycle 1 22 true (0),
.cycle 32 24 true (4),
.cycle 26 8 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 2 31 true (0),
.cycle 41 1 false (1),
.cycle 20 2 true (2),
.last 23 (4,true),
.cycle 5 17 true (0),
.last 22 (4,true),
.cycle 26 1 false (0),
.cycle 1 22 true (0),
.cycle 37 1 false (1),
.cycle 35 1 false (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 37 1 false (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 8 3 true (3)
])
theorem kid23_part38_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part38) = true := by rfl

def kid23_part39 : Audit := .cycle 2 9 true (1)
theorem kid23_part39_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part39) = true := by rfl

def kid23_part40 : Audit := .cycle 6 4 true (2)
theorem kid23_part40_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part40) = true := by rfl

def kid23_part41 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 21 7 false (1),
.cycle 17 5 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 25 true (0),
.cycle 31 1 false (3),
.last 13 (4,false),
.cycle 37 1 false (3),
.cycle 21 7 false (2),
.cycle 18 5 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 21 7 false (1)
]),
.cycle 22 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 8 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 21 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 10 8 true (2),
.cycle 12 1 true (4),
.cycle 10 10 true (2),
.cycle 7 7 true (2),
.cycle 9 5 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.cycle 21 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 7 true (2)
]),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 17 5 false (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 14 6 true (1),
.cycle 0 16 true (0),
.cycle 28 1 false (0),
.cycle 29 1 false (1),
.last 13 (4,false),
.cycle 22 1 false (-2),
.cycle 1 13 true (1),
.cycle 9 8 true (2),
.cycle 9 6 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 14 4 true (1),
.cycle 18 5 false (1),
.cycle 1 15 true (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 22 1 false (-2),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 11 2 true (2)
]),
.cycle 22 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 9 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.last 16 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (2)
]),
.cycle 8 4 true (2)
])
theorem kid23_part41_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part41) = true := by rfl

def kid23_part42 : Audit := .cycle 1 13 true (1)
theorem kid23_part42_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part42) = true := by rfl

def kid23_part43 : Audit := .cycle 1 11 true (1)
theorem kid23_part43_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part43) = true := by rfl

def kid23_part45 : Audit := .cycle 12 4 true (1)
theorem kid23_part45_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part45) = true := by rfl

def kid23_part46 : Audit := .cycle 0 14 true (0)
theorem kid23_part46_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part46) = true := by rfl

def kid23_part47 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.last 20 (4,false),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.last 39 (4,false),
.cycle 12 8 true (0),
.cycle 3 15 true (0),
.last 18 (4,false),
.cycle 2 17 true (0),
.last 24 (4,false),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 1 19 true (0),
.last 20 (4,false),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 1 20 true (0),
.last 18 (4,false),
.last 22 (4,false)
])
theorem kid23_part47_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part47) = true := by rfl

def kid23_part48 : Audit := .cycle 23 1 false (1)
theorem kid23_part48_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part48) = true := by rfl

def kid23_part49 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 24 false (4),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 9 4 true (1),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 14 1 true (2),
.last 19 (5,true),
.cycle 13 6 false (2),
.last 13 (5,true),
.cycle 17 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 24 true (-1),
.last 25 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.last 19 (5,true)
])
theorem kid23_part49_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part49) = true := by rfl

def kid23_part50 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.last 21 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 18 true (-1),
.cycle 11 4 true (-1),
.cycle 12 2 true (-1),
.last 19 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 19 1 false (-3),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 18 true (-1),
.cycle 20 1 false (-2),
.cycle 18 1 false (-2),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid23_part50_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part50) = true := by rfl

def kid23_part51 : Audit := .cycle 1 11 true (1)
theorem kid23_part51_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part51) = true := by rfl

def kid23_part52 : Audit := .split 14 (4,false) (byMove [
.cycle 16 8 true (1),
.cycle 0 18 true (0),
.last 21 (5,true),
.cycle 35 1 false (1),
.cycle 0 20 true (0),
.cycle 20 1 false (-2),
.cycle 1 15 true (1),
.cycle 11 4 true (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.cycle 1 17 true (1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 20 1 false (-2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 9 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 15 (5,true)
])
theorem kid23_part52_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part52) = true := by rfl

def kid23_part53 : Audit := .split 12 (4,false) (byMove [
.cycle 14 6 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 29 1 false (1),
.cycle 16 1 false (2),
.cycle 18 1 false (-2),
.cycle 1 13 true (1),
.cycle 11 4 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 23 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.cycle 16 1 false (0),
.cycle 18 1 false (-2),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 13 (5,true)
])
theorem kid23_part53_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part53) = true := by rfl

def kid23_part54 : Audit := .cycle 0 12 true (0)
theorem kid23_part54_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part54) = true := by rfl

def kid23_part55 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 17 1 false (1),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 12 1 true (4),
.last 23 (5,true),
.cycle 7 7 true (2),
.cycle 9 5 true (2),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (5),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 16 (5,true)
])
theorem kid23_part55_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part55) = true := by rfl

def kid23_part56 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,false),
.cycle 0 21 true (0),
.last 12 (4,false),
.cycle 2 31 true (0),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 1 19 true (0),
.last 12 (4,false),
.cycle 24 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 14 (4,false)
])
theorem kid23_part56_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part56) = true := by rfl

def kid23_part57 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 17 5 false (2),
.cycle 0 15 true (0),
.cycle 21 9 false (2),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 2 13 true (1),
.cycle 12 8 true (1),
.cycle 12 2 true (2),
.cycle 17 5 false (2),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 12 6 true (1)
])
theorem kid23_part57_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part57) = true := by rfl

def kid23_part58 : Audit := .split 15 (5,true) (byMove [
.cycle 11 6 true (0),
.last 19 (4,false),
.last 17 (4,false),
.cycle 0 21 true (0),
.cycle 16 3 false (0),
.cycle 19 1 false (-1),
.cycle 6 10 true (0),
.last 41 (4,false),
.last 17 (4,false),
.cycle 1 17 true (0),
.cycle 10 6 true (0),
.cycle 2 37 true (0),
.cycle 17 10 true (1),
.cycle 14 2 true (0),
.last 17 (4,false),
.cycle 1 21 true (0),
.cycle 16 3 false (0),
.cycle 19 1 false (-1),
.cycle 1 23 true (0),
.cycle 1 17 true (0),
.cycle 12 4 true (0),
.cycle 1 17 true (0),
.last 22 (4,false),
.cycle 16 6 true (1)
])
theorem kid23_part58_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part58) = true := by rfl

def kid23_part59 : Audit := .cycle 1 13 true (1)
theorem kid23_part59_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part59) = true := by rfl

def kid23_part60 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 1 18 true (0),
.cycle 20 1 false (0),
.cycle 0 16 true (0),
.last 35 (4,false),
.cycle 11 8 true (0),
.cycle 3 13 true (0),
.last 16 (4,false),
.cycle 2 15 true (0),
.cycle 27 1 false (1),
.cycle 14 2 true (2),
.cycle 18 1 false (0),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 25 1 false (1)
])
theorem kid23_part60_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part60) = true := by rfl

def kid23_part61 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.last 21 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.last 13 (5,true),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 22 (5,true),
.last 13 (5,true),
.cycle 14 3 false (0),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid23_part61_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part61) = true := by rfl

def kid23_part62 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.last 19 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (5,true),
.cycle 11 4 true (-1),
.cycle 12 2 true (-1),
.last 17 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 19 1 false (-3),
.last 20 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (5,true),
.cycle 20 1 false (-2),
.cycle 18 1 false (-2),
.last 17 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid23_part62_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part62) = true := by rfl

def kid23_part63 : Audit := .cycle 1 11 true (1)
theorem kid23_part63_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part63) = true := by rfl

def kid23_part64 : Audit := .cycle 7 4 true (2)
theorem kid23_part64_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part64) = true := by rfl

def kid23_part65 : Audit := .cycle 9 2 true (2)
theorem kid23_part65_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part65) = true := by rfl

def kid23_part66 : Audit := .cycle 0 12 true (0)
theorem kid23_part66_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part66) = true := by rfl

def kid23_part67 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 10 5 true (2),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (2)
])
theorem kid23_part67_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part67) = true := by rfl

def kid23_part68 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.last 15 (4,false),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 13 (4,false),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (2)
])
theorem kid23_part68_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part68) = true := by rfl

def kid23_part44 : Audit := .split 10 (4,true) (byMove [(kid23_part45),(kid23_part46),(kid23_part47),(kid23_part48),(kid23_part49),(kid23_part50),(kid23_part51),(kid23_part52),(kid23_part53),(kid23_part54),(kid23_part55),(kid23_part56),(kid23_part57),(kid23_part58),(kid23_part59),(kid23_part60),(kid23_part61),(kid23_part62),(kid23_part63),(kid23_part64),(kid23_part65),(kid23_part66),(kid23_part67),(kid23_part68)])

theorem kid23_part44_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part44) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part45),(kid23_part46),(kid23_part47),(kid23_part48),(kid23_part49),(kid23_part50),(kid23_part51),(kid23_part52),(kid23_part53),(kid23_part54),(kid23_part55),(kid23_part56),(kid23_part57),(kid23_part58),(kid23_part59),(kid23_part60),(kid23_part61),(kid23_part62),(kid23_part63),(kid23_part64),(kid23_part65),(kid23_part66),(kid23_part67),(kid23_part68)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part45_checked

  · exact kid23_part51_checked

  · exact kid23_part57_checked

  · exact kid23_part63_checked

  · exact kid23_part46_checked

  · exact kid23_part52_checked

  · exact kid23_part58_checked

  · exact kid23_part64_checked

  · exact kid23_part47_checked

  · exact kid23_part53_checked

  · exact kid23_part59_checked

  · exact kid23_part65_checked

  · exact kid23_part48_checked

  · exact kid23_part54_checked

  · exact kid23_part60_checked

  · exact kid23_part66_checked

  · exact kid23_part49_checked

  · exact kid23_part55_checked

  · exact kid23_part61_checked

  · exact kid23_part67_checked

  · exact kid23_part50_checked

  · exact kid23_part56_checked

  · exact kid23_part62_checked

  · exact kid23_part68_checked

def kid23_part69 : Audit := .split 10 (5,true) (byMove [
.cycle 12 4 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.cycle 16 1 false (-2),
.cycle 7 6 true (1),
.cycle 9 4 true (1),
.cycle 0 14 true (0),
.last 18 (4,true),
.last 13 (4,true),
.last 20 (4,true),
.cycle 13 6 false (2),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.cycle 16 1 false (-2),
.last 17 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 20 1 false (-2)
]),
.cycle 15 1 false (-1),
.cycle 1 11 true (1),
.cycle 9 53 true (0),
.cycle 14 8 true (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 32 (4,false),
.last 28 (4,false),
.last 12 (4,false),
.last 32 (4,false),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.last 18 (4,false),
.last 12 (4,false),
.last 20 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 22 (4,false)
]),
.cycle 2 31 true (0),
.cycle 12 8 true (1),
.cycle 13 2 true (0),
.cycle 1 13 true (1),
.cycle 1 17 true (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 16 1 false (-2),
.cycle 6 6 true (1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 16 1 false (-2),
.last 17 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 9 2 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (2)
]),
.cycle 8 4 true (2)
])
theorem kid23_part69_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part69) = true := by rfl

def kid23_part70 : Audit := .cycle 0 10 true (0)
theorem kid23_part70_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part70) = true := by rfl

def kid23_part71 : Audit := .cycle 1 9 true (1)
theorem kid23_part71_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part71) = true := by rfl

def kid23_part72 : Audit := .cycle 2 8 true (1)
theorem kid23_part72_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part72) = true := by rfl

def kid23_part73 : Audit := .cycle 1 12 true (1)
theorem kid23_part73_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part73) = true := by rfl

def kid23_part75 : Audit := .cycle 1 11 true (1)
theorem kid23_part75_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part75) = true := by rfl

def kid23_part76 : Audit := .cycle 7 4 true (3)
theorem kid23_part76_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part76) = true := by rfl

def kid23_part77 : Audit := .cycle 9 2 true (3)
theorem kid23_part77_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part77) = true := by rfl

def kid23_part78 : Audit := .cycle 0 12 true (0)
theorem kid23_part78_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part78) = true := by rfl

def kid23_part79 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 11 2 true (2),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part79_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part79) = true := by rfl

def kid23_part80 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.cycle 37 1 false (1),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part80_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part80) = true := by rfl

def kid23_part81 : Audit := .cycle 0 11 true (0)
theorem kid23_part81_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part81) = true := by rfl

def kid23_part82 : Audit := .cycle 1 10 true (1)
theorem kid23_part82_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part82) = true := by rfl

def kid23_part83 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 9 10 true (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 69 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.last 29 (4,true),
.cycle 2 18 true (1),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 20 (4,true),
.cycle 1 20 true (1),
.last 19 (4,true),
.last 25 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 10 9 true (3),
.cycle 8 11 true (3)
])
theorem kid23_part83_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part83) = true := by rfl

def kid23_part84 : Audit := .cycle 3 8 true (1)
theorem kid23_part84_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part84) = true := by rfl

def kid23_part85 : Audit := .cycle 10 1 true (4)
theorem kid23_part85_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part85) = true := by rfl

def kid23_part86 : Audit := .cycle 2 10 true (1)
theorem kid23_part86_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part86) = true := by rfl

def kid23_part87 : Audit := .cycle 6 5 true (2)
theorem kid23_part87_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part87) = true := by rfl

def kid23_part88 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 9 4 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 23 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 9 6 true (3),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 23 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 8 5 true (3)
])
theorem kid23_part88_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part88) = true := by rfl

def kid23_part89 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 9 4 true (3),
.cycle 0 14 true (0),
.cycle 0 22 true (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 24 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 8 5 true (3)
])
theorem kid23_part89_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part89) = true := by rfl

def kid23_part90 : Audit := .cycle 1 12 true (1)
theorem kid23_part90_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part90) = true := by rfl

def kid23_part91 : Audit := .split 11 (4,true) (byMove [
.cycle 9 5 true (2),
.cycle 1 20 true (1),
.last 21 (5,true),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 11 2 true (2),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.last 12 (5,true)
])
theorem kid23_part91_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part91) = true := by rfl

def kid23_part92 : Audit := .split 11 (5,true) (byMove [
.cycle 9 5 true (2),
.cycle 1 20 true (1),
.cycle 29 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 21 true (1),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 5 true (3)
])
theorem kid23_part92_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part92) = true := by rfl

def kid23_part93 : Audit := .cycle 0 11 true (0)
theorem kid23_part93_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part93) = true := by rfl

def kid23_part94 : Audit := .cycle 1 10 true (1)
theorem kid23_part94_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part94) = true := by rfl

def kid23_part95 : Audit := .cycle 2 9 true (1)
theorem kid23_part95_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part95) = true := by rfl

def kid23_part96 : Audit := .cycle 1 13 true (1)
theorem kid23_part96_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part96) = true := by rfl

def kid23_part97 : Audit := .cycle 10 1 true (4)
theorem kid23_part97_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part97) = true := by rfl

def kid23_part98 : Audit := .cycle 8 3 true (3)
theorem kid23_part98_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part98) = true := by rfl

def kid23_part74 : Audit := .split 10 (4,false) (byMove [(kid23_part75),(kid23_part76),(kid23_part77),(kid23_part78),(kid23_part79),(kid23_part80),(kid23_part81),(kid23_part82),(kid23_part83),(kid23_part84),(kid23_part85),(kid23_part86),(kid23_part87),(kid23_part88),(kid23_part89),(kid23_part90),(kid23_part91),(kid23_part92),(kid23_part93),(kid23_part94),(kid23_part95),(kid23_part96),(kid23_part97),(kid23_part98)])

theorem kid23_part74_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part74) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid23_part75),(kid23_part76),(kid23_part77),(kid23_part78),(kid23_part79),(kid23_part80),(kid23_part81),(kid23_part82),(kid23_part83),(kid23_part84),(kid23_part85),(kid23_part86),(kid23_part87),(kid23_part88),(kid23_part89),(kid23_part90),(kid23_part91),(kid23_part92),(kid23_part93),(kid23_part94),(kid23_part95),(kid23_part96),(kid23_part97),(kid23_part98)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part75_checked

  · exact kid23_part81_checked

  · exact kid23_part87_checked

  · exact kid23_part93_checked

  · exact kid23_part76_checked

  · exact kid23_part82_checked

  · exact kid23_part88_checked

  · exact kid23_part94_checked

  · exact kid23_part77_checked

  · exact kid23_part83_checked

  · exact kid23_part89_checked

  · exact kid23_part95_checked

  · exact kid23_part78_checked

  · exact kid23_part84_checked

  · exact kid23_part90_checked

  · exact kid23_part96_checked

  · exact kid23_part79_checked

  · exact kid23_part85_checked

  · exact kid23_part91_checked

  · exact kid23_part97_checked

  · exact kid23_part80_checked

  · exact kid23_part86_checked

  · exact kid23_part92_checked

  · exact kid23_part98_checked

def kid23_part99 : Audit := .cycle 8 2 true (3)
theorem kid23_part99_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part99) = true := by rfl

def kid23_part3 : Audit := .split 9 (2,true) (byMove [(kid23_part4),(kid23_part5),(kid23_part6),(kid23_part7),(kid23_part8),(kid23_part33),(kid23_part34),(kid23_part35),(kid23_part36),(kid23_part37),(kid23_part38),(kid23_part39),(kid23_part40),(kid23_part41),(kid23_part42),(kid23_part43),(kid23_part44),(kid23_part69),(kid23_part70),(kid23_part71),(kid23_part72),(kid23_part73),(kid23_part74),(kid23_part99)])

theorem kid23_part3_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (kid23_part3) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) 9 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part4),(kid23_part5),(kid23_part6),(kid23_part7),(kid23_part8),(kid23_part33),(kid23_part34),(kid23_part35),(kid23_part36),(kid23_part37),(kid23_part38),(kid23_part39),(kid23_part40),(kid23_part41),(kid23_part42),(kid23_part43),(kid23_part44),(kid23_part69),(kid23_part70),(kid23_part71),(kid23_part72),(kid23_part73),(kid23_part74),(kid23_part99)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part4_checked

  · exact kid23_part34_checked

  · exact kid23_part40_checked

  · exact kid23_part70_checked

  · exact kid23_part5_checked

  · exact kid23_part35_checked

  · exact kid23_part41_checked

  · exact kid23_part71_checked

  · exact kid23_part6_checked

  · exact kid23_part36_checked

  · exact kid23_part42_checked

  · exact kid23_part72_checked

  · exact kid23_part7_checked

  · exact kid23_part37_checked

  · exact kid23_part43_checked

  · exact kid23_part73_checked

  · exact kid23_part8_checked

  · exact kid23_part38_checked

  · exact kid23_part44_checked

  · exact kid23_part74_checked

  · exact kid23_part33_checked

  · exact kid23_part39_checked

  · exact kid23_part69_checked

  · exact kid23_part99_checked

def kid23_part100 : Audit := .cycle 0 10 true (0)
theorem kid23_part100_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (kid23_part100) = true := by rfl

def kid23_part102 : Audit := .cycle 1 10 true (1)
theorem kid23_part102_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part102) = true := by rfl

def kid23_part103 : Audit := .cycle 1 12 true (1)
theorem kid23_part103_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part103) = true := by rfl

def kid23_part105 : Audit := .cycle 0 11 true (0)
theorem kid23_part105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part105) = true := by rfl

def kid23_part106 : Audit := .cycle 1 10 true (1)
theorem kid23_part106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part106) = true := by rfl

def kid23_part107 : Audit := .cycle 21 1 false (1)
theorem kid23_part107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part107) = true := by rfl

def kid23_part108 : Audit := .cycle 1 13 true (0)
theorem kid23_part108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part108) = true := by rfl

def kid23_part109 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.last 13 (5,true),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 19 1 false (-1)
])
theorem kid23_part109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part109) = true := by rfl

def kid23_part110 : Audit := .cycle 14 1 false (0)
theorem kid23_part110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part110) = true := by rfl

def kid23_part111 : Audit := .cycle 0 11 true (0)
theorem kid23_part111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part111) = true := by rfl

def kid23_part112 : Audit := .cycle 1 10 true (1)
theorem kid23_part112_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part112) = true := by rfl

def kid23_part113 : Audit := .split 19 (5,true) (byMove [
.cycle 1 31 true (0),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 7 15 true (0),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 1 20 true (0),
.cycle 2 21 true (0),
.cycle 10 10 true (0),
.cycle 0 21 true (0),
.cycle 2 19 true (0),
.last 22 (4,false),
.cycle 20 13 true (2),
.cycle 18 2 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 2060, 4096],[128, 2048, 4, 1, 2052, 1, 128, 2048, 4, 1, 8, 4, 4096],5168⟩,
.cycle 5 15 true (0),
.cycle 1 24 true (0),
.last 23 (4,false),
.cycle 1 20 true (0),
.cycle 1 31 true (0),
.cycle 2 27 true (0),
.cycle 0 21 true (0),
.last 30 (4,false),
.cycle 20 11 true (2)
])
theorem kid23_part113_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part113) = true := by rfl

def kid23_part114 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (0),
.cycle 22 1 false (2),
.cycle 27 1 false (3),
.cycle 0 19 true (0),
.cycle 20 1 false (2),
.last 21 (4,false),
.cycle 0 18 true (0),
.cycle 2 37 true (0),
.cycle 11 8 true (0),
.cycle 3 15 true (0),
.last 18 (4,false),
.last 19 (4,false),
.cycle 31 1 false (3),
.cycle 16 2 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 20 1 false (2),
.last 21 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 1 20 true (0),
.last 18 (4,false),
.cycle 29 1 false (3)
])
theorem kid23_part114_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part114) = true := by rfl

def kid23_part115 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 21 (5,true)
])
theorem kid23_part115_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part115) = true := by rfl

def kid23_part116 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 21 7 false (2),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 29 1 false (1)
])
theorem kid23_part116_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part116) = true := by rfl

def kid23_part117 : Audit := .cycle 17 5 false (2)
theorem kid23_part117_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part117) = true := by rfl

def kid23_part118 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 27 1 false (-1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (1),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 19 9 false (2),
.cycle 13 2 true (1),
.cycle 15 5 false (1),
.cycle 1 16 true (1),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 17 7 false (2)
])
theorem kid23_part118_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part118) = true := by rfl

def kid23_part119 : Audit := .cycle 0 13 true (0)
theorem kid23_part119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part119) = true := by rfl

def kid23_part120 : Audit := .cycle 18 1 false (0)
theorem kid23_part120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part120) = true := by rfl

def kid23_part121 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 29 1 false (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 16 1 false (0),
.last 12 (5,true)
])
theorem kid23_part121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part121) = true := by rfl

def kid23_part122 : Audit := .cycle 14 1 false (0)
theorem kid23_part122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part122) = true := by rfl

def kid23_part123 : Audit := .cycle 0 11 true (0)
theorem kid23_part123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part123) = true := by rfl

def kid23_part124 : Audit := .cycle 1 10 true (1)
theorem kid23_part124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part124) = true := by rfl

def kid23_part125 : Audit := .cycle 2 9 true (1)
theorem kid23_part125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part125) = true := by rfl

def kid23_part126 : Audit := .cycle 1 13 true (1)
theorem kid23_part126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part126) = true := by rfl

def kid23_part127 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 29 1 false (1),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 9 4 true (2),
.cycle 1 13 true (1),
.last 19 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2)
])
theorem kid23_part127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part127) = true := by rfl

def kid23_part128 : Audit := .cycle 25 1 false (1)
theorem kid23_part128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part128) = true := by rfl

def kid23_part104 : Audit := .split 10 (2,true) (byMove [(kid23_part105),(kid23_part106),(kid23_part107),(kid23_part108),(kid23_part109),(kid23_part110),(kid23_part111),(kid23_part112),(kid23_part113),(kid23_part114),(kid23_part115),(kid23_part116),(kid23_part117),(kid23_part118),(kid23_part119),(kid23_part120),(kid23_part121),(kid23_part122),(kid23_part123),(kid23_part124),(kid23_part125),(kid23_part126),(kid23_part127),(kid23_part128)])

theorem kid23_part104_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part104) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part105),(kid23_part106),(kid23_part107),(kid23_part108),(kid23_part109),(kid23_part110),(kid23_part111),(kid23_part112),(kid23_part113),(kid23_part114),(kid23_part115),(kid23_part116),(kid23_part117),(kid23_part118),(kid23_part119),(kid23_part120),(kid23_part121),(kid23_part122),(kid23_part123),(kid23_part124),(kid23_part125),(kid23_part126),(kid23_part127),(kid23_part128)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part105_checked

  · exact kid23_part111_checked

  · exact kid23_part117_checked

  · exact kid23_part123_checked

  · exact kid23_part106_checked

  · exact kid23_part112_checked

  · exact kid23_part118_checked

  · exact kid23_part124_checked

  · exact kid23_part107_checked

  · exact kid23_part113_checked

  · exact kid23_part119_checked

  · exact kid23_part125_checked

  · exact kid23_part108_checked

  · exact kid23_part114_checked

  · exact kid23_part120_checked

  · exact kid23_part126_checked

  · exact kid23_part109_checked

  · exact kid23_part115_checked

  · exact kid23_part121_checked

  · exact kid23_part127_checked

  · exact kid23_part110_checked

  · exact kid23_part116_checked

  · exact kid23_part122_checked

  · exact kid23_part128_checked

def kid23_part129 : Audit := .cycle 0 11 true (0)
theorem kid23_part129_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part129) = true := by rfl

def kid23_part130 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 11 false (1),
.split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 20 1 false (-2),
.last 16 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
]),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 23 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 23 2 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 2 false (0),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 19 (5,true) (byMove [
.cycle 1 20 true (0),
.cycle 26 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 10 32 true (0),
.cycle 12 8 true (0),
.cycle 3 17 true (0),
.cycle 10 20 true (0),
.cycle 11 10 true (0),
.cycle 28 1 false (2),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 24 1 false (2),
.cycle 33 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 1 22 true (0),
.cycle 11 9 true (0),
.cycle 26 1 false (2)
]),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.split 13 (5,true) (byMove [
.cycle 1 14 true (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.last 26 (2,true),
.cycle 12 8 true (0),
.last 24 (2,true),
.last 16 (2,true),
.cycle 11 4 true (0),
.last 21 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.cycle 1 15 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 11 3 true (0),
.last 19 (2,true)
]),
.split 12 (2,true) (byMove [
.cycle 14 16 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.last 20 (5,true),
.cycle 1 13 true (0),
.cycle 0 19 true (-1),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 0 17 true (-1),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.last 19 (5,true),
.cycle 1 13 true (0),
.cycle 0 20 true (-2),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 0 18 true (-2),
.last 13 (5,true)
]),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 1 13 true (0),
.cycle 16 2 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 2 false (0),
.cycle 14 2 false (2),
.cycle 22 2 false (-2),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 1 13 true (0),
.cycle 17 2 false (-1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 14 3 false (0)
])
theorem kid23_part130_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part130) = true := by rfl

def kid23_part132 : Audit := .cycle 0 11 true (0)
theorem kid23_part132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part132) = true := by rfl

def kid23_part133 : Audit := .cycle 1 10 true (1)
theorem kid23_part133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part133) = true := by rfl

def kid23_part134 : Audit := .cycle 21 1 false (1)
theorem kid23_part134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part134) = true := by rfl

def kid23_part135 : Audit := .cycle 1 13 true (0)
theorem kid23_part135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part135) = true := by rfl

def kid23_part136 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 16 11 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 15 4 false (0)
])
theorem kid23_part136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part136) = true := by rfl

def kid23_part137 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (4),
.cycle 13 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 15 false (4),
.cycle 13 12 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 true (-2),
.cycle 13 2 true (-2),
.cycle 13 7 false (-1),
.last 16 (2,true),
.cycle 0 17 false (4),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 13 16 false (3),
.cycle 1 14 false (4),
.cycle 13 11 false (1),
.cycle 1 17 false (4),
.cycle 14 1 true (-2),
.cycle 11 4 false (1)
])
theorem kid23_part137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part137) = true := by rfl

def kid23_part138 : Audit := .cycle 0 11 true (0)
theorem kid23_part138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part138) = true := by rfl

def kid23_part139 : Audit := .cycle 1 10 true (1)
theorem kid23_part139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part139) = true := by rfl

def kid23_part140 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 1 23 true (0),
.last 21 (4,false),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.cycle 43 8 true (7),
.cycle 11 10 true (0),
.cycle 21 8 true (2),
.last 21 (4,false),
.last 22 (4,false),
.cycle 25 8 true (2),
.cycle 23 8 true (3),
.cycle 0 23 true (0),
.cycle 4 17 true (0),
.last 21 (4,false),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 40 true (0),
.cycle 1 23 true (0),
.last 21 (4,false),
.cycle 27 1 false (3)
])
theorem kid23_part140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part140) = true := by rfl

def kid23_part141 : Audit := .cycle 3 15 true (0)
theorem kid23_part141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part141) = true := by rfl

def kid23_part142 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 19 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (-2),
.cycle 15 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 28 1 false (4),
.cycle 25 1 false (3),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 15 true (0),
.cycle 16 1 false (-2),
.cycle 16 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 19 4 false (2)
])
theorem kid23_part142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part142) = true := by rfl

def kid23_part143 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 12 true (0),
.cycle 3 19 true (0),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 15 4 false (1)
])
theorem kid23_part143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part143) = true := by rfl

def kid23_part144 : Audit := .cycle 17 5 false (2)
theorem kid23_part144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part144) = true := by rfl

def kid23_part145 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 23 (4,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 2 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 17 2 true (0),
.cycle 13 2 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 15 2 true (0)
])
theorem kid23_part145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part145) = true := by rfl

def kid23_part146 : Audit := .cycle 0 13 true (0)
theorem kid23_part146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part146) = true := by rfl

def kid23_part147 : Audit := .cycle 18 1 false (0)
theorem kid23_part147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part147) = true := by rfl

def kid23_part148 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 77 36 false (1),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 1 12 true (1),
.cycle 15 16 true (-2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 16 1 true (-2),
.cycle 10 2 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 1 12 true (1),
.cycle 0 22 true (-2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 21 3 false (-1),
.cycle 17 4 false (-1)
])
theorem kid23_part148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part148) = true := by rfl

def kid23_part149 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (4),
.cycle 24 12 false (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 19 true (-2),
.last 28 (2,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 20 1 true (0),
.cycle 13 2 true (-2),
.cycle 13 7 false (-1),
.last 16 (2,true),
.last 36 (2,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 19 true (-2),
.cycle 10 14 false (2),
.last 30 (2,true),
.cycle 0 21 true (-2),
.cycle 21 6 false (-1),
.cycle 11 4 false (1)
])
theorem kid23_part149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part149) = true := by rfl

def kid23_part150 : Audit := .cycle 0 11 true (0)
theorem kid23_part150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part150) = true := by rfl

def kid23_part151 : Audit := .cycle 1 10 true (1)
theorem kid23_part151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part151) = true := by rfl

def kid23_part152 : Audit := .cycle 2 9 true (1)
theorem kid23_part152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part152) = true := by rfl

def kid23_part153 : Audit := .cycle 1 13 true (1)
theorem kid23_part153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part153) = true := by rfl

def kid23_part154 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 15 16 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 16 1 false (-2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (2),
.cycle 10 3 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 16 1 false (-2),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2)
])
theorem kid23_part154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part154) = true := by rfl

def kid23_part155 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 false (4),
.cycle 13 14 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 0 17 false (4),
.cycle 13 14 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 true (-2),
.cycle 15 2 true (-2),
.cycle 13 9 false (1),
.last 18 (2,true),
.cycle 0 19 false (4),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 13 20 false (3),
.cycle 1 16 false (4),
.cycle 13 13 false (1),
.cycle 1 19 false (4),
.cycle 16 1 true (-2),
.cycle 13 4 false (1)
])
theorem kid23_part155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part155) = true := by rfl

def kid23_part131 : Audit := .split 10 (5,true) (byMove [(kid23_part132),(kid23_part133),(kid23_part134),(kid23_part135),(kid23_part136),(kid23_part137),(kid23_part138),(kid23_part139),(kid23_part140),(kid23_part141),(kid23_part142),(kid23_part143),(kid23_part144),(kid23_part145),(kid23_part146),(kid23_part147),(kid23_part148),(kid23_part149),(kid23_part150),(kid23_part151),(kid23_part152),(kid23_part153),(kid23_part154),(kid23_part155)])

theorem kid23_part131_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part131) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part132),(kid23_part133),(kid23_part134),(kid23_part135),(kid23_part136),(kid23_part137),(kid23_part138),(kid23_part139),(kid23_part140),(kid23_part141),(kid23_part142),(kid23_part143),(kid23_part144),(kid23_part145),(kid23_part146),(kid23_part147),(kid23_part148),(kid23_part149),(kid23_part150),(kid23_part151),(kid23_part152),(kid23_part153),(kid23_part154),(kid23_part155)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part132_checked

  · exact kid23_part138_checked

  · exact kid23_part144_checked

  · exact kid23_part150_checked

  · exact kid23_part133_checked

  · exact kid23_part139_checked

  · exact kid23_part145_checked

  · exact kid23_part151_checked

  · exact kid23_part134_checked

  · exact kid23_part140_checked

  · exact kid23_part146_checked

  · exact kid23_part152_checked

  · exact kid23_part135_checked

  · exact kid23_part141_checked

  · exact kid23_part147_checked

  · exact kid23_part153_checked

  · exact kid23_part136_checked

  · exact kid23_part142_checked

  · exact kid23_part148_checked

  · exact kid23_part154_checked

  · exact kid23_part137_checked

  · exact kid23_part143_checked

  · exact kid23_part149_checked

  · exact kid23_part155_checked

def kid23_part156 : Audit := .cycle 0 10 true (0)
theorem kid23_part156_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part156) = true := by rfl

def kid23_part157 : Audit := .cycle 1 9 true (1)
theorem kid23_part157_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part157) = true := by rfl

def kid23_part159 : Audit := .cycle 1 18 true (1)
theorem kid23_part159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part159) = true := by rfl

def kid23_part160 : Audit := .cycle 7 11 true (2)
theorem kid23_part160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part160) = true := by rfl

def kid23_part161 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 37 1 false (3),
.cycle 31 1 false (1),
.cycle 0 20 true (0),
.cycle 33 1 false (3),
.cycle 31 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 9 true (2),
.cycle 3 16 true (1),
.last 19 (4,false),
.last 20 (4,false),
.cycle 6 13 true (2),
.cycle 31 5 false (1),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 21 (4,false),
.cycle 31 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (2)
])
theorem kid23_part161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part161) = true := by rfl

def kid23_part162 : Audit := .cycle 0 19 true (0)
theorem kid23_part162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part162) = true := by rfl

def kid23_part163 : Audit := .cycle 9 9 true (2)
theorem kid23_part163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part163) = true := by rfl

def kid23_part164 : Audit := .split 21 (4,false) (byMove [
.cycle 1 22 true (0),
.cycle 26 1 false (2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 24 1 false (2),
.cycle 23 2 false (-1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 21 1 true (1),
.cycle 20 2 true (1),
.cycle 23 16 false (3),
.last 28 (2,true),
.last 22 (2,true),
.cycle 1 23 true (0),
.last 23 (2,true),
.cycle 23 2 false (-1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 21 1 true (1),
.cycle 39 1 false (1)
])
theorem kid23_part164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part164) = true := by rfl

def kid23_part165 : Audit := .cycle 0 18 true (0)
theorem kid23_part165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part165) = true := by rfl

def kid23_part166 : Audit := .cycle 1 17 true (1)
theorem kid23_part166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part166) = true := by rfl

def kid23_part167 : Audit := .cycle 10 8 true (2)
theorem kid23_part167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part167) = true := by rfl

def kid23_part168 : Audit := .cycle 3 15 true (1)
theorem kid23_part168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part168) = true := by rfl

def kid23_part169 : Audit := .split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 11 true (2),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 19 10 true (4),
.cycle 11 8 true (2),
.cycle 18 1 true (6),
.cycle 18 2 true (6),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 21 (2,true),
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 20 10 true (4)
])
theorem kid23_part169_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part169) = true := by rfl

def kid23_part170 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 11 true (2),
.cycle 29 2 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.cycle 19 1 true (5),
.cycle 18 2 true (5),
.cycle 6 14 true (2),
.cycle 16 4 true (4),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 21 (2,true),
.cycle 0 28 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (5),
.cycle 8 12 true (2)
])
theorem kid23_part170_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part170) = true := by rfl

def kid23_part171 : Audit := .cycle 6 12 true (2)
theorem kid23_part171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part171) = true := by rfl

def kid23_part172 : Audit := .cycle 16 2 true (4)
theorem kid23_part172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part172) = true := by rfl

def kid23_part173 : Audit := .split 18 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 0 24 true (0),
.cycle 31 1 false (1),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 7 16 true (2),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 4096, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 2, 1, 4, 1, 128, 2048, 2, 1, 4, 2048, 4096],5168⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 4, 1, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 0 20 true (0),
.last 32 (4,false),
.cycle 0 22 true (0),
.cycle 15 4 true (3),
.cycle 31 5 false (1),
.cycle 5 16 true (1),
.cycle 5 14 true (1),
.last 21 (4,false),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.cycle 9 10 true (2),
.cycle 17 2 true (4)
])
theorem kid23_part173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part173) = true := by rfl

def kid23_part174 : Audit := .cycle 1 19 true (1)
theorem kid23_part174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part174) = true := by rfl

def kid23_part175 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 37 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 11 9 true (2),
.last 20 (4,false),
.last 21 (4,false),
.cycle 7 14 true (2),
.cycle 16 6 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 20 (4,false),
.cycle 0 24 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 4096, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 2048, 1, 4, 4096, 128, 2048, 2048, 1, 4, 2048, 4096],5168⟩
])
theorem kid23_part175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part175) = true := by rfl

def kid23_part176 : Audit := .split 21 (4,false) (byMove [
.cycle 23 20 true (1),
.cycle 26 1 false (2),
.last 22 (2,true),
.last 25 (2,true),
.cycle 24 1 false (2),
.cycle 23 2 false (-1),
.cycle 32 7 false (5),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 32 1 false (0),
.last 24 (2,true),
.cycle 20 2 true (1),
.cycle 23 22 true (1),
.last 28 (2,true),
.last 22 (2,true),
.last 25 (2,true),
.last 23 (2,true),
.cycle 23 2 false (-1),
.cycle 25 8 false (3),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 32 9 false (5),
.last 24 (2,true),
.cycle 5 20 true (1)
])
theorem kid23_part176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part176) = true := by rfl

def kid23_part177 : Audit := .cycle 0 18 true (0)
theorem kid23_part177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part177) = true := by rfl

def kid23_part178 : Audit := .cycle 1 17 true (1)
theorem kid23_part178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part178) = true := by rfl

def kid23_part179 : Audit := .cycle 2 16 true (1)
theorem kid23_part179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part179) = true := by rfl

def kid23_part180 : Audit := .cycle 1 20 true (1)
theorem kid23_part180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part180) = true := by rfl

def kid23_part181 : Audit := .split 18 (4,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 9 10 true (2),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 9 true (2),
.cycle 3 16 true (1),
.cycle 18 1 true (6),
.cycle 18 2 true (6),
.cycle 6 13 true (2),
.cycle 16 3 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.last 20 (2,true),
.cycle 9 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (2)
])
theorem kid23_part181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part181) = true := by rfl

def kid23_part182 : Audit := .cycle 8 10 true (2)
theorem kid23_part182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part182) = true := by rfl

def kid23_part158 : Audit := .split 17 (5,true) (byMove [(kid23_part159),(kid23_part160),(kid23_part161),(kid23_part162),(kid23_part163),(kid23_part164),(kid23_part165),(kid23_part166),(kid23_part167),(kid23_part168),(kid23_part169),(kid23_part170),(kid23_part171),(kid23_part172),(kid23_part173),(kid23_part174),(kid23_part175),(kid23_part176),(kid23_part177),(kid23_part178),(kid23_part179),(kid23_part180),(kid23_part181),(kid23_part182)])

theorem kid23_part158_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part158) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid23_part159),(kid23_part160),(kid23_part161),(kid23_part162),(kid23_part163),(kid23_part164),(kid23_part165),(kid23_part166),(kid23_part167),(kid23_part168),(kid23_part169),(kid23_part170),(kid23_part171),(kid23_part172),(kid23_part173),(kid23_part174),(kid23_part175),(kid23_part176),(kid23_part177),(kid23_part178),(kid23_part179),(kid23_part180),(kid23_part181),(kid23_part182)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part159_checked

  · exact kid23_part165_checked

  · exact kid23_part171_checked

  · exact kid23_part177_checked

  · exact kid23_part160_checked

  · exact kid23_part166_checked

  · exact kid23_part172_checked

  · exact kid23_part178_checked

  · exact kid23_part161_checked

  · exact kid23_part167_checked

  · exact kid23_part173_checked

  · exact kid23_part179_checked

  · exact kid23_part162_checked

  · exact kid23_part168_checked

  · exact kid23_part174_checked

  · exact kid23_part180_checked

  · exact kid23_part163_checked

  · exact kid23_part169_checked

  · exact kid23_part175_checked

  · exact kid23_part181_checked

  · exact kid23_part164_checked

  · exact kid23_part170_checked

  · exact kid23_part176_checked

  · exact kid23_part182_checked

def kid23_part183 : Audit := .cycle 3 7 true (1)
theorem kid23_part183_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part183) = true := by rfl

def kid23_part184 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 17 1 false (1),
.split 16 (5,true) (byMove [
.cycle 0 17 false (4),
.cycle 29 2 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 17 true (0),
.cycle 29 2 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 2 false (1),
.cycle 17 2 false (1),
.cycle 24 2 false (0),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 28 2 false (2),
.cycle 1 19 true (0),
.cycle 15 2 true (0),
.cycle 19 2 false (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.last 24 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.last 22 (2,true),
.cycle 37 1 false (1),
.cycle 1 20 true (1),
.cycle 1 35 true (1),
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 12, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 10 12 true (2),
.cycle 6 17 true (2),
.cycle 18 2 true (4),
.last 20 (2,true),
.cycle 5 15 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 8, 128, 256, 8, 128, 4, 4, 4096],[128, 2048, 4096, 1, 16, 4096, 128, 2048, 4096, 1, 16, 16, 4096],4096⟩,
.cycle 5 29 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 11 true (2),
.cycle 8 13 true (2)
]),
.split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 9 9 true (2),
.cycle 41 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 11 8 true (2),
.cycle 3 15 true (1),
.cycle 10 8 true (2),
.cycle 3 17 true (1),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.last 18 (2,true),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 8, 59, 64],[2, 32, 64, 1, 16, 17, 64],64⟩,
.cycle 32 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 8 10 true (2)
]),
.cycle 10 1 true (4),
.cycle 10 2 true (4),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.last 16 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 5 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 8 5 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 26 1 false (6),
.split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 34 2 false (0),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.last 19 (2,true),
.cycle 20 2 false (2),
.last 17 (2,true),
.cycle 3 18 true (0),
.cycle 18 2 false (2),
.cycle 18 2 false (2),
.cycle 30 2 false (0),
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.last 19 (2,true),
.cycle 23 2 false (1),
.last 17 (2,true),
.cycle 1 23 true (0),
.cycle 21 2 false (1),
.cycle 23 2 false (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 8 3 true (3)
])
theorem kid23_part184_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part184) = true := by rfl

def kid23_part186 : Audit := .cycle 1 12 true (1)
theorem kid23_part186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part186) = true := by rfl

def kid23_part187 : Audit := .cycle 1 16 true (1)
theorem kid23_part187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part187) = true := by rfl

def kid23_part188 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.last 21 (5,true),
.cycle 29 1 false (1),
.cycle 21 7 false (2),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 33 1 false (1)
])
theorem kid23_part188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part188) = true := by rfl

def kid23_part189 : Audit := .cycle 0 13 true (0)
theorem kid23_part189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part189) = true := by rfl

def kid23_part190 : Audit := .cycle 18 1 false (0)
theorem kid23_part190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part190) = true := by rfl

def kid23_part191 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 2 false (-1),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 3 17 true (0),
.cycle 17 2 false (1),
.cycle 17 2 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (-1),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 19 2 false (1)
])
theorem kid23_part191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part191) = true := by rfl

def kid23_part192 : Audit := .cycle 0 12 true (0)
theorem kid23_part192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part192) = true := by rfl

def kid23_part193 : Audit := .cycle 1 11 true (1)
theorem kid23_part193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part193) = true := by rfl

def kid23_part194 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 11 true (2),
.cycle 37 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (2),
.cycle 3 17 true (1),
.cycle 20 12 true (4),
.cycle 10 10 true (2),
.cycle 6 14 true (2),
.cycle 18 2 true (4),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 23 (2,true),
.cycle 5 20 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (2),
.cycle 8 12 true (2)
])
theorem kid23_part194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part194) = true := by rfl

def kid23_part195 : Audit := .cycle 3 9 true (1)
theorem kid23_part195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part195) = true := by rfl

def kid23_part196 : Audit := .cycle 11 1 true (3)
theorem kid23_part196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part196) = true := by rfl

def kid23_part197 : Audit := .cycle 10 2 true (3)
theorem kid23_part197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part197) = true := by rfl

def kid23_part198 : Audit := .cycle 6 6 true (2)
theorem kid23_part198_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part198) = true := by rfl

def kid23_part199 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.last 20 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 18 (2,true),
.last 20 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.last 16 (2,true),
.cycle 10 4 true (2),
.cycle 6 8 true (2),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 18 (2,true),
.last 20 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (2),
.cycle 8 6 true (2)
])
theorem kid23_part199_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part199) = true := by rfl

def kid23_part200 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 13 10 true (-2),
.last 22 (5,true),
.cycle 1 13 true (1),
.cycle 0 20 true (0),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 0 18 true (0),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 20 (5,true),
.last 21 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 13 (5,true)
])
theorem kid23_part200_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part200) = true := by rfl

def kid23_part201 : Audit := .cycle 1 13 true (1)
theorem kid23_part201_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part201) = true := by rfl

def kid23_part202 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 22 (2,true),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 21 true (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (2),
.cycle 47 1 false (3)
])
theorem kid23_part202_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part202) = true := by rfl

def kid23_part203 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 20 (2,true),
.last 17 (2,true),
.cycle 15 2 false (-1),
.cycle 15 2 false (1),
.cycle 1 13 true (1),
.cycle 24 2 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 20 2 false (2),
.cycle 20 2 false (2),
.cycle 14 10 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 1 19 true (0),
.cycle 15 2 false (-1),
.cycle 15 2 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 8 6 true (2)
])
theorem kid23_part203_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part203) = true := by rfl

def kid23_part204 : Audit := .cycle 0 12 true (0)
theorem kid23_part204_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part204) = true := by rfl

def kid23_part205 : Audit := .cycle 1 11 true (1)
theorem kid23_part205_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part205) = true := by rfl

def kid23_part206 : Audit := .cycle 2 10 true (1)
theorem kid23_part206_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part206) = true := by rfl

def kid23_part207 : Audit := .cycle 1 14 true (1)
theorem kid23_part207_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part207) = true := by rfl

def kid23_part208 : Audit := .cycle 11 1 true (3)
theorem kid23_part208_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part208) = true := by rfl

def kid23_part209 : Audit := .cycle 8 4 true (3)
theorem kid23_part209_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part209) = true := by rfl

def kid23_part185 : Audit := .split 11 (4,false) (byMove [(kid23_part186),(kid23_part187),(kid23_part188),(kid23_part189),(kid23_part190),(kid23_part191),(kid23_part192),(kid23_part193),(kid23_part194),(kid23_part195),(kid23_part196),(kid23_part197),(kid23_part198),(kid23_part199),(kid23_part200),(kid23_part201),(kid23_part202),(kid23_part203),(kid23_part204),(kid23_part205),(kid23_part206),(kid23_part207),(kid23_part208),(kid23_part209)])

theorem kid23_part185_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part185) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (4,false) (some mv)) (byMove [(kid23_part186),(kid23_part187),(kid23_part188),(kid23_part189),(kid23_part190),(kid23_part191),(kid23_part192),(kid23_part193),(kid23_part194),(kid23_part195),(kid23_part196),(kid23_part197),(kid23_part198),(kid23_part199),(kid23_part200),(kid23_part201),(kid23_part202),(kid23_part203),(kid23_part204),(kid23_part205),(kid23_part206),(kid23_part207),(kid23_part208),(kid23_part209)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part186_checked

  · exact kid23_part192_checked

  · exact kid23_part198_checked

  · exact kid23_part204_checked

  · exact kid23_part187_checked

  · exact kid23_part193_checked

  · exact kid23_part199_checked

  · exact kid23_part205_checked

  · exact kid23_part188_checked

  · exact kid23_part194_checked

  · exact kid23_part200_checked

  · exact kid23_part206_checked

  · exact kid23_part189_checked

  · exact kid23_part195_checked

  · exact kid23_part201_checked

  · exact kid23_part207_checked

  · exact kid23_part190_checked

  · exact kid23_part196_checked

  · exact kid23_part202_checked

  · exact kid23_part208_checked

  · exact kid23_part191_checked

  · exact kid23_part197_checked

  · exact kid23_part203_checked

  · exact kid23_part209_checked

def kid23_part210 : Audit := .cycle 6 4 true (2)
theorem kid23_part210_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part210) = true := by rfl

def kid23_part212 : Audit := .cycle 1 12 true (1)
theorem kid23_part212_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part212) = true := by rfl

def kid23_part213 : Audit := .split 16 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 22 5 false (1),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 22 3 false (0),
.cycle 17 17 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 7 18 true (1),
.cycle 3 14 true (1),
.last 17 (4,false),
.last 18 (4,false),
.cycle 23 11 false (2),
.cycle 22 7 false (1),
.cycle 1 35 true (-1),
.cycle 1 18 true (1),
.cycle 22 3 false (0),
.cycle 0 42 true (-2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.last 17 (4,false),
.cycle 22 9 false (2)
])
theorem kid23_part213_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part213) = true := by rfl

def kid23_part214 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 25 true (0),
.cycle 31 1 false (3),
.last 13 (4,false),
.last 14 (4,false),
.cycle 21 7 false (2),
.cycle 17 5 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 21 9 false (2)
])
theorem kid23_part214_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part214) = true := by rfl

def kid23_part215 : Audit := .cycle 0 13 true (0)
theorem kid23_part215_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part215) = true := by rfl

def kid23_part216 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (1),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 21 9 false (1),
.cycle 18 5 false (1),
.cycle 1 31 true (-1),
.cycle 1 16 true (1),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 19 7 false (1)
])
theorem kid23_part216_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part216) = true := by rfl

def kid23_part217 : Audit := .split 16 (2,true) (byMove [
.cycle 1 17 false (4),
.cycle 13 5 false (1),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 14 3 false (0),
.last 19 (4,false),
.cycle 0 17 true (-1),
.last 30 (4,false),
.last 28 (4,false),
.last 28 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 25 (4,false),
.last 21 (4,false),
.cycle 1 20 true (-2),
.cycle 1 18 true (-1),
.cycle 14 3 false (0),
.last 19 (4,false),
.last 37 (4,false),
.last 35 (4,false),
.cycle 2 15 false (4),
.cycle 1 19 true (-1),
.last 17 (4,false),
.last 23 (4,false)
])
theorem kid23_part217_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part217) = true := by rfl

def kid23_part218 : Audit := .cycle 0 12 true (0)
theorem kid23_part218_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part218) = true := by rfl

def kid23_part219 : Audit := .cycle 1 11 true (1)
theorem kid23_part219_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part219) = true := by rfl

def kid23_part220 : Audit := .cycle 10 8 true (2)
theorem kid23_part220_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part220) = true := by rfl

def kid23_part221 : Audit := .cycle 3 9 true (1)
theorem kid23_part221_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part221) = true := by rfl

def kid23_part222 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 10 8 true (2),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 16 (2,true)
])
theorem kid23_part222_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part222) = true := by rfl

def kid23_part223 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.last 18 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 16 (2,true),
.last 20 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 12 2 true (3),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 16 (2,true),
.cycle 22 2 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 8 6 true (2)
])
theorem kid23_part223_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part223) = true := by rfl

def kid23_part224 : Audit := .cycle 6 6 true (2)
theorem kid23_part224_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part224) = true := by rfl

def kid23_part225 : Audit := .cycle 10 2 true (2)
theorem kid23_part225_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part225) = true := by rfl

def kid23_part226 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 0 24 true (-2),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 4, 1, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 14 4 true (1),
.cycle 17 5 false (1),
.cycle 1 15 true (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.last 26 (4,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
])
theorem kid23_part226_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part226) = true := by rfl

def kid23_part227 : Audit := .cycle 1 13 true (1)
theorem kid23_part227_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part227) = true := by rfl

def kid23_part228 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 1 15 true (1),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 8, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 0 16 true (0),
.last 18 (4,false),
.last 16 (4,false),
.cycle 19 9 false (2),
.cycle 18 5 false (1),
.cycle 15 12 true (-1),
.cycle 5 10 true (1),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 1 15 true (1),
.cycle 18 11 false (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 18 9 false (2),
.cycle 18 7 false (2)
])
theorem kid23_part228_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part228) = true := by rfl

def kid23_part229 : Audit := .split 16 (2,true) (byMove [
.cycle 1 21 true (-1),
.cycle 13 5 false (1),
.cycle 19 1 false (-1),
.cycle 7 16 true (-1),
.cycle 14 3 false (0),
.last 19 (4,false),
.cycle 11 9 false (3),
.last 37 (4,false),
.cycle 1 19 true (-1),
.last 26 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 25 (4,false),
.last 21 (4,false),
.last 33 (4,false),
.cycle 5 16 true (-1),
.cycle 14 3 false (0),
.last 19 (4,false),
.last 25 (4,false),
.last 29 (4,false),
.cycle 1 19 true (-1),
.cycle 11 11 false (3),
.last 17 (4,false),
.last 23 (4,false)
])
theorem kid23_part229_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part229) = true := by rfl

def kid23_part230 : Audit := .cycle 0 12 true (0)
theorem kid23_part230_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part230) = true := by rfl

def kid23_part231 : Audit := .cycle 1 11 true (1)
theorem kid23_part231_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part231) = true := by rfl

def kid23_part232 : Audit := .cycle 2 10 true (1)
theorem kid23_part232_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part232) = true := by rfl

def kid23_part233 : Audit := .cycle 1 14 true (1)
theorem kid23_part233_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part233) = true := by rfl

def kid23_part234 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 9 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 7 true (2),
.cycle 9 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (2)
])
theorem kid23_part234_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part234) = true := by rfl

def kid23_part235 : Audit := .cycle 8 4 true (2)
theorem kid23_part235_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part235) = true := by rfl

def kid23_part211 : Audit := .split 11 (5,true) (byMove [(kid23_part212),(kid23_part213),(kid23_part214),(kid23_part215),(kid23_part216),(kid23_part217),(kid23_part218),(kid23_part219),(kid23_part220),(kid23_part221),(kid23_part222),(kid23_part223),(kid23_part224),(kid23_part225),(kid23_part226),(kid23_part227),(kid23_part228),(kid23_part229),(kid23_part230),(kid23_part231),(kid23_part232),(kid23_part233),(kid23_part234),(kid23_part235)])

theorem kid23_part211_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part211) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some mv)) (byMove [(kid23_part212),(kid23_part213),(kid23_part214),(kid23_part215),(kid23_part216),(kid23_part217),(kid23_part218),(kid23_part219),(kid23_part220),(kid23_part221),(kid23_part222),(kid23_part223),(kid23_part224),(kid23_part225),(kid23_part226),(kid23_part227),(kid23_part228),(kid23_part229),(kid23_part230),(kid23_part231),(kid23_part232),(kid23_part233),(kid23_part234),(kid23_part235)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part212_checked

  · exact kid23_part218_checked

  · exact kid23_part224_checked

  · exact kid23_part230_checked

  · exact kid23_part213_checked

  · exact kid23_part219_checked

  · exact kid23_part225_checked

  · exact kid23_part231_checked

  · exact kid23_part214_checked

  · exact kid23_part220_checked

  · exact kid23_part226_checked

  · exact kid23_part232_checked

  · exact kid23_part215_checked

  · exact kid23_part221_checked

  · exact kid23_part227_checked

  · exact kid23_part233_checked

  · exact kid23_part216_checked

  · exact kid23_part222_checked

  · exact kid23_part228_checked

  · exact kid23_part234_checked

  · exact kid23_part217_checked

  · exact kid23_part223_checked

  · exact kid23_part229_checked

  · exact kid23_part235_checked

def kid23_part237 : Audit := .cycle 1 14 true (1)
theorem kid23_part237_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part237) = true := by rfl

def kid23_part238 : Audit := .cycle 0 14 true (0)
theorem kid23_part238_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part238) = true := by rfl

def kid23_part239 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 0 18 true (0),
.cycle 0 41 true (0),
.cycle 12 8 true (0),
.cycle 3 15 true (0),
.last 18 (4,false),
.last 19 (4,false),
.cycle 25 1 false (1),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 1 19 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 1 20 true (0),
.last 18 (4,false),
.cycle 23 1 false (1)
])
theorem kid23_part239_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part239) = true := by rfl

def kid23_part240 : Audit := .cycle 0 17 true (0)
theorem kid23_part240_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part240) = true := by rfl

def kid23_part241 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 30 (5,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.last 13 (5,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.last 12 (5,true),
.cycle 17 14 true (-2),
.cycle 22 5 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 12 true (-2),
.cycle 12 10 true (-2)
])
theorem kid23_part241_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part241) = true := by rfl

def kid23_part242 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (-1),
.cycle 0 24 true (-1),
.last 21 (4,false),
.cycle 0 20 true (-1),
.cycle 0 22 true (-1),
.last 21 (4,false),
.cycle 0 19 true (-1),
.last 30 (4,false),
.cycle 18 8 true (1),
.last 28 (4,false),
.last 19 (4,false),
.last 20 (4,false),
.last 25 (4,false),
.cycle 18 2 true (1),
.last 21 (4,false),
.cycle 1 20 true (-1),
.cycle 1 22 true (-1),
.last 21 (4,false),
.cycle 30 6 true (1),
.last 33 (4,false),
.cycle 2 17 true (-1),
.cycle 1 21 true (-1),
.last 19 (4,false),
.last 23 (4,false)
])
theorem kid23_part242_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part242) = true := by rfl

def kid23_part243 : Audit := .cycle 1 11 true (1)
theorem kid23_part243_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part243) = true := by rfl

def kid23_part244 : Audit := .cycle 0 16 true (0)
theorem kid23_part244_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part244) = true := by rfl

def kid23_part245 : Audit := .split 21 (5,true) (byMove [
.cycle 1 46 true (0),
.cycle 1 29 true (0),
.cycle 1 25 true (0),
.cycle 0 27 true (0),
.cycle 1 27 true (0),
.last 25 (4,false),
.cycle 6 16 true (0),
.cycle 0 53 true (0),
.cycle 10 12 true (0),
.cycle 1 23 true (0),
.cycle 1 25 true (0),
.last 25 (4,false),
.cycle 22 18 true (2),
.cycle 20 2 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 136, 4096],[128, 2048, 4, 1, 1, 1, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 1 27 true (0),
.cycle 29 1 false (7),
.last 25 (4,false),
.cycle 1 37 true (0),
.cycle 1 23 true (0),
.cycle 2 40 true (0),
.cycle 1 23 true (0),
.cycle 10 14 true (0),
.cycle 22 14 true (3)
])
theorem kid23_part245_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part245) = true := by rfl

def kid23_part246 : Audit := .cycle 0 12 true (0)
theorem kid23_part246_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part246) = true := by rfl

def kid23_part247 : Audit := .cycle 0 14 true (0)
theorem kid23_part247_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part247) = true := by rfl

def kid23_part248 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 12 true (0),
.cycle 0 21 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 19 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 0 16 true (0)
])
theorem kid23_part248_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part248) = true := by rfl

def kid23_part249 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 21 9 false (2),
.cycle 0 15 true (0),
.cycle 17 5 false (2),
.last 18 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 12 8 true (1),
.cycle 12 2 true (2),
.cycle 12 4 true (1),
.cycle 1 15 true (1),
.cycle 17 5 false (2),
.last 18 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 12 6 true (1)
])
theorem kid23_part249_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part249) = true := by rfl

def kid23_part250 : Audit := .split 14 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 15 14 true (-2),
.cycle 15 5 false (1),
.cycle 7 10 true (1),
.cycle 15 12 true (-2),
.last 18 (4,false),
.cycle 1 15 true (1),
.cycle 0 20 true (0),
.cycle 18 8 true (2),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 17 (4,false),
.cycle 12 10 true (1),
.cycle 13 2 true (1),
.cycle 15 5 false (1),
.cycle 5 10 true (1),
.cycle 13 12 true (-2),
.last 18 (4,false),
.cycle 1 15 true (1),
.cycle 12 6 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 12 4 true (1),
.cycle 12 6 true (1)
])
theorem kid23_part250_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part250) = true := by rfl

def kid23_part251 : Audit := .cycle 1 13 true (1)
theorem kid23_part251_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part251) = true := by rfl

def kid23_part252 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 1 18 true (0),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.last 19 (4,false),
.cycle 0 16 true (0),
.cycle 0 37 true (0),
.cycle 11 8 true (0),
.cycle 3 13 true (0),
.last 16 (4,false),
.last 17 (4,false),
.cycle 27 1 false (1),
.cycle 14 2 true (2),
.cycle 23 1 false (1),
.cycle 1 17 true (0),
.cycle 18 1 false (0),
.last 19 (4,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 25 1 false (1)
])
theorem kid23_part252_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part252) = true := by rfl

def kid23_part253 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.last 19 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.last 17 (5,true),
.last 12 (5,true),
.cycle 6 6 true (1),
.last 13 (5,true),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.cycle 1 15 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 12 (5,true),
.last 22 (5,true),
.last 13 (5,true),
.last 22 (5,true),
.cycle 1 13 true (1),
.last 19 (5,true),
.last 12 (5,true)
])
theorem kid23_part253_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part253) = true := by rfl

def kid23_part254 : Audit := .split 17 (5,true) (byMove [
.last 33 (4,false),
.last 23 (4,false),
.cycle 21 1 false (1),
.cycle 0 19 true (-1),
.last 21 (4,false),
.last 21 (4,false),
.cycle 0 18 true (-1),
.last 29 (4,false),
.cycle 16 8 true (2),
.cycle 3 15 true (-1),
.last 18 (4,false),
.last 19 (4,false),
.cycle 25 12 true (0),
.cycle 16 2 true (2),
.last 28 (4,false),
.cycle 1 19 true (-1),
.last 21 (4,false),
.last 21 (4,false),
.cycle 29 6 true (2),
.cycle 16 21 true (1),
.last 31 (4,false),
.cycle 1 20 true (-1),
.last 18 (4,false),
.cycle 17 6 true (1)
])
theorem kid23_part254_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part254) = true := by rfl

def kid23_part255 : Audit := .cycle 1 11 true (1)
theorem kid23_part255_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part255) = true := by rfl

def kid23_part256 : Audit := .cycle 7 4 true (2)
theorem kid23_part256_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part256) = true := by rfl

def kid23_part257 : Audit := .cycle 2 10 true (1)
theorem kid23_part257_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part257) = true := by rfl

def kid23_part258 : Audit := .cycle 0 12 true (0)
theorem kid23_part258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part258) = true := by rfl

def kid23_part259 : Audit := .cycle 9 2 true (2)
theorem kid23_part259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part259) = true := by rfl

def kid23_part260 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.cycle 0 17 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.cycle 1 15 true (1),
.last 23 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (2)
])
theorem kid23_part260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part260) = true := by rfl

def kid23_part236 : Audit := .split 10 (2,true) (byMove [(kid23_part237),(kid23_part238),(kid23_part239),(kid23_part240),(kid23_part241),(kid23_part242),(kid23_part243),(kid23_part244),(kid23_part245),(kid23_part246),(kid23_part247),(kid23_part248),(kid23_part249),(kid23_part250),(kid23_part251),(kid23_part252),(kid23_part253),(kid23_part254),(kid23_part255),(kid23_part256),(kid23_part257),(kid23_part258),(kid23_part259),(kid23_part260)])

theorem kid23_part236_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part236) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part237),(kid23_part238),(kid23_part239),(kid23_part240),(kid23_part241),(kid23_part242),(kid23_part243),(kid23_part244),(kid23_part245),(kid23_part246),(kid23_part247),(kid23_part248),(kid23_part249),(kid23_part250),(kid23_part251),(kid23_part252),(kid23_part253),(kid23_part254),(kid23_part255),(kid23_part256),(kid23_part257),(kid23_part258),(kid23_part259),(kid23_part260)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part237_checked

  · exact kid23_part243_checked

  · exact kid23_part249_checked

  · exact kid23_part255_checked

  · exact kid23_part238_checked

  · exact kid23_part244_checked

  · exact kid23_part250_checked

  · exact kid23_part256_checked

  · exact kid23_part239_checked

  · exact kid23_part245_checked

  · exact kid23_part251_checked

  · exact kid23_part257_checked

  · exact kid23_part240_checked

  · exact kid23_part246_checked

  · exact kid23_part252_checked

  · exact kid23_part258_checked

  · exact kid23_part241_checked

  · exact kid23_part247_checked

  · exact kid23_part253_checked

  · exact kid23_part259_checked

  · exact kid23_part242_checked

  · exact kid23_part248_checked

  · exact kid23_part254_checked

  · exact kid23_part260_checked

def kid23_part261 : Audit := .cycle 1 11 true (1)
theorem kid23_part261_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part261) = true := by rfl

def kid23_part263 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.cycle 7 10 true (0),
.cycle 13 6 false (2),
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 13 21 true (1),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 0 21 true (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 21 (5,true),
.cycle 5 10 true (0),
.cycle 13 6 false (2),
.last 15 (5,true),
.cycle 1 15 true (0),
.last 26 (5,true),
.cycle 2 14 true (0),
.cycle 0 16 true (0),
.cycle 13 8 false (3),
.last 15 (5,true)
])
theorem kid23_part263_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part263) = true := by rfl

def kid23_part264 : Audit := .split 21 (5,true) (byMove [
.last 44 (2,true),
.cycle 1 30 true (-2),
.last 22 (2,true),
.last 57 (2,true),
.cycle 1 28 true (-2),
.cycle 34 34 false (3),
.last 48 (2,true),
.cycle 1 36 true (-2),
.cycle 20 8 true (2),
.cycle 3 19 true (-2),
.last 44 (2,true),
.cycle 1 32 true (-2),
.cycle 1 41 true (-2),
.cycle 20 2 true (2),
.last 22 (2,true),
.last 57 (2,true),
.cycle 1 37 true (-2),
.last 35 (2,true),
.proven (BB6.Agent11Raw39Pumps.M2473.table) (fun m hm => BB6.Agent11Raw39Pumps.M2473.never m hm),
.last 53 (2,true),
.last 42 (2,true),
.last 50 (2,true),
.cycle 1 41 true (-2),
.cycle 1 39 true (-2)
])
theorem kid23_part264_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part264) = true := by rfl

def kid23_part265 : Audit := .split 12 (2,true) (byMove [
.cycle 1 17 true (-1),
.last 20 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 15 (5,true),
.last 39 (5,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 20 1 false (-2),
.last 16 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 15 (5,true),
.cycle 23 1 false (-1),
.cycle 1 15 true (0),
.last 17 (5,true),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
])
theorem kid23_part265_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part265) = true := by rfl

def kid23_part266 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (0),
.cycle 21 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 16 true (0),
.last 31 (2,true),
.cycle 14 8 true (2),
.cycle 3 13 true (0),
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.cycle 23 1 false (-1),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 1 17 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 0 18 true (0),
.cycle 21 1 false (-1)
])
theorem kid23_part266_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part266) = true := by rfl

def kid23_part267 : Audit := .cycle 13 1 false (-1)
theorem kid23_part267_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part267) = true := by rfl

def kid23_part268 : Audit := .split 12 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 25 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 1 20 true (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid23_part268_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part268) = true := by rfl

def kid23_part269 : Audit := .cycle 6 6 true (1)
theorem kid23_part269_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part269) = true := by rfl

def kid23_part270 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 14 4 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 4 true (1),
.cycle 15 4 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 1 15 true (1),
.cycle 6 8 true (1),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 4 true (1),
.cycle 15 4 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 8 6 true (1)
])
theorem kid23_part270_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part270) = true := by rfl

def kid23_part271 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.last 23 (5,true),
.cycle 0 14 true (0),
.last 27 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.cycle 11 2 true (1),
.last 23 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 9 4 true (1),
.last 13 (5,true)
])
theorem kid23_part271_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part271) = true := by rfl

def kid23_part272 : Audit := .cycle 1 13 true (1)
theorem kid23_part272_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part272) = true := by rfl

def kid23_part273 : Audit := .cycle 10 2 true (1)
theorem kid23_part273_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part273) = true := by rfl

def kid23_part274 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 20 (2,true),
.last 17 (2,true),
.cycle 13 2 true (1),
.cycle 17 2 true (-2),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 16 2 true (4),
.cycle 14 2 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 1 19 true (0),
.cycle 11 2 true (1),
.cycle 17 2 true (-2),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 4 true (1),
.cycle 8 6 true (1)
])
theorem kid23_part274_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part274) = true := by rfl

def kid23_part275 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 13 8 false (2),
.last 15 (2,true),
.cycle 7 10 true (0),
.cycle 13 6 false (2),
.cycle 13 13 false (2),
.cycle 1 15 true (0),
.cycle 13 21 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 13 2 true (1),
.last 15 (2,true),
.cycle 5 10 true (0),
.cycle 13 6 false (2),
.cycle 13 13 false (2),
.cycle 1 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 8 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part275_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part275) = true := by rfl

def kid23_part276 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.last 19 (2,true),
.last 14 (2,true),
.cycle 0 19 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 6 8 true (0),
.last 28 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 10 4 true (0),
.last 19 (2,true),
.last 29 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.cycle 1 19 true (0),
.last 17 (2,true),
.last 18 (2,true),
.last 23 (2,true),
.cycle 1 15 true (0),
.last 14 (2,true),
.cycle 1 15 true (0),
.last 19 (2,true),
.last 23 (2,true)
])
theorem kid23_part276_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part276) = true := by rfl

def kid23_part277 : Audit := .split 12 (2,true) (byMove [
.cycle 14 22 true (0),
.cycle 14 8 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 17 1 false (5),
.cycle 13 8 true (0),
.last 19 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.last 18 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 2 14 true (0),
.cycle 5 8 true (0),
.last 20 (5,true),
.last 13 (5,true)
])
theorem kid23_part277_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part277) = true := by rfl

def kid23_part278 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (0),
.cycle 21 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 16 true (0),
.cycle 5 31 true (0),
.cycle 12 8 true (0),
.cycle 3 13 true (0),
.cycle 4 13 true (0),
.cycle 1 19 true (0),
.cycle 23 1 false (-1),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 1 17 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 1 18 true (0),
.cycle 21 1 false (-1)
])
theorem kid23_part278_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part278) = true := by rfl

def kid23_part279 : Audit := .cycle 13 1 false (-1)
theorem kid23_part279_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part279) = true := by rfl

def kid23_part280 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 24 2 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.cycle 35 2 false (1),
.last 13 (2,true),
.cycle 19 2 false (1),
.cycle 14 2 false (0),
.cycle 16 2 false (4),
.cycle 30 2 false (-2),
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.cycle 21 2 false (-1),
.last 13 (2,true),
.cycle 5 8 true (0),
.cycle 15 2 false (-1),
.cycle 21 2 false (-1)
])
theorem kid23_part280_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part280) = true := by rfl

def kid23_part281 : Audit := .split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 16 9 false (2),
.last 23 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2176, 64, 128, 128, 256, 8, 128, 64, 256, 4096],[128, 2048, 4096, 1, 128, 256, 128, 2048, 4096, 1, 2176, 128, 4096],4096⟩,
.cycle 16 7 false (2),
.cycle 15 29 false (3),
.cycle 1 23 true (-1),
.cycle 54 31 true (2),
.last 23 (2,true),
.cycle 0 24 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 1, 7, 64],[2, 32, 64, 1, 50, 16, 64],64⟩,
.cycle 22 28 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 6, 64],[2, 32, 64, 1, 34, 32, 64],64⟩,
.cycle 21 2 true (1),
.last 23 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 6, 64],[2, 32, 64, 1, 34, 34, 64],64⟩,
.cycle 16 7 false (2),
.cycle 21 8 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 1, 6, 64],[2, 32, 64, 1, 35, 1, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 6, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 23 (2,true),
.cycle 0 24 true (-1),
.cycle 15 9 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 6, 64],[2, 32, 64, 1, 34, 32, 64],64⟩
])
theorem kid23_part281_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part281) = true := by rfl

def kid23_part282 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 17 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 5 false (1),
.cycle 1 18 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 4, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 15 5 false (1),
.last 20 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 4, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part282_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part282) = true := by rfl

def kid23_part283 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 16 5 false (0),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.last 22 (5,true),
.cycle 0 14 true (0),
.cycle 2 15 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 1 13 true (1),
.last 22 (5,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.last 13 (5,true)
])
theorem kid23_part283_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part283) = true := by rfl

def kid23_part284 : Audit := .cycle 1 13 true (1)
theorem kid23_part284_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part284) = true := by rfl

def kid23_part285 : Audit := .cycle 13 3 false (1)
theorem kid23_part285_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part285) = true := by rfl

def kid23_part286 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 16 5 false (0),
.last 13 (2,true),
.cycle 7 8 true (1),
.cycle 14 3 false (0),
.cycle 13 7 false (1),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 5 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.cycle 13 7 false (1),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part286_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part286) = true := by rfl

def kid23_part262 : Audit := .split 11 (4,false) (byMove [(kid23_part263),(kid23_part264),(kid23_part265),(kid23_part266),(kid23_part267),(kid23_part268),(kid23_part269),(kid23_part270),(kid23_part271),(kid23_part272),(kid23_part273),(kid23_part274),(kid23_part275),(kid23_part276),(kid23_part277),(kid23_part278),(kid23_part279),(kid23_part280),(kid23_part281),(kid23_part282),(kid23_part283),(kid23_part284),(kid23_part285),(kid23_part286)])

theorem kid23_part262_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part262) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid23_part263),(kid23_part264),(kid23_part265),(kid23_part266),(kid23_part267),(kid23_part268),(kid23_part269),(kid23_part270),(kid23_part271),(kid23_part272),(kid23_part273),(kid23_part274),(kid23_part275),(kid23_part276),(kid23_part277),(kid23_part278),(kid23_part279),(kid23_part280),(kid23_part281),(kid23_part282),(kid23_part283),(kid23_part284),(kid23_part285),(kid23_part286)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part263_checked

  · exact kid23_part269_checked

  · exact kid23_part275_checked

  · exact kid23_part281_checked

  · exact kid23_part264_checked

  · exact kid23_part270_checked

  · exact kid23_part276_checked

  · exact kid23_part282_checked

  · exact kid23_part265_checked

  · exact kid23_part271_checked

  · exact kid23_part277_checked

  · exact kid23_part283_checked

  · exact kid23_part266_checked

  · exact kid23_part272_checked

  · exact kid23_part278_checked

  · exact kid23_part284_checked

  · exact kid23_part267_checked

  · exact kid23_part273_checked

  · exact kid23_part279_checked

  · exact kid23_part285_checked

  · exact kid23_part268_checked

  · exact kid23_part274_checked

  · exact kid23_part280_checked

  · exact kid23_part286_checked

def kid23_part288 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 17 5 false (2),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 12 8 true (1),
.cycle 1 16 true (1),
.cycle 12 34 true (-1),
.cycle 1 15 true (1),
.cycle 17 5 false (2),
.cycle 12 4 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 12 6 true (1)
])
theorem kid23_part288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part288) = true := by rfl

def kid23_part289 : Audit := .cycle 0 14 true (0)
theorem kid23_part289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part289) = true := by rfl

def kid23_part290 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (0),
.last 23 (4,false),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.last 21 (4,false),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 18 21 true (1),
.cycle 12 9 true (0),
.cycle 28 1 false (2),
.last 19 (4,false),
.last 20 (4,false),
.cycle 25 1 false (1),
.cycle 18 5 false (2),
.cycle 1 22 true (0),
.cycle 1 20 true (0),
.last 21 (4,false),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 1 21 true (0),
.last 19 (4,false),
.cycle 23 1 false (1)
])
theorem kid23_part290_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part290) = true := by rfl

def kid23_part291 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131200, 262144, 262144, 8192, 16384, 8, 128, 262144, 262400, 128, 256, 8, 128, 262144, 256, 262144],[128, 2048, 2, 1, 262146, 16640, 8192, 131072, 2, 1, 131074, 128, 128, 2048, 2, 1, 131072, 128, 262144],330800⟩,
.cycle 0 25 true (0),
.cycle 3 13 true (0),
.last 16 (4,false),
.last 17 (4,false),
.cycle 27 1 false (1),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.cycle 18 1 false (0),
.cycle 23 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 25 1 false (1)
])
theorem kid23_part291_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part291) = true := by rfl

def kid23_part292 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 16 11 false (0),
.last 12 (2,true),
.last 15 (2,true),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 11 4 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 19 8 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 6 false (1),
.cycle 15 4 false (0)
])
theorem kid23_part292_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part292) = true := by rfl

def kid23_part293 : Audit := .split 14 (4,false) (byMove [
.last 21 (2,true),
.cycle 24 12 false (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 24 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.cycle 13 7 false (-1),
.last 16 (2,true),
.last 28 (2,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 29 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.last 28 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 0, 16, 64],64⟩,
.cycle 11 4 false (1)
])
theorem kid23_part293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part293) = true := by rfl

def kid23_part294 : Audit := .cycle 1 11 true (1)
theorem kid23_part294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part294) = true := by rfl

def kid23_part295 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (0),
.last 73 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.cycle 18 1 false (-2),
.cycle 0 20 true (0),
.cycle 7 10 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.last 62 (2,true),
.cycle 13 4 true (1),
.cycle 14 2 true (1),
.cycle 17 10 false (2),
.last 19 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.cycle 18 1 false (-2),
.cycle 20 2 false (0),
.cycle 28 12 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 26 10 false (2),
.cycle 20 4 false (2)
])
theorem kid23_part295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part295) = true := by rfl

def kid23_part296 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 12 8 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 12 true (0),
.cycle 21 8 true (2),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (2),
.cycle 14 8 true (2),
.cycle 0 14 true (0),
.cycle 12 8 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 15 (4,false)
])
theorem kid23_part296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part296) = true := by rfl

def kid23_part297 : Audit := .cycle 0 12 true (0)
theorem kid23_part297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part297) = true := by rfl

def kid23_part298 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (0),
.proven (BB6.Agent11Raw39Pumps.M2495.table) (fun m hm => BB6.Agent11Raw39Pumps.M2495.never m hm),
.last 14 (2,true),
.last 17 (2,true),
.cycle 16 1 false (-2),
.cycle 15 2 false (1),
.cycle 7 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 8 true (0),
.cycle 11 4 true (1),
.cycle 12 2 true (1),
.cycle 15 8 false (2),
.last 18 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.cycle 16 1 false (-2),
.cycle 16 2 false (0),
.cycle 23 10 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 21 8 false (1),
.cycle 17 4 false (1)
])
theorem kid23_part298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part298) = true := by rfl

def kid23_part299 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (2,true),
.cycle 25 1 false (1),
.cycle 18 1 false (-2),
.cycle 17 2 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (0),
.cycle 3 31 true (0),
.cycle 13 1 true (3),
.cycle 12 2 true (3),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 23 true (0),
.cycle 18 1 false (-2),
.cycle 18 2 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 22 4 false (2)
])
theorem kid23_part299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part299) = true := by rfl

def kid23_part300 : Audit := .cycle 12 8 true (1)
theorem kid23_part300_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part300) = true := by rfl

def kid23_part301 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 23 (4,false),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 1 13 true (1),
.last 27 (4,false),
.cycle 21 2 true (3),
.cycle 0 14 true (0),
.last 23 (4,false),
.last 17 (4,false),
.cycle 14 2 true (2),
.cycle 13 2 true (1),
.cycle 18 2 true (2),
.cycle 5 8 true (1),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 1 13 true (1),
.cycle 16 2 true (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 14 2 true (1),
.cycle 13 2 true (2)
])
theorem kid23_part301_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part301) = true := by rfl

def kid23_part302 : Audit := .cycle 1 13 true (1)
theorem kid23_part302_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part302) = true := by rfl

def kid23_part303 : Audit := .cycle 1 17 true (0)
theorem kid23_part303_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part303) = true := by rfl

def kid23_part304 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.last 42 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 6 6 true (1),
.last 20 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 14 4 true (-2),
.cycle 10 2 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 21 8 false (2),
.last 20 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 11 6 false (2),
.cycle 17 4 false (-1)
])
theorem kid23_part304_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part304) = true := by rfl

def kid23_part305 : Audit := .split 14 (4,false) (byMove [
.cycle 16 41 true (-2),
.cycle 13 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 19 7 false (0),
.last 16 (2,true),
.cycle 1 35 true (-2),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.cycle 13 7 false (-1),
.last 16 (2,true),
.cycle 21 9 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 19 8 false (-1),
.last 16 (2,true),
.cycle 1 35 true (-2),
.cycle 21 9 false (0),
.cycle 13 6 false (0),
.cycle 11 4 false (1)
])
theorem kid23_part305_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part305) = true := by rfl

def kid23_part306 : Audit := .cycle 1 11 true (1)
theorem kid23_part306_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part306) = true := by rfl

def kid23_part307 : Audit := .cycle 7 4 true (2)
theorem kid23_part307_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part307) = true := by rfl

def kid23_part308 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 18 (4,false),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 16 (4,false),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 16 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (2)
])
theorem kid23_part308_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part308) = true := by rfl

def kid23_part309 : Audit := .cycle 0 12 true (0)
theorem kid23_part309_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part309) = true := by rfl

def kid23_part310 : Audit := .cycle 9 2 true (2)
theorem kid23_part310_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part310) = true := by rfl

def kid23_part311 : Audit := .cycle 8 4 true (2)
theorem kid23_part311_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part311) = true := by rfl

def kid23_part287 : Audit := .split 10 (5,true) (byMove [(kid23_part288),(kid23_part289),(kid23_part290),(kid23_part291),(kid23_part292),(kid23_part293),(kid23_part294),(kid23_part295),(kid23_part296),(kid23_part297),(kid23_part298),(kid23_part299),(kid23_part300),(kid23_part301),(kid23_part302),(kid23_part303),(kid23_part304),(kid23_part305),(kid23_part306),(kid23_part307),(kid23_part308),(kid23_part309),(kid23_part310),(kid23_part311)])

theorem kid23_part287_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part287) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part288),(kid23_part289),(kid23_part290),(kid23_part291),(kid23_part292),(kid23_part293),(kid23_part294),(kid23_part295),(kid23_part296),(kid23_part297),(kid23_part298),(kid23_part299),(kid23_part300),(kid23_part301),(kid23_part302),(kid23_part303),(kid23_part304),(kid23_part305),(kid23_part306),(kid23_part307),(kid23_part308),(kid23_part309),(kid23_part310),(kid23_part311)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part288_checked

  · exact kid23_part294_checked

  · exact kid23_part300_checked

  · exact kid23_part306_checked

  · exact kid23_part289_checked

  · exact kid23_part295_checked

  · exact kid23_part301_checked

  · exact kid23_part307_checked

  · exact kid23_part290_checked

  · exact kid23_part296_checked

  · exact kid23_part302_checked

  · exact kid23_part308_checked

  · exact kid23_part291_checked

  · exact kid23_part297_checked

  · exact kid23_part303_checked

  · exact kid23_part309_checked

  · exact kid23_part292_checked

  · exact kid23_part298_checked

  · exact kid23_part304_checked

  · exact kid23_part310_checked

  · exact kid23_part293_checked

  · exact kid23_part299_checked

  · exact kid23_part305_checked

  · exact kid23_part311_checked

def kid23_part312 : Audit := .cycle 0 10 true (0)
theorem kid23_part312_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part312) = true := by rfl

def kid23_part313 : Audit := .cycle 1 9 true (1)
theorem kid23_part313_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part313) = true := by rfl

def kid23_part314 : Audit := .cycle 2 8 true (1)
theorem kid23_part314_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part314) = true := by rfl

def kid23_part315 : Audit := .cycle 1 12 true (1)
theorem kid23_part315_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part315) = true := by rfl

def kid23_part316 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 19 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 33 1 false (1),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 9 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
]),
.cycle 0 12 true (0),
.cycle 9 2 true (3),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.cycle 21 2 false (1),
.cycle 21 2 false (1),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 4 true (2),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 9 10 true (3),
.cycle 49 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.cycle 9 20 true (3),
.cycle 10 10 true (3),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 9 11 true (3),
.last 24 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 10 9 true (3),
.cycle 8 11 true (3)
]),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 10 2 true (4),
.cycle 6 5 true (2),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.last 24 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 15 (2,true),
.cycle 10 4 true (3),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 5 true (3),
.last 24 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 8 5 true (3)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 34 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 9 5 true (2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true)
]),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 31 2 false (3),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 9 5 true (2),
.cycle 17 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 8 5 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 8 3 true (3)
])
theorem kid23_part316_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part316) = true := by rfl

def kid23_part317 : Audit := .cycle 8 2 true (3)
theorem kid23_part317_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part317) = true := by rfl

def kid23_part101 : Audit := .split 9 (4,true) (byMove [(kid23_part102),(kid23_part103),(kid23_part104),(kid23_part129),(kid23_part130),(kid23_part131),(kid23_part156),(kid23_part157),(kid23_part158),(kid23_part183),(kid23_part184),(kid23_part185),(kid23_part210),(kid23_part211),(kid23_part236),(kid23_part261),(kid23_part262),(kid23_part287),(kid23_part312),(kid23_part313),(kid23_part314),(kid23_part315),(kid23_part316),(kid23_part317)])

theorem kid23_part101_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (kid23_part101) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) 9 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part102),(kid23_part103),(kid23_part104),(kid23_part129),(kid23_part130),(kid23_part131),(kid23_part156),(kid23_part157),(kid23_part158),(kid23_part183),(kid23_part184),(kid23_part185),(kid23_part210),(kid23_part211),(kid23_part236),(kid23_part261),(kid23_part262),(kid23_part287),(kid23_part312),(kid23_part313),(kid23_part314),(kid23_part315),(kid23_part316),(kid23_part317)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part102_checked

  · exact kid23_part156_checked

  · exact kid23_part210_checked

  · exact kid23_part312_checked

  · exact kid23_part103_checked

  · exact kid23_part157_checked

  · exact kid23_part211_checked

  · exact kid23_part313_checked

  · exact kid23_part104_checked

  · exact kid23_part158_checked

  · exact kid23_part236_checked

  · exact kid23_part314_checked

  · exact kid23_part129_checked

  · exact kid23_part183_checked

  · exact kid23_part261_checked

  · exact kid23_part315_checked

  · exact kid23_part130_checked

  · exact kid23_part184_checked

  · exact kid23_part262_checked

  · exact kid23_part316_checked

  · exact kid23_part131_checked

  · exact kid23_part185_checked

  · exact kid23_part287_checked

  · exact kid23_part317_checked

def kid23_part319 : Audit := .cycle 1 10 true (1)
theorem kid23_part319_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part319) = true := by rfl

def kid23_part320 : Audit := .cycle 1 12 true (1)
theorem kid23_part320_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part320) = true := by rfl

def kid23_part321 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 16 1 false (0),
.cycle 13 6 false (2),
.last 18 (4,true),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 19 1 false (-1)
]),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 27 1 false (3),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (3),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (4,true),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 18 1 false (0),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 28 1 false (2),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 39 1 false (3)
]),
.cycle 16 1 false (0),
.cycle 17 5 false (2),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (0),
.cycle 1 12 true (1),
.cycle 29 1 false (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 25 1 false (1),
.last 16 (4,true),
.last 18 (4,true),
.last 20 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (0),
.cycle 1 12 true (1),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true)
]),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 29 1 false (1),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 10 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 29 1 false (1),
.cycle 6 6 true (2),
.cycle 9 4 true (2),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 27 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2)
]),
.cycle 25 1 false (1)
])
theorem kid23_part321_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part321) = true := by rfl

def kid23_part322 : Audit := .cycle 0 11 true (0)
theorem kid23_part322_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part322) = true := by rfl

def kid23_part324 : Audit := .cycle 0 11 true (0)
theorem kid23_part324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part324) = true := by rfl

def kid23_part325 : Audit := .cycle 1 10 true (1)
theorem kid23_part325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part325) = true := by rfl

def kid23_part326 : Audit := .cycle 21 1 false (1)
theorem kid23_part326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part326) = true := by rfl

def kid23_part327 : Audit := .cycle 1 13 true (0)
theorem kid23_part327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part327) = true := by rfl

def kid23_part328 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 15 11 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 16 1 false (0),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 15 3 false (0)
])
theorem kid23_part328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part328) = true := by rfl

def kid23_part329 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (4),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 24 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 14 1 false (0),
.cycle 19 1 false (-3),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 28 1 false (-2),
.cycle 1 13 false (4),
.cycle 23 1 false (-1),
.cycle 1 16 true (-1),
.cycle 13 1 true (-1),
.cycle 11 3 false (1)
])
theorem kid23_part329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part329) = true := by rfl

def kid23_part330 : Audit := .cycle 0 11 true (0)
theorem kid23_part330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part330) = true := by rfl

def kid23_part331 : Audit := .cycle 1 10 true (1)
theorem kid23_part331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part331) = true := by rfl

def kid23_part332 : Audit := .cycle 0 23 true (0)
theorem kid23_part332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part332) = true := by rfl

def kid23_part333 : Audit := .cycle 27 1 false (3)
theorem kid23_part333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part333) = true := by rfl

def kid23_part334 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (3),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 18 1 false (0),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 28 1 false (2),
.cycle 18 1 false (4),
.cycle 16 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 21 3 false (2)
])
theorem kid23_part334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part334) = true := by rfl

def kid23_part335 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 false (4),
.cycle 26 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 16 true (-1),
.cycle 26 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 true (-1),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.last 17 (2,true),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 32 1 false (0),
.cycle 1 15 false (4),
.cycle 25 1 false (1),
.cycle 1 18 true (-1),
.cycle 15 1 true (-1),
.cycle 13 3 false (1)
])
theorem kid23_part335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part335) = true := by rfl

def kid23_part336 : Audit := .cycle 17 5 false (2)
theorem kid23_part336_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part336) = true := by rfl

def kid23_part337 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 22 (4,false),
.cycle 19 7 false (1),
.cycle 16 5 false (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 17 5 false (1)
])
theorem kid23_part337_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part337) = true := by rfl

def kid23_part338 : Audit := .cycle 0 13 true (0)
theorem kid23_part338_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part338) = true := by rfl

def kid23_part339 : Audit := .cycle 18 1 false (0)
theorem kid23_part339_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part339) = true := by rfl

def kid23_part340 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.last 32 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 1 12 true (1),
.cycle 1 15 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 18 1 false (0),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 1 12 true (1),
.cycle 14 5 false (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0)
])
theorem kid23_part340_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part340) = true := by rfl

def kid23_part341 : Audit := .split 13 (4,false) (byMove [
.cycle 0 30 true (-2),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 14 1 false (0),
.cycle 19 1 false (-3),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 0 26 true (-1),
.last 18 (2,true),
.cycle 25 1 false (-3),
.cycle 11 3 false (1)
])
theorem kid23_part341_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part341) = true := by rfl

def kid23_part342 : Audit := .cycle 0 11 true (0)
theorem kid23_part342_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part342) = true := by rfl

def kid23_part343 : Audit := .cycle 1 10 true (1)
theorem kid23_part343_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part343) = true := by rfl

def kid23_part344 : Audit := .cycle 2 9 true (1)
theorem kid23_part344_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part344) = true := by rfl

def kid23_part345 : Audit := .cycle 1 13 true (1)
theorem kid23_part345_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part345) = true := by rfl

def kid23_part346 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 15 15 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 16 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 10 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 20 1 false (0),
.cycle 6 6 true (2),
.cycle 9 4 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.cycle 16 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2)
])
theorem kid23_part346_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part346) = true := by rfl

def kid23_part347 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 15 13 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 30 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 18 1 false (0),
.cycle 15 8 false (2),
.last 21 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 19 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 17 3 false (1)
])
theorem kid23_part347_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part347) = true := by rfl

def kid23_part323 : Audit := .split 10 (4,true) (byMove [(kid23_part324),(kid23_part325),(kid23_part326),(kid23_part327),(kid23_part328),(kid23_part329),(kid23_part330),(kid23_part331),(kid23_part332),(kid23_part333),(kid23_part334),(kid23_part335),(kid23_part336),(kid23_part337),(kid23_part338),(kid23_part339),(kid23_part340),(kid23_part341),(kid23_part342),(kid23_part343),(kid23_part344),(kid23_part345),(kid23_part346),(kid23_part347)])

theorem kid23_part323_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part323) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part324),(kid23_part325),(kid23_part326),(kid23_part327),(kid23_part328),(kid23_part329),(kid23_part330),(kid23_part331),(kid23_part332),(kid23_part333),(kid23_part334),(kid23_part335),(kid23_part336),(kid23_part337),(kid23_part338),(kid23_part339),(kid23_part340),(kid23_part341),(kid23_part342),(kid23_part343),(kid23_part344),(kid23_part345),(kid23_part346),(kid23_part347)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part324_checked

  · exact kid23_part330_checked

  · exact kid23_part336_checked

  · exact kid23_part342_checked

  · exact kid23_part325_checked

  · exact kid23_part331_checked

  · exact kid23_part337_checked

  · exact kid23_part343_checked

  · exact kid23_part326_checked

  · exact kid23_part332_checked

  · exact kid23_part338_checked

  · exact kid23_part344_checked

  · exact kid23_part327_checked

  · exact kid23_part333_checked

  · exact kid23_part339_checked

  · exact kid23_part345_checked

  · exact kid23_part328_checked

  · exact kid23_part334_checked

  · exact kid23_part340_checked

  · exact kid23_part346_checked

  · exact kid23_part329_checked

  · exact kid23_part335_checked

  · exact kid23_part341_checked

  · exact kid23_part347_checked

def kid23_part348 : Audit := .cycle 13 1 false (-1)
theorem kid23_part348_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part348) = true := by rfl

def kid23_part349 : Audit := .cycle 0 10 true (0)
theorem kid23_part349_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part349) = true := by rfl

def kid23_part350 : Audit := .cycle 1 9 true (1)
theorem kid23_part350_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part350) = true := by rfl

def kid23_part351 : Audit := .cycle 9 8 true (2)
theorem kid23_part351_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part351) = true := by rfl

def kid23_part352 : Audit := .cycle 3 7 true (1)
theorem kid23_part352_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part352) = true := by rfl

def kid23_part353 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 10 true (0),
.cycle 33 1 false (3),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 21 1 false (1)
]),
.cycle 18 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 20 true (2),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (2),
.cycle 9 18 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 62, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 15 true (2),
.cycle 7 15 true (2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 22 (2,true),
.last 24 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 20 true (2),
.cycle 9 26 true (2)
]),
.cycle 9 8 true (2),
.cycle 10 1 true (4),
.cycle 22 1 false (2),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 11 true (3),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.cycle 8 6 true (3),
.cycle 6 7 true (2),
.cycle 9 5 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 6 true (3),
.cycle 8 5 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 2 19 true (0),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 6 7 true (2),
.cycle 9 5 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 26 1 false (6),
.cycle 21 1 false (1),
.cycle 14 11 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 4 15 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 6 7 true (2),
.cycle 9 5 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 13 3 true (3),
.cycle 9 14 true (2)
]),
.cycle 18 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 8 3 true (3)
])
theorem kid23_part353_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part353) = true := by rfl

def kid23_part354 : Audit := .cycle 17 1 false (1)
theorem kid23_part354_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part354) = true := by rfl

def kid23_part355 : Audit := .cycle 6 4 true (2)
theorem kid23_part355_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part355) = true := by rfl

def kid23_part356 : Audit := .cycle 9 2 true (2)
theorem kid23_part356_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part356) = true := by rfl

def kid23_part357 : Audit := .split 10 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 20 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.last 18 (4,true),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 13 (4,true),
.last 20 (4,true),
.cycle 13 6 false (2),
.last 18 (4,true),
.cycle 12 8 true (-2),
.last 16 (4,true),
.last 12 (4,true),
.last 18 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 12 10 true (-2)
]),
.cycle 20 1 false (0),
.cycle 1 11 true (1),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 64, 47, 64],[2, 32, 4, 1, 64, 5, 64],80⟩,
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (3),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 0 17 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 42 (4,false),
.cycle 0 23 true (0),
.last 12 (4,false),
.cycle 0 19 true (-1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 28 1 false (2),
.last 12 (4,false),
.last 20 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 0 16 true (0)
]),
.cycle 0 14 true (0),
.cycle 12 4 true (1),
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.last 21 (4,true),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.last 19 (4,true),
.cycle 6 6 true (1),
.cycle 9 4 true (1),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 1 15 true (1),
.last 16 (4,true),
.last 18 (4,true),
.last 20 (4,true),
.last 17 (4,true),
.last 12 (4,true),
.last 19 (4,true),
.last 17 (4,true),
.last 15 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true)
]),
.cycle 27 1 false (1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 2 10 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 17 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 10 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 0 17 true (0),
.cycle 6 6 true (2),
.cycle 9 4 true (2),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid23_part357_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part357) = true := by rfl

def kid23_part358 : Audit := .cycle 1 11 true (1)
theorem kid23_part358_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part358) = true := by rfl

def kid23_part360 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 12 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 19 7 false (3),
.cycle 12 8 true (1),
.cycle 12 6 true (1),
.cycle 24 12 true (0),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 12 6 true (1)
])
theorem kid23_part360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part360) = true := by rfl

def kid23_part361 : Audit := .cycle 0 14 true (0)
theorem kid23_part361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part361) = true := by rfl

def kid23_part362 : Audit := .split 19 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 11 10 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 20 1 false (0),
.cycle 26 1 false (2),
.last 47 (4,false),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 20 1 false (2),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 28 1 false (2),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 20 1 false (0),
.cycle 17 6 true (1),
.cycle 1 21 true (0),
.cycle 0 22 true (0),
.cycle 28 1 false (2),
.last 20 (4,false),
.last 22 (4,false)
])
theorem kid23_part362_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part362) = true := by rfl

def kid23_part363 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131072, 262144, 393480, 8192, 16384, 8, 128, 262144, 262400, 128, 256, 8, 128, 262144, 256, 262144],[128, 2048, 2, 1, 16640, 262144, 8192, 131072, 2, 1, 128, 131074, 128, 2048, 2, 1, 128, 131072, 262144],330800⟩,
.cycle 39 1 false (1),
.cycle 3 13 true (0),
.last 16 (4,false),
.cycle 20 1 false (0),
.cycle 27 1 false (1),
.cycle 25 1 false (1),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 25 1 false (1)
])
theorem kid23_part363_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part363) = true := by rfl

def kid23_part364 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 21 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.cycle 14 2 true (-1),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 24 true (-1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.cycle 13 6 false (1)
])
theorem kid23_part364_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part364) = true := by rfl

def kid23_part365 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-1),
.cycle 11 4 true (-1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 12 2 true (-1),
.cycle 12 6 false (0),
.last 15 (2,true),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 12 3 false (0),
.cycle 16 1 false (-2)
])
theorem kid23_part365_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part365) = true := by rfl

def kid23_part366 : Audit := .cycle 1 11 true (1)
theorem kid23_part366_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part366) = true := by rfl

def kid23_part367 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.last 27 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (-2),
.cycle 1 15 true (1),
.cycle 11 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 2 true (2),
.cycle 16 8 true (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 35 1 false (1),
.cycle 26 1 false (2),
.cycle 18 1 false (-2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 9 6 true (2)
])
theorem kid23_part367_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part367) = true := by rfl

def kid23_part368 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (3),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131076, 262144, 393228, 8192, 16384, 8, 128, 262144, 262152, 128, 256, 8, 128, 262144, 8, 262144],[128, 2048, 4, 1, 4, 262144, 8192, 131072, 4, 1, 4, 4, 128, 2048, 4, 1, 4, 4, 262144],330800⟩,
.cycle 0 23 true (0),
.last 12 (4,false),
.last 17 (4,false),
.cycle 7 6 true (2),
.cycle 9 6 true (2),
.cycle 0 14 true (0),
.cycle 28 1 false (2),
.last 12 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 14 (4,false)
])
theorem kid23_part368_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part368) = true := by rfl

def kid23_part369 : Audit := .cycle 0 12 true (0)
theorem kid23_part369_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part369) = true := by rfl

def kid23_part370 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (0),
.cycle 33 1 false (3),
.cycle 17 1 false (1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131088, 4, 393244, 8192, 16384, 8, 128, 4, 262148, 128, 256, 8, 128, 4, 4, 262144],[128, 2048, 262144, 1, 16, 262144, 8192, 131072, 262144, 1, 16, 16, 128, 2048, 262144, 1, 16, 16, 262144],264224⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 8, 63, 64],[2, 32, 64, 1, 16, 17, 64],64⟩,
.cycle 12 1 true (4),
.cycle 18 2 true (-1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 11 true (0),
.cycle 21 1 false (5),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 7 true (2)
])
theorem kid23_part370_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part370) = true := by rfl

def kid23_part371 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 23 (2,true),
.last 17 (2,true),
.cycle 15 1 false (1),
.cycle 16 1 false (-2),
.cycle 1 13 true (1),
.cycle 11 4 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 11 2 true (2),
.cycle 14 6 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (-2),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 5 false (2),
.cycle 9 4 true (2)
])
theorem kid23_part371_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part371) = true := by rfl

def kid23_part372 : Audit := .cycle 12 4 true (1)
theorem kid23_part372_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part372) = true := by rfl

def kid23_part373 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 1 13 true (1),
.last 16 (4,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131076, 262144, 393228, 8192, 16384, 8, 128, 262144, 262152, 128, 256, 8, 128, 262144, 8, 262144],[128, 2048, 4, 1, 4, 262144, 8192, 131072, 4, 1, 4, 4, 128, 2048, 4, 1, 4, 4, 262144],330800⟩,
.cycle 0 14 true (0),
.last 16 (4,false),
.last 14 (4,false),
.cycle 17 9 false (2),
.cycle 16 5 false (1),
.cycle 13 12 true (-1),
.cycle 5 8 true (1),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 1 13 true (1),
.cycle 15 11 false (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 16 9 false (2),
.cycle 16 7 false (2)
])
theorem kid23_part373_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part373) = true := by rfl

def kid23_part374 : Audit := .cycle 1 13 true (1)
theorem kid23_part374_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part374) = true := by rfl

def kid23_part375 : Audit := .cycle 23 1 false (1)
theorem kid23_part375_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part375) = true := by rfl

def kid23_part376 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 1 37 true (-2),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 6 true (1),
.cycle 9 4 true (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 7 false (3),
.cycle 15 5 false (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.cycle 14 3 false (0)
])
theorem kid23_part376_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part376) = true := by rfl

def kid23_part377 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 35 1 false (-3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 11 4 true (-1),
.last 14 (2,true),
.cycle 27 1 false (1),
.cycle 15 1 false (-1),
.cycle 12 2 true (-1),
.cycle 12 6 false (0),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 30 1 false (-2),
.cycle 12 3 false (0),
.cycle 16 1 false (-2)
])
theorem kid23_part377_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part377) = true := by rfl

def kid23_part378 : Audit := .cycle 1 11 true (1)
theorem kid23_part378_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part378) = true := by rfl

def kid23_part379 : Audit := .cycle 7 4 true (2)
theorem kid23_part379_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part379) = true := by rfl

def kid23_part380 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 15 (4,false),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 10 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 6 6 true (2),
.cycle 9 4 true (2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (2)
])
theorem kid23_part380_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part380) = true := by rfl

def kid23_part381 : Audit := .cycle 0 12 true (0)
theorem kid23_part381_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part381) = true := by rfl

def kid23_part382 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 11 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 8 6 true (2),
.cycle 6 7 true (2),
.cycle 9 5 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.cycle 10 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (2)
])
theorem kid23_part382_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part382) = true := by rfl

def kid23_part383 : Audit := .cycle 9 2 true (2)
theorem kid23_part383_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part383) = true := by rfl

def kid23_part359 : Audit := .split 10 (4,true) (byMove [(kid23_part360),(kid23_part361),(kid23_part362),(kid23_part363),(kid23_part364),(kid23_part365),(kid23_part366),(kid23_part367),(kid23_part368),(kid23_part369),(kid23_part370),(kid23_part371),(kid23_part372),(kid23_part373),(kid23_part374),(kid23_part375),(kid23_part376),(kid23_part377),(kid23_part378),(kid23_part379),(kid23_part380),(kid23_part381),(kid23_part382),(kid23_part383)])

theorem kid23_part359_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part359) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part360),(kid23_part361),(kid23_part362),(kid23_part363),(kid23_part364),(kid23_part365),(kid23_part366),(kid23_part367),(kid23_part368),(kid23_part369),(kid23_part370),(kid23_part371),(kid23_part372),(kid23_part373),(kid23_part374),(kid23_part375),(kid23_part376),(kid23_part377),(kid23_part378),(kid23_part379),(kid23_part380),(kid23_part381),(kid23_part382),(kid23_part383)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part360_checked

  · exact kid23_part366_checked

  · exact kid23_part372_checked

  · exact kid23_part378_checked

  · exact kid23_part361_checked

  · exact kid23_part367_checked

  · exact kid23_part373_checked

  · exact kid23_part379_checked

  · exact kid23_part362_checked

  · exact kid23_part368_checked

  · exact kid23_part374_checked

  · exact kid23_part380_checked

  · exact kid23_part363_checked

  · exact kid23_part369_checked

  · exact kid23_part375_checked

  · exact kid23_part381_checked

  · exact kid23_part364_checked

  · exact kid23_part370_checked

  · exact kid23_part376_checked

  · exact kid23_part382_checked

  · exact kid23_part365_checked

  · exact kid23_part371_checked

  · exact kid23_part377_checked

  · exact kid23_part383_checked

def kid23_part384 : Audit := .cycle 13 1 false (-1)
theorem kid23_part384_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part384) = true := by rfl

def kid23_part385 : Audit := .cycle 0 10 true (0)
theorem kid23_part385_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part385) = true := by rfl

def kid23_part386 : Audit := .cycle 1 9 true (1)
theorem kid23_part386_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part386) = true := by rfl

def kid23_part387 : Audit := .cycle 2 8 true (1)
theorem kid23_part387_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part387) = true := by rfl

def kid23_part388 : Audit := .cycle 1 12 true (1)
theorem kid23_part388_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part388) = true := by rfl

def kid23_part389 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 10 true (2),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 23 1 false (1),
.cycle 6 6 true (2),
.cycle 9 4 true (2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 10 true (2),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 23 1 false (1),
.cycle 6 6 true (2),
.cycle 9 4 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 9 true (3),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 8 4 true (3),
.cycle 6 5 true (2),
.cycle 9 3 true (3),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 22 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 9 5 true (2),
.last 14 (4,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.cycle 9 3 true (3),
.cycle 9 5 true (2),
.cycle 9 7 true (2),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.cycle 11 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 9 3 true (3)
]),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 20 1 false (-2),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 11 true (3),
.cycle 3 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 6 true (3),
.cycle 6 7 true (2),
.cycle 9 5 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 20 1 false (-2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 8 5 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 8 3 true (3)
])
theorem kid23_part389_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part389) = true := by rfl

def kid23_part390 : Audit := .cycle 8 2 true (3)
theorem kid23_part390_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part390) = true := by rfl

def kid23_part318 : Audit := .split 9 (5,true) (byMove [(kid23_part319),(kid23_part320),(kid23_part321),(kid23_part322),(kid23_part323),(kid23_part348),(kid23_part349),(kid23_part350),(kid23_part351),(kid23_part352),(kid23_part353),(kid23_part354),(kid23_part355),(kid23_part356),(kid23_part357),(kid23_part358),(kid23_part359),(kid23_part384),(kid23_part385),(kid23_part386),(kid23_part387),(kid23_part388),(kid23_part389),(kid23_part390)])

theorem kid23_part318_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (kid23_part318) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) 9 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part319),(kid23_part320),(kid23_part321),(kid23_part322),(kid23_part323),(kid23_part348),(kid23_part349),(kid23_part350),(kid23_part351),(kid23_part352),(kid23_part353),(kid23_part354),(kid23_part355),(kid23_part356),(kid23_part357),(kid23_part358),(kid23_part359),(kid23_part384),(kid23_part385),(kid23_part386),(kid23_part387),(kid23_part388),(kid23_part389),(kid23_part390)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part319_checked

  · exact kid23_part349_checked

  · exact kid23_part355_checked

  · exact kid23_part385_checked

  · exact kid23_part320_checked

  · exact kid23_part350_checked

  · exact kid23_part356_checked

  · exact kid23_part386_checked

  · exact kid23_part321_checked

  · exact kid23_part351_checked

  · exact kid23_part357_checked

  · exact kid23_part387_checked

  · exact kid23_part322_checked

  · exact kid23_part352_checked

  · exact kid23_part358_checked

  · exact kid23_part388_checked

  · exact kid23_part323_checked

  · exact kid23_part353_checked

  · exact kid23_part359_checked

  · exact kid23_part389_checked

  · exact kid23_part348_checked

  · exact kid23_part354_checked

  · exact kid23_part384_checked

  · exact kid23_part390_checked

def kid23_part391 : Audit := .cycle 0 9 true (0)
theorem kid23_part391_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,0⟩)) (kid23_part391) = true := by rfl

def kid23_part392 : Audit := .cycle 1 8 true (1)
theorem kid23_part392_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,1⟩)) (kid23_part392) = true := by rfl

def kid23_part394 : Audit := .cycle 1 17 true (1)
theorem kid23_part394_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part394) = true := by rfl

def kid23_part395 : Audit := .cycle 7 10 true (3)
theorem kid23_part395_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part395) = true := by rfl

def kid23_part396 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 44 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 43 1 false (3),
.cycle 38 1 false (2),
.last 19 (4,false),
.cycle 1 35 true (1),
.cycle 7 13 true (3),
.last 25 (4,false),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 19 (4,false),
.last 21 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
]),
.cycle 2 17 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 9 true (3),
.cycle 3 15 true (1),
.split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 46 (4,true),
.cycle 10 9 true (3),
.cycle 18 1 true (6),
.cycle 9 35 true (3),
.cycle 7 13 true (3),
.cycle 17 3 true (5),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (4,true),
.cycle 17 3 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (3)
]),
.cycle 19 41 true (4),
.cycle 6 12 true (2),
.cycle 33 5 false (1),
.cycle 1 21 true (1),
.cycle 1 19 true (1),
.split 18 (4,true) (byMove [
.cycle 20 4 true (3),
.cycle 0 22 true (0),
.cycle 39 1 false (1),
.cycle 7 20 true (2),
.last 19 (4,false),
.cycle 0 22 true (0),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 20 (4,false),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 44 1 false (2),
.cycle 35 5 false (2),
.last 25 (4,false),
.cycle 1 21 true (1),
.cycle 34 1 false (0),
.last 19 (4,false),
.last 21 (4,false),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 17 2 true (4),
.cycle 0 20 true (0),
.last 20 (4,false),
.last 21 (4,false)
]),
.cycle 39 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.split 18 (4,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 17 2 true (5),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 2 21 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 18 1 true (6),
.cycle 2 30 true (1),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.last 20 (4,true),
.cycle 1 20 true (1),
.last 19 (4,true),
.cycle 51 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (3)
]),
.cycle 8 10 true (3)
])
theorem kid23_part396_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part396) = true := by rfl

def kid23_part397 : Audit := .cycle 0 18 true (0)
theorem kid23_part397_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part397) = true := by rfl

def kid23_part399 : Audit := .cycle 1 18 true (1)
theorem kid23_part399_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part399) = true := by rfl

def kid23_part400 : Audit := .cycle 7 11 true (3)
theorem kid23_part400_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part400) = true := by rfl

def kid23_part401 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 44 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 43 1 false (3),
.cycle 38 1 false (2),
.last 19 (4,false),
.cycle 1 35 true (1),
.cycle 7 13 true (3),
.cycle 37 1 false (-1),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 19 (4,false),
.cycle 18 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
])
theorem kid23_part401_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part401) = true := by rfl

def kid23_part402 : Audit := .cycle 0 19 true (0)
theorem kid23_part402_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part402) = true := by rfl

def kid23_part403 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 1 32 true (1),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 44 1 false (2),
.cycle 3 17 true (1),
.cycle 19 1 true (3),
.cycle 49 1 false (3),
.cycle 6 14 true (2),
.last 29 (2,true),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 23 1 false (-1),
.last 25 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (3),
.cycle 8 12 true (3)
])
theorem kid23_part403_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part403) = true := by rfl

def kid23_part404 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 1 32 true (1),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 32 1 false (0),
.cycle 26 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 44 1 false (2),
.cycle 3 17 true (1),
.cycle 19 1 true (3),
.cycle 49 1 false (3),
.cycle 6 14 true (2),
.last 36 (2,true),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.last 25 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (3),
.cycle 8 12 true (3)
])
theorem kid23_part404_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part404) = true := by rfl

def kid23_part405 : Audit := .cycle 0 18 true (0)
theorem kid23_part405_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part405) = true := by rfl

def kid23_part406 : Audit := .cycle 1 17 true (1)
theorem kid23_part406_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part406) = true := by rfl

def kid23_part407 : Audit := .cycle 9 9 true (3)
theorem kid23_part407_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part407) = true := by rfl

def kid23_part408 : Audit := .cycle 3 15 true (1)
theorem kid23_part408_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part408) = true := by rfl

def kid23_part409 : Audit := .split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 29 1 false (1),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 30 (2,true),
.cycle 10 9 true (3),
.cycle 18 1 true (6),
.last 35 (2,true),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 51 1 false (9),
.last 20 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (3)
])
theorem kid23_part409_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part409) = true := by rfl

def kid23_part410 : Audit := .split 30 (2,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.cycle 9 22 true (3),
.cycle 3 28 true (1),
.last 31 (4,false),
.cycle 18 13 true (4),
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 32, 4096, 128, 2048, 4, 1, 32, 4, 4096],5136⟩,
.cycle 20 11 true (4),
.last 31 (4,false),
.last 47 (4,false),
.cycle 7 25 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 32, 4096, 128, 2048, 4, 1, 32, 4, 4096],5136⟩,
.cycle 0 33 true (0),
.cycle 11 20 true (3),
.last 31 (4,false),
.cycle 29 2 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.cycle 2 29 true (1),
.cycle 1 33 true (1),
.last 31 (4,false),
.cycle 8 23 true (3)
])
theorem kid23_part410_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part410) = true := by rfl

def kid23_part411 : Audit := .cycle 6 12 true (2)
theorem kid23_part411_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part411) = true := by rfl

def kid23_part412 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (3),
.cycle 49 1 false (1),
.cycle 0 24 true (0),
.cycle 32 3 false (0),
.last 32 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 9 14 true (3),
.cycle 3 20 true (1),
.last 23 (4,false),
.cycle 0 42 true (0),
.cycle 6 17 true (2),
.cycle 34 5 false (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.cycle 32 3 false (0),
.last 32 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.last 23 (4,false),
.cycle 8 15 true (3)
])
theorem kid23_part412_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part412) = true := by rfl

def kid23_part413 : Audit := .split 18 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 0 22 true (0),
.cycle 39 1 false (1),
.cycle 0 25 true (0),
.last 19 (4,false),
.cycle 0 22 true (0),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 1 35 true (1),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.last 20 (4,false),
.cycle 35 5 false (2),
.cycle 0 58 true (-2),
.cycle 1 21 true (1),
.cycle 34 1 false (0),
.last 19 (4,false),
.cycle 18 2 true (3),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.cycle 17 2 true (4),
.cycle 0 23 true (0)
])
theorem kid23_part413_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part413) = true := by rfl

def kid23_part414 : Audit := .cycle 1 19 true (1)
theorem kid23_part414_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part414) = true := by rfl

def kid23_part415 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.last 31 (2,true),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 6 14 true (2),
.cycle 7 17 true (3),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 18 2 true (3),
.last 23 (2,true),
.cycle 27 6 false (2),
.last 29 (2,true),
.last 20 (2,true),
.cycle 35 1 false (-1),
.cycle 23 1 false (-1),
.last 25 (2,true),
.cycle 6 14 true (2),
.cycle 29 5 false (1),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 25 3 false (1),
.cycle 26 3 false (0)
])
theorem kid23_part415_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part415) = true := by rfl

def kid23_part416 : Audit := .split 19 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.last 20 (2,true),
.last 23 (2,true),
.last 22 (2,true),
.cycle 26 1 false (0),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 39 1 false (1),
.last 23 (2,true),
.last 21 (2,true),
.last 23 (2,true),
.last 24 (2,true),
.last 20 (2,true),
.last 23 (2,true),
.last 22 (2,true),
.last 25 (2,true),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 37 (2,true),
.last 21 (2,true)
])
theorem kid23_part416_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part416) = true := by rfl

def kid23_part417 : Audit := .cycle 0 18 true (0)
theorem kid23_part417_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part417) = true := by rfl

def kid23_part418 : Audit := .cycle 1 17 true (1)
theorem kid23_part418_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part418) = true := by rfl

def kid23_part419 : Audit := .cycle 2 16 true (1)
theorem kid23_part419_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part419) = true := by rfl

def kid23_part420 : Audit := .cycle 1 20 true (1)
theorem kid23_part420_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part420) = true := by rfl

def kid23_part421 : Audit := .split 18 (4,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 17 2 true (5),
.cycle 30 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 18 1 true (6),
.cycle 18 14 true (5),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 17 3 true (5),
.last 29 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (3)
])
theorem kid23_part421_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part421) = true := by rfl

def kid23_part422 : Audit := .cycle 8 10 true (3)
theorem kid23_part422_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part422) = true := by rfl

def kid23_part398 : Audit := .split 17 (4,true) (byMove [(kid23_part399),(kid23_part400),(kid23_part401),(kid23_part402),(kid23_part403),(kid23_part404),(kid23_part405),(kid23_part406),(kid23_part407),(kid23_part408),(kid23_part409),(kid23_part410),(kid23_part411),(kid23_part412),(kid23_part413),(kid23_part414),(kid23_part415),(kid23_part416),(kid23_part417),(kid23_part418),(kid23_part419),(kid23_part420),(kid23_part421),(kid23_part422)])

theorem kid23_part398_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part398) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part399),(kid23_part400),(kid23_part401),(kid23_part402),(kid23_part403),(kid23_part404),(kid23_part405),(kid23_part406),(kid23_part407),(kid23_part408),(kid23_part409),(kid23_part410),(kid23_part411),(kid23_part412),(kid23_part413),(kid23_part414),(kid23_part415),(kid23_part416),(kid23_part417),(kid23_part418),(kid23_part419),(kid23_part420),(kid23_part421),(kid23_part422)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part399_checked

  · exact kid23_part405_checked

  · exact kid23_part411_checked

  · exact kid23_part417_checked

  · exact kid23_part400_checked

  · exact kid23_part406_checked

  · exact kid23_part412_checked

  · exact kid23_part418_checked

  · exact kid23_part401_checked

  · exact kid23_part407_checked

  · exact kid23_part413_checked

  · exact kid23_part419_checked

  · exact kid23_part402_checked

  · exact kid23_part408_checked

  · exact kid23_part414_checked

  · exact kid23_part420_checked

  · exact kid23_part403_checked

  · exact kid23_part409_checked

  · exact kid23_part415_checked

  · exact kid23_part421_checked

  · exact kid23_part404_checked

  · exact kid23_part410_checked

  · exact kid23_part416_checked

  · exact kid23_part422_checked

def kid23_part423 : Audit := .cycle 44 1 false (2)
theorem kid23_part423_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part423) = true := by rfl

def kid23_part424 : Audit := .cycle 0 17 true (0)
theorem kid23_part424_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part424) = true := by rfl

def kid23_part425 : Audit := .cycle 1 16 true (1)
theorem kid23_part425_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part425) = true := by rfl

def kid23_part426 : Audit := .cycle 9 8 true (3)
theorem kid23_part426_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part426) = true := by rfl

def kid23_part427 : Audit := .cycle 3 14 true (1)
theorem kid23_part427_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part427) = true := by rfl

def kid23_part428 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 25 1 false (-1),
.cycle 38 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 31 1 false (1),
.cycle 17 29 true (4),
.cycle 6 14 true (2),
.last 26 (2,true),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 25 1 false (-1),
.last 23 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (5),
.cycle 8 12 true (3)
]),
.cycle 8 10 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 27 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 9 20 true (3),
.cycle 8 20 true (3),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 18 10 true (5),
.cycle 10 18 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 7 22 true (3),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 4 24 true (1),
.last 29 (2,true),
.last 29 (2,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 9 20 true (3),
.cycle 8 20 true (3)
]),
.cycle 10 8 true (3),
.cycle 17 1 true (7),
.split 29 (4,true) (byMove [
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 11 20 true (3),
.last 34 (2,true),
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 15 16 true (5),
.last 31 (2,true),
.cycle 1 32 true (1),
.cycle 12 18 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.last 31 (2,true),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 30 12 true (10),
.cycle 16 14 true (5)
]),
.cycle 7 12 true (3),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 16 4 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 17 3 true (6),
.last 30 (4,true),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.cycle 13 11 true (3),
.cycle 1 21 true (1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 15 6 true (5),
.cycle 8 12 true (3)
]),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 15 7 true (4),
.cycle 25 1 false (-1),
.cycle 8 24 true (1),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 67 1 false (11),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 48, 4, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 7 18 true (3),
.last 24 (2,true),
.last 20 (2,true),
.cycle 13 7 true (3),
.cycle 25 1 false (-1),
.last 23 (2,true),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 20 3 true (6),
.cycle 8 14 true (3)
]),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 22 (4,true),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (4,true),
.cycle 10 10 true (3),
.cycle 17 3 true (6),
.last 31 (4,true),
.cycle 7 14 true (3),
.cycle 15 7 true (5),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 22 (4,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 22 (4,true),
.cycle 8 12 true (3)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 17 1 true (7),
.cycle 8 10 true (3)
])
theorem kid23_part428_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part428) = true := by rfl

def kid23_part429 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 4, 64],[2, 32, 64, 1, 64, 32, 64],80⟩
theorem kid23_part429_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part429) = true := by rfl

def kid23_part430 : Audit := .cycle 6 11 true (2)
theorem kid23_part430_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part430) = true := by rfl

def kid23_part431 : Audit := .cycle 15 2 true (5)
theorem kid23_part431_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part431) = true := by rfl

def kid23_part432 : Audit := .split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 1 20 true (1),
.cycle 2 25 true (1),
.cycle 7 13 true (3),
.split 18 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 11 10 true (3),
.last 27 (4,false),
.cycle 0 25 true (0),
.last 19 (4,false),
.cycle 44 1 false (2),
.cycle 7 13 true (3),
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 38 1 false (2),
.last 19 (4,false),
.last 21 (4,false),
.last 23 (4,false),
.last 25 (4,false),
.cycle 7 15 true (3),
.last 25 (4,false),
.last 19 (4,false),
.last 21 (4,false),
.cycle 7 13 true (3),
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 19 (4,false),
.last 21 (4,false)
]),
.cycle 7 15 true (3),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 64, 4, 64],[2, 32, 4, 1, 64, 5, 64],80⟩,
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 31 (4,false),
.cycle 10 9 true (3),
.last 19 (4,false),
.cycle 1 35 true (1),
.cycle 7 13 true (3),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 19 (4,false),
.last 21 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
]),
.cycle 0 21 true (0),
.cycle 14 4 true (4),
.cycle 33 5 false (1),
.cycle 5 15 true (1),
.cycle 5 13 true (1),
.split 18 (4,true) (byMove [
.cycle 20 4 true (3),
.cycle 1 22 true (1),
.cycle 39 1 false (1),
.cycle 40 1 false (0),
.last 19 (4,false),
.cycle 1 22 true (1),
.cycle 6 13 true (2),
.last 22 (4,false),
.last 20 (4,false),
.cycle 1 20 true (1),
.last 21 (4,false),
.cycle 1 22 true (1),
.cycle 35 5 false (2),
.last 25 (4,false),
.cycle 5 15 true (1),
.cycle 34 1 false (0),
.last 19 (4,false),
.last 21 (4,false),
.cycle 6 13 true (2),
.cycle 15 4 true (4),
.cycle 17 2 true (4),
.cycle 1 20 true (1),
.last 21 (4,false),
.last 21 (4,false)
]),
.cycle 5 15 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 20 (4,false),
.cycle 0 20 true (0),
.last 21 (4,false),
.cycle 0 25 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.last 19 (4,false),
.cycle 0 34 true (0),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.cycle 17 2 true (5),
.cycle 1 20 true (1),
.last 21 (4,false),
.cycle 5 19 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
]),
.cycle 16 2 true (5)
])
theorem kid23_part432_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part432) = true := by rfl

def kid23_part433 : Audit := .cycle 1 18 true (1)
theorem kid23_part433_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part433) = true := by rfl

def kid23_part435 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 2 21 true (1),
.cycle 0 22 true (0),
.cycle 1 22 true (1),
.cycle 39 5 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (3),
.cycle 3 18 true (1),
.last 21 (4,false),
.last 36 (4,false),
.cycle 6 15 true (2),
.cycle 15 6 true (4),
.cycle 5 19 true (1),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.cycle 39 5 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (3)
])
theorem kid23_part435_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part435) = true := by rfl

def kid23_part436 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2181, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 8, 4096, 128, 2048, 4, 1, 4, 5, 4096],5136⟩,
.cycle 10 11 true (3),
.last 21 (4,false),
.last 37 (4,false),
.cycle 7 15 true (3),
.cycle 15 8 true (4),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 21 (4,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (3)
])
theorem kid23_part436_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part436) = true := by rfl

def kid23_part437 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 11 10 true (3),
.cycle 2 25 true (1),
.cycle 0 25 true (0),
.last 19 (4,false),
.cycle 44 1 false (2),
.cycle 7 13 true (3),
.cycle 1 20 true (1),
.cycle 0 21 true (0),
.cycle 38 1 false (2),
.last 19 (4,false),
.last 39 (4,false),
.cycle 7 17 true (3),
.cycle 37 1 false (-1),
.cycle 7 15 true (3),
.cycle 4 21 true (1),
.last 19 (4,false),
.cycle 18 2 true (3),
.cycle 7 13 true (3),
.cycle 1 20 true (1),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 19 (4,false),
.cycle 8 13 true (3)
])
theorem kid23_part437_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part437) = true := by rfl

def kid23_part438 : Audit := .cycle 7 13 true (3)
theorem kid23_part438_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part438) = true := by rfl

def kid23_part439 : Audit := .split 19 (4,false) (byMove [
.cycle 11 12 true (2),
.last 41 (2,true),
.last 20 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (-1),
.cycle 1 50 true (-2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 44 1 false (2),
.last 26 (2,true),
.cycle 23 1 true (5),
.cycle 0 23 true (0),
.cycle 0 25 true (0),
.last 29 (2,true),
.last 20 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (-1),
.last 25 (2,true),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 11 10 true (3),
.last 24 (2,true),
.cycle 27 1 true (1),
.cycle 0 23 true (0)
])
theorem kid23_part439_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part439) = true := by rfl

def kid23_part440 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.last 24 (2,true),
.cycle 32 1 false (0),
.last 30 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (3),
.cycle 50 1 false (2),
.cycle 18 2 true (3),
.cycle 27 6 false (2),
.last 28 (2,true),
.last 20 (2,true),
.last 24 (2,true),
.last 26 (2,true),
.last 25 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (3),
.last 28 (2,true),
.last 36 (2,true)
])
theorem kid23_part440_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part440) = true := by rfl

def kid23_part441 : Audit := .cycle 1 18 true (1)
theorem kid23_part441_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part441) = true := by rfl

def kid23_part442 : Audit := .cycle 7 11 true (3)
theorem kid23_part442_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part442) = true := by rfl

def kid23_part443 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 10 9 true (3),
.last 19 (4,false),
.last 33 (4,false),
.cycle 7 13 true (3),
.cycle 15 6 true (5),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 19 (4,false),
.cycle 18 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
])
theorem kid23_part443_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part443) = true := by rfl

def kid23_part444 : Audit := .cycle 0 19 true (0)
theorem kid23_part444_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part444) = true := by rfl

def kid23_part445 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 31 1 false (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 8, 4, 128, 256, 8, 128, 4236, 4, 4096],[128, 2048, 4096, 1, 16, 6145, 128, 2048, 4096, 1, 16, 16, 4096],5120⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 2048, 4096, 1, 16, 4096, 128, 2048, 4096, 1, 16, 16, 4096],4096⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 8, 4, 64],[2, 32, 64, 1, 16, 17, 64],64⟩,
.cycle 19 1 true (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 11 9 true (3),
.cycle 58 1 false (10),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (3)
])
theorem kid23_part445_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part445) = true := by rfl

def kid23_part446 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (3),
.last 22 (2,true),
.last 32 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 16, 4, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 18 2 true (5),
.cycle 14 6 true (4),
.last 26 (2,true),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 30 1 false (0),
.last 27 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 17 17 true (5),
.cycle 16 4 true (5)
])
theorem kid23_part446_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part446) = true := by rfl

def kid23_part447 : Audit := .cycle 14 4 true (4)
theorem kid23_part447_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part447) = true := by rfl

def kid23_part448 : Audit := .split 22 (2,true) (byMove [
.cycle 1 29 true (1),
.cycle 0 29 true (0),
.cycle 1 34 true (0),
.cycle 15 10 true (3),
.cycle 32 3 false (0),
.last 32 (4,false),
.cycle 6 17 true (2),
.cycle 7 21 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 1 24 true (1),
.last 29 (4,false),
.last 24 (4,false),
.cycle 39 9 false (2),
.cycle 34 5 false (1),
.cycle 23 12 true (1),
.cycle 13 10 true (3),
.cycle 32 3 false (0),
.last 32 (4,false),
.cycle 6 17 true (2),
.cycle 40 11 false (3),
.cycle 2 23 true (1),
.cycle 1 24 true (1),
.cycle 38 9 false (2),
.cycle 36 7 false (2)
])
theorem kid23_part448_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part448) = true := by rfl

def kid23_part449 : Audit := .split 18 (2,true) (byMove [
.cycle 1 25 true (1),
.cycle 1 22 true (1),
.cycle 39 1 false (1),
.cycle 7 19 true (2),
.last 19 (4,false),
.cycle 1 22 true (1),
.cycle 6 13 true (2),
.cycle 1 24 true (1),
.cycle 66 1 false (12),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 35 5 false (2),
.cycle 27 12 true (-2),
.cycle 5 15 true (1),
.cycle 34 1 false (0),
.last 19 (4,false),
.cycle 18 2 true (3),
.cycle 6 13 true (2),
.cycle 15 4 true (4),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 17 2 true (4),
.cycle 5 17 true (1)
])
theorem kid23_part449_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part449) = true := by rfl

def kid23_part450 : Audit := .cycle 5 13 true (1)
theorem kid23_part450_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part450) = true := by rfl

def kid23_part451 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.last 31 (2,true),
.cycle 23 1 false (-1),
.last 30 (2,true),
.cycle 14 6 true (3),
.cycle 18 4 true (3),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 18 2 true (3),
.cycle 19 2 true (3),
.cycle 27 6 false (2),
.last 29 (2,true),
.last 20 (2,true),
.cycle 35 1 false (-1),
.cycle 23 1 false (-1),
.last 25 (2,true),
.cycle 32 7 false (2),
.cycle 29 5 false (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 25 3 false (1),
.cycle 26 3 false (0)
])
theorem kid23_part451_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part451) = true := by rfl

def kid23_part452 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.last 31 (2,true),
.last 22 (2,true),
.last 30 (2,true),
.cycle 14 6 true (3),
.last 24 (2,true),
.last 20 (2,true),
.cycle 5 15 true (1),
.last 22 (2,true),
.cycle 18 2 true (3),
.cycle 27 6 false (2),
.last 24 (2,true),
.last 20 (2,true),
.cycle 35 1 false (-1),
.last 22 (2,true),
.last 25 (2,true),
.last 43 (2,true),
.last 26 (2,true),
.last 20 (2,true),
.cycle 5 15 true (1),
.last 24 (2,true),
.last 31 (2,true)
])
theorem kid23_part452_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part452) = true := by rfl

def kid23_part453 : Audit := .cycle 1 18 true (1)
theorem kid23_part453_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part453) = true := by rfl

def kid23_part454 : Audit := .cycle 7 11 true (3)
theorem kid23_part454_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part454) = true := by rfl

def kid23_part455 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 19 true (1),
.cycle 0 20 true (0),
.cycle 2 18 true (1),
.last 23 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.last 19 (4,false),
.last 32 (4,false),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.cycle 5 17 true (1),
.cycle 1 20 true (1),
.cycle 17 2 true (5),
.last 23 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
])
theorem kid23_part455_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part455) = true := by rfl

def kid23_part456 : Audit := .cycle 0 19 true (0)
theorem kid23_part456_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part456) = true := by rfl

def kid23_part457 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (6),
.cycle 16 4 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 17 14 true (5),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.cycle 17 5 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (3)
])
theorem kid23_part457_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part457) = true := by rfl

def kid23_part458 : Audit := .cycle 16 2 true (5)
theorem kid23_part458_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part458) = true := by rfl

def kid23_part434 : Audit := .split 17 (4,true) (byMove [(kid23_part435),(kid23_part436),(kid23_part437),(kid23_part438),(kid23_part439),(kid23_part440),(kid23_part441),(kid23_part442),(kid23_part443),(kid23_part444),(kid23_part445),(kid23_part446),(kid23_part447),(kid23_part448),(kid23_part449),(kid23_part450),(kid23_part451),(kid23_part452),(kid23_part453),(kid23_part454),(kid23_part455),(kid23_part456),(kid23_part457),(kid23_part458)])

theorem kid23_part434_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part434) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part435),(kid23_part436),(kid23_part437),(kid23_part438),(kid23_part439),(kid23_part440),(kid23_part441),(kid23_part442),(kid23_part443),(kid23_part444),(kid23_part445),(kid23_part446),(kid23_part447),(kid23_part448),(kid23_part449),(kid23_part450),(kid23_part451),(kid23_part452),(kid23_part453),(kid23_part454),(kid23_part455),(kid23_part456),(kid23_part457),(kid23_part458)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part435_checked

  · exact kid23_part441_checked

  · exact kid23_part447_checked

  · exact kid23_part453_checked

  · exact kid23_part436_checked

  · exact kid23_part442_checked

  · exact kid23_part448_checked

  · exact kid23_part454_checked

  · exact kid23_part437_checked

  · exact kid23_part443_checked

  · exact kid23_part449_checked

  · exact kid23_part455_checked

  · exact kid23_part438_checked

  · exact kid23_part444_checked

  · exact kid23_part450_checked

  · exact kid23_part456_checked

  · exact kid23_part439_checked

  · exact kid23_part445_checked

  · exact kid23_part451_checked

  · exact kid23_part457_checked

  · exact kid23_part440_checked

  · exact kid23_part446_checked

  · exact kid23_part452_checked

  · exact kid23_part458_checked

def kid23_part459 : Audit := .split 20 (2,true) (byMove [
.cycle 1 27 true (1),
.cycle 1 24 true (1),
.cycle 45 1 false (1),
.cycle 7 21 true (2),
.split 21 (4,false) (byMove [
.cycle 1 26 true (1),
.cycle 1 26 true (1),
.cycle 27 1 false (-1),
.last 26 (4,true),
.last 22 (4,true),
.cycle 32 1 false (0),
.cycle 15 8 true (3),
.last 24 (4,true),
.cycle 1 24 true (1),
.cycle 45 1 false (1),
.last 23 (4,true),
.cycle 110 1 false (12),
.cycle 6 26 true (2),
.last 36 (4,true),
.last 34 (4,true),
.last 26 (4,true),
.last 22 (4,true),
.cycle 27 3 false (0),
.cycle 35 9 false (3),
.last 24 (4,true),
.cycle 1 24 true (1),
.cycle 12 10 true (3),
.last 23 (4,true),
.cycle 8 20 true (3)
]),
.cycle 1 24 true (1),
.cycle 6 15 true (2),
.cycle 7 19 true (3),
.cycle 72 1 false (12),
.cycle 1 22 true (1),
.split 21 (4,true) (byMove [
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 50 1 false (2),
.last 29 (4,false),
.last 22 (4,false),
.cycle 0 25 true (0),
.cycle 1 22 true (1),
.cycle 7 15 true (3),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 25 (4,false),
.cycle 15 8 true (3),
.last 27 (4,false),
.cycle 1 24 true (1),
.cycle 45 1 false (1),
.last 22 (4,false),
.last 27 (4,false),
.cycle 1 22 true (1),
.cycle 7 15 true (3),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 8 19 true (3)
]),
.cycle 119 1 false (15),
.cycle 32 7 false (2),
.cycle 33 7 false (1),
.cycle 5 17 true (1),
.cycle 40 1 false (0),
.split 21 (4,false) (byMove [
.last 25 (4,true),
.cycle 19 4 true (2),
.cycle 27 1 false (-1),
.last 36 (4,true),
.last 22 (4,true),
.last 49 (4,true),
.cycle 14 8 true (3),
.cycle 17 6 true (3),
.cycle 20 2 true (3),
.cycle 5 17 true (1),
.last 22 (4,true),
.cycle 18 4 true (3),
.cycle 31 8 false (2),
.last 36 (4,true),
.cycle 24 10 true (-2),
.cycle 41 1 false (-1),
.last 22 (4,true),
.cycle 27 3 false (0),
.cycle 35 9 false (3),
.cycle 32 7 false (2),
.last 23 (4,true),
.cycle 5 17 true (1),
.last 22 (4,true),
.cycle 29 5 false (1)
]),
.cycle 19 2 true (3),
.cycle 6 15 true (2),
.cycle 15 6 true (3),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.split 21 (4,true) (byMove [
.last 25 (4,false),
.last 25 (4,false),
.last 23 (4,false),
.cycle 7 17 true (3),
.last 23 (4,false),
.last 25 (4,false),
.cycle 1 22 true (1),
.cycle 7 15 true (3),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 25 (4,false),
.cycle 14 8 true (3),
.cycle 17 6 true (3),
.cycle 20 2 true (4),
.cycle 5 17 true (1),
.last 23 (4,false),
.cycle 18 4 true (3),
.cycle 1 22 true (1),
.cycle 7 15 true (3),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 16 6 true (3)
]),
.cycle 17 4 true (3)
])
theorem kid23_part459_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part459) = true := by rfl

def kid23_part460 : Audit := .cycle 0 17 true (0)
theorem kid23_part460_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part460) = true := by rfl

def kid23_part461 : Audit := .cycle 1 16 true (1)
theorem kid23_part461_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part461) = true := by rfl

def kid23_part462 : Audit := .cycle 2 15 true (1)
theorem kid23_part462_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part462) = true := by rfl

def kid23_part463 : Audit := .cycle 1 19 true (1)
theorem kid23_part463_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part463) = true := by rfl

def kid23_part464 : Audit := .split 17 (4,false) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 19 true (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.last 52 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 2 18 true (1),
.last 29 (4,true),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.cycle 5 17 true (1),
.cycle 1 20 true (1),
.last 19 (4,true),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 17 2 true (6),
.cycle 8 11 true (3)
]),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 25 1 false (-1),
.cycle 64 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 33 1 false (1),
.cycle 18 11 true (5),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 25 1 false (-1),
.cycle 18 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 17 2 true (6),
.cycle 8 11 true (3)
]),
.cycle 16 2 true (6),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 9 true (3),
.cycle 3 15 true (1),
.cycle 17 1 true (7),
.split 28 (4,true) (byMove [
.cycle 1 29 true (1),
.cycle 7 22 true (3),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 97 1 false (3),
.cycle 16 13 true (6),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 9 20 true (3),
.cycle 3 26 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 18 11 true (6),
.cycle 6 23 true (2),
.cycle 15 14 true (5),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 30 4 true (6),
.cycle 27 2 true (9),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 17 12 true (6),
.cycle 8 21 true (3)
]),
.cycle 6 12 true (2),
.cycle 15 3 true (5),
.split 18 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 1 21 true (1),
.cycle 0 30 true (0),
.cycle 7 14 true (3),
.last 19 (4,true),
.cycle 5 22 true (1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 29 (4,true),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 16 3 true (6),
.cycle 14 5 true (4),
.last 21 (4,true),
.cycle 13 9 true (3),
.cycle 5 14 true (1),
.last 19 (4,true),
.last 20 (4,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 16 3 true (6)
]),
.cycle 1 19 true (1),
.split 18 (4,true) (byMove [
.last 21 (2,true),
.last 21 (2,true),
.last 19 (2,true),
.cycle 7 14 true (3),
.cycle 25 1 false (-1),
.cycle 5 22 true (1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 78 1 false (12),
.cycle 16 3 true (6),
.cycle 14 5 true (4),
.cycle 15 7 true (5),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 25 1 false (-1),
.cycle 18 2 true (5),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 17 3 true (6),
.cycle 16 3 true (6)
]),
.split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 33 (2,true),
.cycle 16 4 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.last 22 (2,true),
.cycle 18 11 true (6),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 33 (2,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 17 3 true (6),
.cycle 8 12 true (3)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 17 1 true (7),
.cycle 8 10 true (3)
])
theorem kid23_part464_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part464) = true := by rfl

def kid23_part465 : Audit := .cycle 8 9 true (3)
theorem kid23_part465_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part465) = true := by rfl

def kid23_part393 : Audit := .split 16 (5,true) (byMove [(kid23_part394),(kid23_part395),(kid23_part396),(kid23_part397),(kid23_part398),(kid23_part423),(kid23_part424),(kid23_part425),(kid23_part426),(kid23_part427),(kid23_part428),(kid23_part429),(kid23_part430),(kid23_part431),(kid23_part432),(kid23_part433),(kid23_part434),(kid23_part459),(kid23_part460),(kid23_part461),(kid23_part462),(kid23_part463),(kid23_part464),(kid23_part465)])

theorem kid23_part393_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (kid23_part393) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) 16 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid23_part394),(kid23_part395),(kid23_part396),(kid23_part397),(kid23_part398),(kid23_part423),(kid23_part424),(kid23_part425),(kid23_part426),(kid23_part427),(kid23_part428),(kid23_part429),(kid23_part430),(kid23_part431),(kid23_part432),(kid23_part433),(kid23_part434),(kid23_part459),(kid23_part460),(kid23_part461),(kid23_part462),(kid23_part463),(kid23_part464),(kid23_part465)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part394_checked

  · exact kid23_part424_checked

  · exact kid23_part430_checked

  · exact kid23_part460_checked

  · exact kid23_part395_checked

  · exact kid23_part425_checked

  · exact kid23_part431_checked

  · exact kid23_part461_checked

  · exact kid23_part396_checked

  · exact kid23_part426_checked

  · exact kid23_part432_checked

  · exact kid23_part462_checked

  · exact kid23_part397_checked

  · exact kid23_part427_checked

  · exact kid23_part433_checked

  · exact kid23_part463_checked

  · exact kid23_part398_checked

  · exact kid23_part428_checked

  · exact kid23_part434_checked

  · exact kid23_part464_checked

  · exact kid23_part423_checked

  · exact kid23_part429_checked

  · exact kid23_part459_checked

  · exact kid23_part465_checked

def kid23_part466 : Audit := .cycle 3 6 true (1)
theorem kid23_part466_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (kid23_part466) = true := by rfl

def kid23_part468 : Audit := .cycle 0 10 true (0)
theorem kid23_part468_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part468) = true := by rfl

def kid23_part469 : Audit := .cycle 1 9 true (1)
theorem kid23_part469_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part469) = true := by rfl

def kid23_part470 : Audit := .cycle 2 8 true (1)
theorem kid23_part470_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part470) = true := by rfl

def kid23_part471 : Audit := .cycle 1 12 true (1)
theorem kid23_part471_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part471) = true := by rfl

def kid23_part472 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 18 1 false (0),
.cycle 20 1 false (0),
.cycle 21 7 false (3),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 33 1 false (1)
]),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 3 17 true (0),
.cycle 18 1 false (0),
.cycle 20 1 false (0),
.cycle 21 7 false (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.cycle 22 1 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 11 9 true (2),
.cycle 28 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (2),
.cycle 3 17 true (1),
.cycle 9 11 true (2),
.cycle 9 13 true (2),
.cycle 6 14 true (2),
.cycle 18 2 true (4),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 21 (2,true),
.last 24 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 10 10 true (2),
.cycle 8 12 true (2)
]),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 24 1 false (2),
.cycle 6 6 true (2),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.last 20 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 16 (2,true),
.last 20 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.last 18 (2,true),
.last 20 (2,true),
.cycle 6 8 true (2),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 16 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 10 4 true (2),
.cycle 8 6 true (2)
]),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 22 1 false (0),
.last 22 (5,true),
.cycle 1 13 true (1),
.cycle 0 20 true (0),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 19 (5,true),
.cycle 1 17 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 13 (5,true)
]),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 20 (2,true),
.last 17 (2,true),
.cycle 14 2 true (-1),
.cycle 16 2 true (-1),
.cycle 1 13 true (1),
.cycle 17 2 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 2 true (2),
.cycle 20 2 true (-1),
.cycle 14 10 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 1 19 true (0),
.cycle 14 2 true (-1),
.cycle 13 2 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 8 6 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part472_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part472) = true := by rfl

def kid23_part473 : Audit := .cycle 8 2 true (4)
theorem kid23_part473_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part473) = true := by rfl

def kid23_part474 : Audit := .cycle 0 10 true (0)
theorem kid23_part474_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part474) = true := by rfl

def kid23_part475 : Audit := .cycle 1 9 true (1)
theorem kid23_part475_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part475) = true := by rfl

def kid23_part477 : Audit := .split 21 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (3),
.cycle 2 23 true (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 1 23 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 1 30 true (1),
.cycle 3 19 true (1),
.cycle 9 13 true (3),
.cycle 0 38 true (0),
.cycle 6 16 true (2),
.cycle 1 24 true (1),
.cycle 1 30 true (1),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 18 4 true (5),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 1 31 true (1),
.cycle 8 14 true (3)
])
theorem kid23_part477_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part477) = true := by rfl

def kid23_part478 : Audit := .split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 7 24 true (3),
.cycle 8 14 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 10 12 true (3),
.cycle 7 22 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 4, 16, 64],[2, 32, 64, 1, 16, 24, 64],64⟩,
.cycle 0 42 true (0),
.cycle 7 16 true (3),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (2,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 7 24 true (3),
.cycle 8 14 true (3)
])
theorem kid23_part478_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part478) = true := by rfl

def kid23_part479 : Audit := .split 19 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 38 true (1),
.cycle 0 25 true (0),
.last 20 (4,true),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131076, 4, 16, 8192, 16384, 8, 128, 4, 16, 128, 256, 8, 128, 4, 16, 262144],[128, 2048, 4, 1, 262144, 131076, 8192, 131072, 24, 1, 262144, 24, 128, 2048, 131076, 1, 262144, 131076, 262144],262144⟩,
.cycle 7 14 true (3),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 3 24 true (1),
.last 37 (4,true),
.last 21 (4,true),
.last 23 (4,true),
.cycle 35 5 false (1),
.cycle 5 24 true (1),
.cycle 1 25 true (1),
.last 20 (4,true),
.cycle 41 1 false (1),
.cycle 7 14 true (3),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 21 10 true (7),
.last 21 (4,true)
])
theorem kid23_part479_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part479) = true := by rfl

def kid23_part480 : Audit := .cycle 7 14 true (3)
theorem kid23_part480_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part480) = true := by rfl

def kid23_part481 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.last 23 (2,true),
.last 20 (2,true),
.last 23 (2,true),
.cycle 46 1 false (2),
.cycle 46 1 false (2),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 3 24 true (1),
.last 21 (2,true),
.cycle 1 43 true (1),
.cycle 7 18 true (3),
.last 24 (2,true),
.last 20 (2,true),
.last 23 (2,true),
.last 22 (2,true),
.cycle 7 18 true (3),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 8 14 true (3)
])
theorem kid23_part481_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part481) = true := by rfl

def kid23_part482 : Audit := .cycle 51 1 false (3)
theorem kid23_part482_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part482) = true := by rfl

def kid23_part483 : Audit := .cycle 1 19 true (1)
theorem kid23_part483_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part483) = true := by rfl

def kid23_part484 : Audit := .cycle 7 12 true (3)
theorem kid23_part484_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part484) = true := by rfl

def kid23_part485 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 21 8 true (5),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (3),
.cycle 20 8 true (5),
.last 32 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 14 true (3),
.cycle 22 8 true (6),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 19 2 true (6),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 21 8 true (7),
.cycle 8 12 true (3)
])
theorem kid23_part485_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part485) = true := by rfl

def kid23_part486 : Audit := .cycle 0 20 true (0)
theorem kid23_part486_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part486) = true := by rfl

def kid23_part487 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 20 true (3),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (3),
.cycle 9 18 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 19 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 20 true (3),
.cycle 8 12 true (3)
])
theorem kid23_part487_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part487) = true := by rfl

def kid23_part488 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 4, 16, 64],[2, 32, 64, 1, 64, 32, 64],64⟩
theorem kid23_part488_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part488) = true := by rfl

def kid23_part489 : Audit := .cycle 6 16 true (2)
theorem kid23_part489_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part489) = true := by rfl

def kid23_part490 : Audit := .cycle 17 2 true (5)
theorem kid23_part490_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part490) = true := by rfl

def kid23_part491 : Audit := .split 19 (2,true) (byMove [
.cycle 1 26 true (1),
.last 22 (4,true),
.last 28 (4,true),
.cycle 7 20 true (3),
.last 20 (4,true),
.cycle 7 24 true (3),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 4, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 1 23 true (1),
.cycle 16 4 true (4),
.cycle 35 5 false (1),
.cycle 5 24 true (1),
.cycle 5 20 true (1),
.last 20 (4,true),
.cycle 5 24 true (1),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 18 2 true (5)
])
theorem kid23_part491_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part491) = true := by rfl

def kid23_part492 : Audit := .cycle 5 14 true (1)
theorem kid23_part492_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part492) = true := by rfl

def kid23_part493 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 26 true (0),
.last 20 (2,true),
.cycle 7 20 true (3),
.cycle 46 1 false (2),
.last 22 (2,true),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.last 20 (2,true),
.cycle 1 21 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 2048, 4096, 1, 16, 4096, 128, 2048, 4096, 1, 16, 16, 4096],4096⟩,
.last 22 (2,true),
.cycle 16 4 true (4),
.last 24 (2,true),
.last 20 (2,true),
.cycle 5 20 true (1),
.last 22 (2,true),
.last 22 (2,true),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 20 11 true (6),
.cycle 18 2 true (5)
])
theorem kid23_part493_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part493) = true := by rfl

def kid23_part494 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 5 20 true (1),
.cycle 47 1 false (1),
.last 27 (2,true),
.cycle 5 20 true (1),
.last 25 (2,true),
.cycle 6 24 true (2),
.cycle 7 26 true (3),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 88 1 false (16),
.cycle 147 1 false (19),
.cycle 34 7 false (2),
.last 24 (2,true),
.cycle 5 28 true (1),
.cycle 42 1 false (0),
.last 24 (2,true),
.cycle 21 2 true (3),
.cycle 18 8 true (3),
.cycle 17 6 true (3),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 23 15 true (5),
.cycle 19 4 true (3)
])
theorem kid23_part494_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part494) = true := by rfl

def kid23_part495 : Audit := .cycle 1 19 true (1)
theorem kid23_part495_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part495) = true := by rfl

def kid23_part496 : Audit := .cycle 7 12 true (3)
theorem kid23_part496_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part496) = true := by rfl

def kid23_part497 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 2 19 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 26 true (1),
.cycle 3 17 true (1),
.cycle 9 11 true (3),
.cycle 2 32 true (1),
.cycle 6 14 true (2),
.cycle 2 20 true (1),
.cycle 2 26 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 27 true (1),
.cycle 8 12 true (3)
])
theorem kid23_part497_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part497) = true := by rfl

def kid23_part498 : Audit := .cycle 0 20 true (0)
theorem kid23_part498_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part498) = true := by rfl

def kid23_part499 : Audit := .split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 23 9 true (2),
.cycle 20 9 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 20 9 true (6),
.cycle 3 17 true (1),
.cycle 9 11 true (3),
.cycle 33 9 true (11),
.cycle 6 14 true (2),
.cycle 20 9 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 24 (2,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 20 9 true (7),
.cycle 8 12 true (3)
])
theorem kid23_part499_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part499) = true := by rfl

def kid23_part500 : Audit := .cycle 8 12 true (3)
theorem kid23_part500_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part500) = true := by rfl

def kid23_part476 : Audit := .split 18 (5,true) (byMove [(kid23_part477),(kid23_part478),(kid23_part479),(kid23_part480),(kid23_part481),(kid23_part482),(kid23_part483),(kid23_part484),(kid23_part485),(kid23_part486),(kid23_part487),(kid23_part488),(kid23_part489),(kid23_part490),(kid23_part491),(kid23_part492),(kid23_part493),(kid23_part494),(kid23_part495),(kid23_part496),(kid23_part497),(kid23_part498),(kid23_part499),(kid23_part500)])

theorem kid23_part476_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part476) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid23_part477),(kid23_part478),(kid23_part479),(kid23_part480),(kid23_part481),(kid23_part482),(kid23_part483),(kid23_part484),(kid23_part485),(kid23_part486),(kid23_part487),(kid23_part488),(kid23_part489),(kid23_part490),(kid23_part491),(kid23_part492),(kid23_part493),(kid23_part494),(kid23_part495),(kid23_part496),(kid23_part497),(kid23_part498),(kid23_part499),(kid23_part500)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part477_checked

  · exact kid23_part483_checked

  · exact kid23_part489_checked

  · exact kid23_part495_checked

  · exact kid23_part478_checked

  · exact kid23_part484_checked

  · exact kid23_part490_checked

  · exact kid23_part496_checked

  · exact kid23_part479_checked

  · exact kid23_part485_checked

  · exact kid23_part491_checked

  · exact kid23_part497_checked

  · exact kid23_part480_checked

  · exact kid23_part486_checked

  · exact kid23_part492_checked

  · exact kid23_part498_checked

  · exact kid23_part481_checked

  · exact kid23_part487_checked

  · exact kid23_part493_checked

  · exact kid23_part499_checked

  · exact kid23_part482_checked

  · exact kid23_part488_checked

  · exact kid23_part494_checked

  · exact kid23_part500_checked

def kid23_part501 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (1),
.cycle 7 10 true (3),
.split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 2 17 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 9 true (3),
.cycle 3 15 true (1),
.cycle 9 9 true (3),
.last 30 (4,true),
.cycle 6 12 true (2),
.cycle 33 5 false (1),
.cycle 1 21 true (1),
.cycle 1 19 true (1),
.last 18 (4,true),
.cycle 39 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 8 10 true (3)
]),
.cycle 0 18 true (0),
.split 17 (4,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 3 17 true (1),
.cycle 3 17 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 9 true (3),
.cycle 3 15 true (1),
.cycle 9 9 true (3),
.cycle 19 41 true (4),
.cycle 6 12 true (2),
.last 22 (2,true),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 1 21 true (1),
.cycle 39 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 8 10 true (3)
]),
.cycle 44 1 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 10 8 true (3),
.cycle 3 14 true (1),
.cycle 9 8 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 8, 16, 64],[2, 32, 64, 1, 64, 32, 64],64⟩,
.cycle 6 11 true (2),
.cycle 15 2 true (5),
.split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.last 20 (4,true),
.last 26 (4,true),
.cycle 7 13 true (3),
.last 18 (4,true),
.cycle 7 15 true (3),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 8, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 0 21 true (0),
.cycle 14 4 true (4),
.cycle 33 5 false (1),
.cycle 5 15 true (1),
.cycle 5 13 true (1),
.last 18 (4,true),
.cycle 5 15 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 16 2 true (5)
]),
.cycle 1 18 true (1),
.split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 1 20 true (1),
.last 18 (2,true),
.cycle 7 13 true (3),
.cycle 3 25 true (1),
.cycle 7 15 true (3),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 8, 16, 64],[2, 32, 64, 1, 16, 17, 64],64⟩,
.cycle 0 21 true (0),
.cycle 14 4 true (4),
.last 22 (2,true),
.last 18 (2,true),
.cycle 5 13 true (1),
.cycle 5 15 true (1),
.cycle 5 15 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 3 17 true (1),
.cycle 16 2 true (5)
]),
.split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 1 24 true (1),
.cycle 45 1 false (1),
.last 25 (2,true),
.cycle 45 1 false (1),
.cycle 1 24 true (1),
.cycle 6 15 true (2),
.cycle 7 19 true (3),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 72 1 false (12),
.cycle 119 1 false (15),
.cycle 32 7 false (2),
.last 22 (2,true),
.cycle 5 17 true (1),
.cycle 40 1 false (0),
.cycle 5 17 true (1),
.cycle 19 2 true (3),
.cycle 6 15 true (2),
.cycle 15 6 true (3),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 3 21 true (1),
.cycle 17 4 true (3)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 3 15 true (1),
.cycle 8 9 true (3)
])
theorem kid23_part501_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part501) = true := by rfl

def kid23_part502 : Audit := .cycle 9 1 true (5)
theorem kid23_part502_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part502) = true := by rfl

def kid23_part503 : Audit := .cycle 8 2 true (4)
theorem kid23_part503_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part503) = true := by rfl

def kid23_part504 : Audit := .cycle 7 4 true (3)
theorem kid23_part504_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part504) = true := by rfl

def kid23_part506 : Audit := .cycle 1 12 true (1)
theorem kid23_part506_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part506) = true := by rfl

def kid23_part507 : Audit := .cycle 7 5 true (3)
theorem kid23_part507_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part507) = true := by rfl

def kid23_part508 : Audit := .cycle 29 1 false (1)
theorem kid23_part508_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part508) = true := by rfl

def kid23_part509 : Audit := .cycle 0 13 true (0)
theorem kid23_part509_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part509) = true := by rfl

def kid23_part510 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 17 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 9 4 true (4),
.cycle 8 5 true (4),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 7 11 true (1),
.cycle 1 14 true (1),
.last 17 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 8 5 true (4)
])
theorem kid23_part510_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part510) = true := by rfl

def kid23_part511 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 20 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 8 true (3),
.cycle 3 10 true (1),
.cycle 9 4 true (4),
.cycle 8 5 true (4),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 7 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.cycle 8 5 true (4)
])
theorem kid23_part511_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part511) = true := by rfl

def kid23_part512 : Audit := .cycle 0 12 true (0)
theorem kid23_part512_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part512) = true := by rfl

def kid23_part513 : Audit := .cycle 1 11 true (1)
theorem kid23_part513_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part513) = true := by rfl

def kid23_part514 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 11 9 true (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 8 14 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (4),
.cycle 3 17 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4),
.cycle 6 14 true (2),
.cycle 18 2 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 5, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 1 21 true (1),
.last 20 (4,true),
.last 23 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (6),
.cycle 8 12 true (4)
])
theorem kid23_part514_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part514) = true := by rfl

def kid23_part515 : Audit := .cycle 3 9 true (1)
theorem kid23_part515_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part515) = true := by rfl

def kid23_part516 : Audit := .cycle 9 3 true (4)
theorem kid23_part516_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part516) = true := by rfl

def kid23_part517 : Audit := .cycle 8 4 true (4)
theorem kid23_part517_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part517) = true := by rfl

def kid23_part518 : Audit := .cycle 6 6 true (2)
theorem kid23_part518_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part518) = true := by rfl

def kid23_part519 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 25 5 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 23 7 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 25 5 false (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 18 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 3 true (4),
.cycle 8 6 true (4)
])
theorem kid23_part519_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part519) = true := by rfl

def kid23_part520 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (1),
.cycle 1 24 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 1 29 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 16 8 true (2),
.cycle 3 17 true (1),
.cycle 9 11 true (1),
.cycle 1 27 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 16, 64],[2, 32, 35, 1, 64, 32, 64],64⟩,
.cycle 18 2 true (4),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.last 23 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 16, 64],[2, 32, 35, 1, 64, 32, 64],64⟩
])
theorem kid23_part520_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part520) = true := by rfl

def kid23_part521 : Audit := .cycle 1 13 true (1)
theorem kid23_part521_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part521) = true := by rfl

def kid23_part522 : Audit := .split 12 (4,true) (byMove [
.cycle 10 4 true (3),
.cycle 1 15 true (1),
.last 21 (5,true),
.cycle 7 8 true (3),
.last 17 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 9 5 true (4),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.last 17 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid23_part522_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part522) = true := by rfl

def kid23_part523 : Audit := .split 12 (5,true) (byMove [
.cycle 10 4 true (3),
.last 15 (4,true),
.cycle 25 1 false (1),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 20 5 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (4),
.cycle 6 10 true (2),
.cycle 12 2 true (3),
.cycle 5 18 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (4)
])
theorem kid23_part523_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part523) = true := by rfl

def kid23_part524 : Audit := .cycle 0 12 true (0)
theorem kid23_part524_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part524) = true := by rfl

def kid23_part525 : Audit := .cycle 1 11 true (1)
theorem kid23_part525_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part525) = true := by rfl

def kid23_part526 : Audit := .cycle 2 10 true (1)
theorem kid23_part526_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part526) = true := by rfl

def kid23_part527 : Audit := .cycle 1 14 true (1)
theorem kid23_part527_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part527) = true := by rfl

def kid23_part528 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 11 4 true (5),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 26 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (5),
.cycle 3 12 true (1),
.cycle 9 6 true (4),
.cycle 8 7 true (4),
.cycle 6 9 true (2),
.cycle 13 2 true (5),
.last 16 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 20 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (5),
.cycle 8 7 true (4)
])
theorem kid23_part528_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part528) = true := by rfl

def kid23_part529 : Audit := .cycle 8 4 true (4)
theorem kid23_part529_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part529) = true := by rfl

def kid23_part505 : Audit := .split 11 (2,true) (byMove [(kid23_part506),(kid23_part507),(kid23_part508),(kid23_part509),(kid23_part510),(kid23_part511),(kid23_part512),(kid23_part513),(kid23_part514),(kid23_part515),(kid23_part516),(kid23_part517),(kid23_part518),(kid23_part519),(kid23_part520),(kid23_part521),(kid23_part522),(kid23_part523),(kid23_part524),(kid23_part525),(kid23_part526),(kid23_part527),(kid23_part528),(kid23_part529)])

theorem kid23_part505_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part505) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid23_part506),(kid23_part507),(kid23_part508),(kid23_part509),(kid23_part510),(kid23_part511),(kid23_part512),(kid23_part513),(kid23_part514),(kid23_part515),(kid23_part516),(kid23_part517),(kid23_part518),(kid23_part519),(kid23_part520),(kid23_part521),(kid23_part522),(kid23_part523),(kid23_part524),(kid23_part525),(kid23_part526),(kid23_part527),(kid23_part528),(kid23_part529)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part506_checked

  · exact kid23_part512_checked

  · exact kid23_part518_checked

  · exact kid23_part524_checked

  · exact kid23_part507_checked

  · exact kid23_part513_checked

  · exact kid23_part519_checked

  · exact kid23_part525_checked

  · exact kid23_part508_checked

  · exact kid23_part514_checked

  · exact kid23_part520_checked

  · exact kid23_part526_checked

  · exact kid23_part509_checked

  · exact kid23_part515_checked

  · exact kid23_part521_checked

  · exact kid23_part527_checked

  · exact kid23_part510_checked

  · exact kid23_part516_checked

  · exact kid23_part522_checked

  · exact kid23_part528_checked

  · exact kid23_part511_checked

  · exact kid23_part517_checked

  · exact kid23_part523_checked

  · exact kid23_part529_checked

def kid23_part530 : Audit := .cycle 0 12 true (0)
theorem kid23_part530_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part530) = true := by rfl

def kid23_part531 : Audit := .cycle 4 6 true (1)
theorem kid23_part531_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part531) = true := by rfl

def kid23_part533 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 33 1 false (1),
.cycle 7 10 true (2),
.cycle 0 20 true (0),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 13 8 true (3),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 21 (5,true),
.cycle 5 10 true (1),
.cycle 11 4 true (2),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 15 (5,true)
])
theorem kid23_part533_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part533) = true := by rfl

def kid23_part534 : Audit := .cycle 0 18 true (0)
theorem kid23_part534_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part534) = true := by rfl

def kid23_part535 : Audit := .split 12 (2,true) (byMove [
.cycle 1 17 true (1),
.last 20 (5,true),
.last 27 (5,true),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.cycle 18 1 false (0),
.last 15 (5,true),
.last 26 (5,true),
.cycle 1 15 true (1),
.last 19 (5,true),
.cycle 18 1 false (0),
.last 23 (5,true),
.last 23 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.last 25 (5,true),
.cycle 16 1 false (0),
.last 29 (5,true),
.last 15 (5,true),
.cycle 7 8 true (2),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 21 (5,true),
.last 21 (5,true)
])
theorem kid23_part535_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part535) = true := by rfl

def kid23_part536 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 14 8 true (4),
.cycle 3 13 true (1),
.cycle 9 7 true (2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 8519680, 1077952512, 16, 8192, 16384, 8, 128, 1077952512, 16, 33554432, 67108864, 2097152, 128, 131072, 4194304, 33554432, 67108864, 2097152, 8519680, 8388608, 4194304, 33554432, 67108864, 134217728, 570425344, 1992441856, 268435456, 1073741824],[128, 2048, 1073741824, 1, 4210688, 32, 8192, 131072, 1073741824, 1, 128, 32, 33554432, 536870912, 1073741824, 262144, 128, 8388608, 33554432, 536870912, 1073741824, 262144, 4210688, 8388608, 33554432, 536870912, 1073741824, 16777216, 369098752, 536870912, 1073741824],2131508336⟩,
.cycle 6 10 true (2),
.cycle 14 2 true (4),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 7 12 true (2),
.last 31 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 7 13 true (2),
.cycle 8 8 true (2)
])
theorem kid23_part536_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part536) = true := by rfl

def kid23_part537 : Audit := .cycle 15 1 false (-1)
theorem kid23_part537_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part537) = true := by rfl

def kid23_part538 : Audit := .split 12 (5,true) (byMove [
.cycle 1 17 true (1),
.cycle 8 16 true (1),
.cycle 27 1 false (1),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 1 21 true (0),
.cycle 18 1 false (0),
.cycle 22 1 false (0),
.cycle 23 9 false (3),
.last 14 (2,true),
.last 18 (2,true),
.cycle 24 1 false (0),
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 20 1 false (0),
.cycle 24 1 false (0)
])
theorem kid23_part538_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part538) = true := by rfl

def kid23_part539 : Audit := .cycle 6 6 true (2)
theorem kid23_part539_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part539) = true := by rfl

def kid23_part540 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 31 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.cycle 9 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 7 10 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part540_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part540) = true := by rfl

def kid23_part541 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (5,true),
.cycle 0 14 true (0),
.last 23 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.cycle 20 1 false (0),
.last 27 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 13 (5,true)
])
theorem kid23_part541_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part541) = true := by rfl

def kid23_part542 : Audit := .cycle 1 13 true (1)
theorem kid23_part542_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part542) = true := by rfl

def kid23_part543 : Audit := .cycle 38 1 false (8)
theorem kid23_part543_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part543) = true := by rfl

def kid23_part544 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 20 (2,true),
.last 17 (2,true),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 44 1 false (10),
.cycle 47 1 false (11),
.cycle 6 10 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 1 19 true (1),
.cycle 20 1 false (0),
.cycle 79 1 false (11),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 20 3 true (6),
.cycle 8 6 true (3)
])
theorem kid23_part544_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part544) = true := by rfl

def kid23_part545 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 7 12 true (2),
.last 15 (2,true),
.cycle 7 10 true (2),
.cycle 7 14 true (2),
.cycle 27 1 false (-1),
.cycle 1 15 true (1),
.cycle 13 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 10 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 6 12 true (2),
.cycle 13 2 true (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 11 4 true (2),
.cycle 22 7 false (2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 10 true (2),
.cycle 8 8 true (2)
])
theorem kid23_part545_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part545) = true := by rfl

def kid23_part546 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.last 18 (2,true),
.last 14 (2,true),
.cycle 0 19 true (0),
.last 16 (2,true),
.last 20 (2,true),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 16 (2,true),
.last 24 (2,true),
.cycle 6 14 true (2),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 1 19 true (1),
.last 16 (2,true),
.last 18 (2,true),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 7 true (3),
.cycle 8 8 true (2)
])
theorem kid23_part546_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part546) = true := by rfl

def kid23_part547 : Audit := .split 12 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 5 10 true (1),
.last 19 (5,true),
.last 21 (5,true),
.cycle 22 1 false (0),
.last 21 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 27 (5,true),
.cycle 5 8 true (1),
.cycle 5 10 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 2 14 true (1),
.cycle 5 8 true (1),
.cycle 11 2 true (2),
.last 13 (5,true)
])
theorem kid23_part547_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part547) = true := by rfl

def kid23_part548 : Audit := .split 15 (5,true) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 1 18 true (1),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 12 8 true (2),
.cycle 3 13 true (1),
.cycle 9 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 34, 32, 64],64⟩,
.cycle 6 10 true (2),
.cycle 14 2 true (4),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 5 12 true (1),
.cycle 30 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 5 13 true (1),
.cycle 8 8 true (2)
])
theorem kid23_part548_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part548) = true := by rfl

def kid23_part549 : Audit := .cycle 15 1 false (-1)
theorem kid23_part549_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part549) = true := by rfl

def kid23_part550 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 5 10 true (1),
.last 20 (2,true),
.last 17 (2,true),
.cycle 14 2 true (-1),
.cycle 16 2 true (-1),
.cycle 0 16 true (0),
.cycle 19 2 true (4),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 13 2 true (2),
.cycle 24 2 true (-1),
.cycle 14 16 true (2),
.last 14 (2,true),
.last 18 (2,true),
.cycle 1 23 true (0),
.cycle 14 2 true (-1),
.cycle 13 2 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 11 2 true (2),
.cycle 8 8 true (2)
])
theorem kid23_part550_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part550) = true := by rfl

def kid23_part551 : Audit := .cycle 6 6 true (2)
theorem kid23_part551_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part551) = true := by rfl

def kid23_part552 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 26 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.cycle 9 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 14 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part552_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part552) = true := by rfl

def kid23_part553 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 2 14 true (1),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (5,true),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 13 (5,true)
])
theorem kid23_part553_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part553) = true := by rfl

def kid23_part554 : Audit := .cycle 1 13 true (1)
theorem kid23_part554_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part554) = true := by rfl

def kid23_part555 : Audit := .cycle 12 3 true (4)
theorem kid23_part555_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part555) = true := by rfl

def kid23_part556 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 8 8 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 8 8 true (3),
.cycle 22 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 6 10 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 11 2 true (3),
.cycle 13 4 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part556_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part556) = true := by rfl

def kid23_part532 : Audit := .split 11 (4,true) (byMove [(kid23_part533),(kid23_part534),(kid23_part535),(kid23_part536),(kid23_part537),(kid23_part538),(kid23_part539),(kid23_part540),(kid23_part541),(kid23_part542),(kid23_part543),(kid23_part544),(kid23_part545),(kid23_part546),(kid23_part547),(kid23_part548),(kid23_part549),(kid23_part550),(kid23_part551),(kid23_part552),(kid23_part553),(kid23_part554),(kid23_part555),(kid23_part556)])

theorem kid23_part532_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part532) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part533),(kid23_part534),(kid23_part535),(kid23_part536),(kid23_part537),(kid23_part538),(kid23_part539),(kid23_part540),(kid23_part541),(kid23_part542),(kid23_part543),(kid23_part544),(kid23_part545),(kid23_part546),(kid23_part547),(kid23_part548),(kid23_part549),(kid23_part550),(kid23_part551),(kid23_part552),(kid23_part553),(kid23_part554),(kid23_part555),(kid23_part556)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part533_checked

  · exact kid23_part539_checked

  · exact kid23_part545_checked

  · exact kid23_part551_checked

  · exact kid23_part534_checked

  · exact kid23_part540_checked

  · exact kid23_part546_checked

  · exact kid23_part552_checked

  · exact kid23_part535_checked

  · exact kid23_part541_checked

  · exact kid23_part547_checked

  · exact kid23_part553_checked

  · exact kid23_part536_checked

  · exact kid23_part542_checked

  · exact kid23_part548_checked

  · exact kid23_part554_checked

  · exact kid23_part537_checked

  · exact kid23_part543_checked

  · exact kid23_part549_checked

  · exact kid23_part555_checked

  · exact kid23_part538_checked

  · exact kid23_part544_checked

  · exact kid23_part550_checked

  · exact kid23_part556_checked

def kid23_part557 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 22 true (0),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 17 3 false (-1),
.cycle 22 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 23 3 false (1),
.cycle 45 3 false (3),
.cycle 6 11 true (2),
.cycle 13 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 17 3 false (-1),
.cycle 19 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 3 false (0),
.cycle 8 7 true (3)
]),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 10 12 true (3),
.last 21 (2,true),
.cycle 7 16 true (3),
.cycle 0 24 true (0),
.cycle 59 1 false (3),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 11 10 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 36, 16, 64],[2, 32, 64, 1, 4, 32, 64],64⟩,
.cycle 6 18 true (2),
.cycle 19 2 true (5),
.last 21 (2,true),
.cycle 5 16 true (1),
.last 22 (2,true),
.last 25 (2,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 11 true (6),
.cycle 8 14 true (3)
]),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 3 17 true (1),
.cycle 52 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 12 8 true (3),
.cycle 3 16 true (1),
.cycle 9 10 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 40, 16, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 0 21 true (0),
.cycle 1 24 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 19 true (1),
.cycle 8 11 true (3)
]),
.cycle 9 3 true (4),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 21 (5,true),
.cycle 1 15 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 8 6 true (4)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 5 16 true (1),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 17 3 false (-1),
.cycle 22 3 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 23 3 false (1),
.cycle 73 3 false (11),
.cycle 6 14 true (2),
.cycle 13 2 true (2),
.last 14 (2,true),
.cycle 1 19 true (1),
.cycle 17 3 false (-1),
.cycle 19 3 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 3 false (0),
.cycle 8 8 true (3)
]),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.last 21 (2,true),
.last 18 (2,true),
.cycle 19 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (5),
.cycle 8 7 true (4),
.cycle 6 11 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 1 20 true (1),
.cycle 18 5 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (5),
.cycle 8 7 true (4)
]),
.cycle 8 4 true (4)
])
theorem kid23_part557_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part557) = true := by rfl

def kid23_part558 : Audit := .cycle 0 10 true (0)
theorem kid23_part558_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part558) = true := by rfl

def kid23_part559 : Audit := .cycle 1 9 true (1)
theorem kid23_part559_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part559) = true := by rfl

def kid23_part560 : Audit := .cycle 2 8 true (1)
theorem kid23_part560_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part560) = true := by rfl

def kid23_part561 : Audit := .cycle 1 12 true (1)
theorem kid23_part561_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part561) = true := by rfl

def kid23_part562 : Audit := .cycle 9 1 true (5)
theorem kid23_part562_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part562) = true := by rfl

def kid23_part563 : Audit := .cycle 8 2 true (4)
theorem kid23_part563_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part563) = true := by rfl

def kid23_part467 : Audit := .split 9 (4,false) (byMove [(kid23_part468),(kid23_part469),(kid23_part470),(kid23_part471),(kid23_part472),(kid23_part473),(kid23_part474),(kid23_part475),(kid23_part476),(kid23_part501),(kid23_part502),(kid23_part503),(kid23_part504),(kid23_part505),(kid23_part530),(kid23_part531),(kid23_part532),(kid23_part557),(kid23_part558),(kid23_part559),(kid23_part560),(kid23_part561),(kid23_part562),(kid23_part563)])

theorem kid23_part467_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (kid23_part467) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid23_part468),(kid23_part469),(kid23_part470),(kid23_part471),(kid23_part472),(kid23_part473),(kid23_part474),(kid23_part475),(kid23_part476),(kid23_part501),(kid23_part502),(kid23_part503),(kid23_part504),(kid23_part505),(kid23_part530),(kid23_part531),(kid23_part532),(kid23_part557),(kid23_part558),(kid23_part559),(kid23_part560),(kid23_part561),(kid23_part562),(kid23_part563)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part468_checked

  · exact kid23_part474_checked

  · exact kid23_part504_checked

  · exact kid23_part558_checked

  · exact kid23_part469_checked

  · exact kid23_part475_checked

  · exact kid23_part505_checked

  · exact kid23_part559_checked

  · exact kid23_part470_checked

  · exact kid23_part476_checked

  · exact kid23_part530_checked

  · exact kid23_part560_checked

  · exact kid23_part471_checked

  · exact kid23_part501_checked

  · exact kid23_part531_checked

  · exact kid23_part561_checked

  · exact kid23_part472_checked

  · exact kid23_part502_checked

  · exact kid23_part532_checked

  · exact kid23_part562_checked

  · exact kid23_part473_checked

  · exact kid23_part503_checked

  · exact kid23_part557_checked

  · exact kid23_part563_checked

def kid23_part564 : Audit := .cycle 8 1 true (4)
theorem kid23_part564_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨false,true,5⟩)) (kid23_part564) = true := by rfl

def kid23_part565 : Audit := .cycle 6 3 true (2)
theorem kid23_part565_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (kid23_part565) = true := by rfl

def kid23_part567 : Audit := .cycle 1 11 true (1)
theorem kid23_part567_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part567) = true := by rfl

def kid23_part568 : Audit := .cycle 7 4 true (3)
theorem kid23_part568_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part568) = true := by rfl

def kid23_part569 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 13 (4,false),
.cycle 11 4 true (2),
.cycle 21 7 false (2),
.last 19 (4,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 17 (4,false)
]),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 9 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 25 9 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 40 (4,true),
.cycle 9 9 true (2),
.cycle 12 1 true (4),
.cycle 11 4 true (3),
.cycle 7 7 true (3),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 21 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3)
]),
.cycle 11 3 true (3),
.cycle 6 6 true (2),
.cycle 19 5 false (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 14 4 true (1),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.last 17 (4,false),
.cycle 1 13 true (1),
.last 18 (4,false),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 26 1 false (2),
.cycle 19 5 false (2),
.last 19 (4,false),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 15 (4,false)
]),
.cycle 23 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 4 true (3),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3)
]),
.cycle 8 4 true (3)
])
theorem kid23_part569_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part569) = true := by rfl

def kid23_part570 : Audit := .cycle 0 12 true (0)
theorem kid23_part570_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part570) = true := by rfl

def kid23_part572 : Audit := .cycle 1 12 true (1)
theorem kid23_part572_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part572) = true := by rfl

def kid23_part573 : Audit := .cycle 1 16 true (1)
theorem kid23_part573_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part573) = true := by rfl

def kid23_part574 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 13 (4,false),
.cycle 12 3 true (2),
.cycle 21 7 false (2),
.cycle 25 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 33 1 false (1)
])
theorem kid23_part574_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part574) = true := by rfl

def kid23_part575 : Audit := .cycle 0 13 true (0)
theorem kid23_part575_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part575) = true := by rfl

def kid23_part576 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 18 13 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.last 16 (2,true),
.cycle 15 8 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 18 5 false (0)
])
theorem kid23_part576_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part576) = true := by rfl

def kid23_part577 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.last 21 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.last 16 (2,true),
.cycle 15 8 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.last 26 (2,true)
])
theorem kid23_part577_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part577) = true := by rfl

def kid23_part578 : Audit := .cycle 0 12 true (0)
theorem kid23_part578_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part578) = true := by rfl

def kid23_part579 : Audit := .cycle 1 11 true (1)
theorem kid23_part579_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part579) = true := by rfl

def kid23_part580 : Audit := .cycle 9 9 true (2)
theorem kid23_part580_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part580) = true := by rfl

def kid23_part581 : Audit := .cycle 3 9 true (1)
theorem kid23_part581_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part581) = true := by rfl

def kid23_part582 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.last 20 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 9 9 true (2),
.cycle 12 1 true (4),
.last 15 (2,true),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 28 1 false (6),
.last 20 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3)
])
theorem kid23_part582_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part582) = true := by rfl

def kid23_part583 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (3),
.last 21 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 12 3 true (3),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 17 (4,false),
.last 21 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (3)
])
theorem kid23_part583_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part583) = true := by rfl

def kid23_part584 : Audit := .cycle 6 6 true (2)
theorem kid23_part584_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part584) = true := by rfl

def kid23_part585 : Audit := .split 16 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 22 7 false (1),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 20 3 false (0),
.last 22 (4,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 14 true (1),
.cycle 3 14 true (1),
.last 17 (4,false),
.cycle 15 3 true (1),
.cycle 23 11 false (2),
.cycle 20 5 false (1),
.cycle 1 35 true (-1),
.cycle 1 18 true (1),
.cycle 20 3 false (0),
.last 22 (4,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.last 17 (4,false),
.cycle 21 9 false (2)
])
theorem kid23_part585_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part585) = true := by rfl

def kid23_part586 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 0 26 true (-1),
.cycle 1 13 true (1),
.cycle 0 20 true (0),
.cycle 1 29 true (0),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.last 14 (4,false),
.cycle 19 5 false (2),
.cycle 15 14 true (-2),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.last 13 (4,false),
.last 28 (4,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 0 17 true (0)
])
theorem kid23_part586_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part586) = true := by rfl

def kid23_part587 : Audit := .cycle 1 13 true (1)
theorem kid23_part587_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part587) = true := by rfl

def kid23_part588 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 1 32 true (-2),
.last 14 (2,true),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 6 8 true (1),
.cycle 14 6 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (1),
.last 18 (2,true),
.cycle 15 6 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 20 7 false (2),
.cycle 17 5 false (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 15 3 false (1),
.cycle 16 3 false (0)
])
theorem kid23_part588_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part588) = true := by rfl

def kid23_part589 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (0),
.last 21 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.last 17 (2,true),
.last 18 (2,true),
.cycle 7 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.last 18 (2,true),
.last 16 (2,true),
.cycle 15 8 false (2),
.last 19 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.last 17 (2,true),
.last 18 (2,true),
.last 34 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 26 (2,true),
.last 26 (2,true)
])
theorem kid23_part589_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part589) = true := by rfl

def kid23_part590 : Audit := .cycle 0 12 true (0)
theorem kid23_part590_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part590) = true := by rfl

def kid23_part591 : Audit := .cycle 1 11 true (1)
theorem kid23_part591_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part591) = true := by rfl

def kid23_part592 : Audit := .cycle 2 10 true (1)
theorem kid23_part592_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part592) = true := by rfl

def kid23_part593 : Audit := .cycle 1 14 true (1)
theorem kid23_part593_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part593) = true := by rfl

def kid23_part594 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 22 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 15 (2,true),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.last 22 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3)
])
theorem kid23_part594_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part594) = true := by rfl

def kid23_part595 : Audit := .cycle 8 4 true (3)
theorem kid23_part595_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part595) = true := by rfl

def kid23_part571 : Audit := .split 11 (4,true) (byMove [(kid23_part572),(kid23_part573),(kid23_part574),(kid23_part575),(kid23_part576),(kid23_part577),(kid23_part578),(kid23_part579),(kid23_part580),(kid23_part581),(kid23_part582),(kid23_part583),(kid23_part584),(kid23_part585),(kid23_part586),(kid23_part587),(kid23_part588),(kid23_part589),(kid23_part590),(kid23_part591),(kid23_part592),(kid23_part593),(kid23_part594),(kid23_part595)])

theorem kid23_part571_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part571) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part572),(kid23_part573),(kid23_part574),(kid23_part575),(kid23_part576),(kid23_part577),(kid23_part578),(kid23_part579),(kid23_part580),(kid23_part581),(kid23_part582),(kid23_part583),(kid23_part584),(kid23_part585),(kid23_part586),(kid23_part587),(kid23_part588),(kid23_part589),(kid23_part590),(kid23_part591),(kid23_part592),(kid23_part593),(kid23_part594),(kid23_part595)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part572_checked

  · exact kid23_part578_checked

  · exact kid23_part584_checked

  · exact kid23_part590_checked

  · exact kid23_part573_checked

  · exact kid23_part579_checked

  · exact kid23_part585_checked

  · exact kid23_part591_checked

  · exact kid23_part574_checked

  · exact kid23_part580_checked

  · exact kid23_part586_checked

  · exact kid23_part592_checked

  · exact kid23_part575_checked

  · exact kid23_part581_checked

  · exact kid23_part587_checked

  · exact kid23_part593_checked

  · exact kid23_part576_checked

  · exact kid23_part582_checked

  · exact kid23_part588_checked

  · exact kid23_part594_checked

  · exact kid23_part577_checked

  · exact kid23_part583_checked

  · exact kid23_part589_checked

  · exact kid23_part595_checked

def kid23_part596 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 false (4),
.cycle 13 8 false (1),
.cycle 22 1 false (-2),
.cycle 0 21 false (4),
.split 20 (4,true) (byMove [
.cycle 0 21 false (4),
.cycle 15 16 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 0 21 false (4),
.cycle 15 16 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 17 4 true (-2),
.cycle 15 11 false (1),
.cycle 18 3 false (-1),
.cycle 0 23 false (4),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 15 22 false (3),
.cycle 1 20 false (4),
.cycle 15 15 false (1),
.cycle 1 23 false (4),
.last 21 (4,false),
.cycle 13 8 false (1)
]),
.cycle 16 4 false (0),
.cycle 11 24 false (4),
.cycle 15 15 true (-2),
.cycle 15 13 false (1),
.cycle 15 13 false (1),
.split 20 (4,false) (byMove [
.cycle 15 22 false (3),
.cycle 1 20 false (4),
.cycle 15 15 false (1),
.cycle 1 23 false (4),
.last 22 (4,true),
.cycle 13 8 false (1),
.cycle 0 21 true (-2),
.cycle 15 16 true (-2),
.cycle 15 15 false (2),
.cycle 15 13 false (1),
.cycle 20 1 true (0),
.cycle 17 4 true (-2),
.cycle 15 12 false (1),
.cycle 18 3 true (-2),
.cycle 0 23 true (-2),
.cycle 15 13 false (1),
.last 22 (4,true),
.cycle 13 8 false (1),
.cycle 8 26 false (5),
.cycle 11 24 false (4),
.cycle 15 15 true (-2),
.cycle 1 23 true (-2),
.cycle 20 1 true (0),
.cycle 11 12 false (3)
]),
.cycle 17 3 true (-2),
.cycle 15 10 false (1),
.cycle 14 6 false (1),
.cycle 1 23 false (4),
.cycle 1 21 false (4),
.split 20 (4,true) (byMove [
.cycle 22 4 true (-3),
.cycle 37 25 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 1 21 false (4),
.cycle 13 9 false (1),
.last 22 (4,false),
.cycle 0 22 true (-2),
.last 22 (4,false),
.cycle 16 5 false (0),
.cycle 15 9 false (1),
.cycle 18 3 false (-1),
.cycle 1 23 false (4),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 15 22 false (3),
.cycle 15 10 false (1),
.cycle 19 2 true (-2),
.cycle 11 26 false (4),
.last 22 (4,false),
.cycle 15 6 false (1)
]),
.cycle 16 4 false (0),
.cycle 15 22 false (4),
.cycle 15 20 false (3),
.cycle 2 18 false (4),
.cycle 11 26 false (4),
.split 20 (4,false) (byMove [
.cycle 15 22 false (3),
.cycle 15 10 false (1),
.cycle 19 2 true (-1),
.cycle 11 26 false (4),
.last 21 (4,true),
.cycle 15 6 false (1),
.cycle 15 26 false (5),
.cycle 15 16 true (-2),
.cycle 9 18 false (4),
.cycle 3 18 false (4),
.cycle 20 1 true (0),
.cycle 17 4 true (-2),
.cycle 15 12 false (1),
.cycle 15 8 false (1),
.last 22 (4,true),
.cycle 11 26 false (4),
.last 21 (4,true),
.cycle 15 6 false (1),
.cycle 15 24 false (5),
.cycle 15 22 false (4),
.cycle 15 20 false (3),
.cycle 15 28 false (5),
.cycle 20 1 true (0),
.cycle 15 10 false (1)
]),
.cycle 15 8 false (1)
])
theorem kid23_part596_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part596) = true := by rfl

def kid23_part597 : Audit := .cycle 0 11 true (0)
theorem kid23_part597_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part597) = true := by rfl

def kid23_part598 : Audit := .cycle 1 10 true (1)
theorem kid23_part598_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part598) = true := by rfl

def kid23_part599 : Audit := .cycle 9 8 true (3)
theorem kid23_part599_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part599) = true := by rfl

def kid23_part600 : Audit := .cycle 3 8 true (1)
theorem kid23_part600_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part600) = true := by rfl

def kid23_part601 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 21 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (2),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.last 16 (2,true),
.cycle 6 8 true (2),
.last 20 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 17 1 false (-1),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (3),
.cycle 8 6 true (3)
]),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 9 20 true (3),
.cycle 8 14 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (3),
.cycle 9 18 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 4096, 128, 256, 8, 128, 4, 16, 4096],[128, 2048, 4096, 1, 16, 16, 128, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.last 24 (2,true),
.cycle 7 16 true (3),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (2,true),
.cycle 19 4 true (5),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 9 20 true (3),
.cycle 8 14 true (3)
]),
.cycle 9 8 true (3),
.cycle 11 1 true (5),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 10 5 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3)
]),
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.cycle 11 3 true (4),
.cycle 12 3 true (4),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.cycle 9 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 6 true (3),
.cycle 8 6 true (3)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 22 true (0),
.last 14 (2,true),
.cycle 9 7 true (2),
.cycle 17 1 false (-1),
.last 21 (2,true),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 40 1 false (8),
.last 18 (2,true),
.cycle 7 12 true (2),
.last 18 (2,true),
.last 14 (2,true),
.cycle 9 7 true (2),
.cycle 17 1 false (-1),
.last 18 (2,true),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.cycle 8 8 true (3)
]),
.split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.last 33 (2,true),
.cycle 8 8 true (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 10 true (3),
.cycle 9 12 true (3),
.last 19 (2,true),
.last 18 (2,true),
.cycle 7 10 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 33 (2,true),
.cycle 12 4 true (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 14 3 true (4),
.cycle 8 8 true (3)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part601_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part601) = true := by rfl

def kid23_part602 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 33 4 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 11 4 true (4),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.cycle 7 13 true (1),
.cycle 1 16 true (1),
.last 17 (4,false),
.cycle 15 8 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (3)
]),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 8 7 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 14 true (4),
.cycle 9 11 true (3),
.cycle 14 1 true (6),
.cycle 11 4 true (4),
.cycle 7 9 true (3),
.cycle 12 3 true (4),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (4,true),
.cycle 10 8 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (6),
.cycle 8 7 true (3)
]),
.cycle 11 3 true (4),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.cycle 9 11 true (1),
.cycle 1 15 true (1),
.split 14 (4,true) (byMove [
.cycle 12 4 true (3),
.cycle 0 27 true (0),
.cycle 31 1 false (1),
.cycle 7 10 true (3),
.last 17 (4,false),
.cycle 33 4 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 16 (4,false),
.cycle 0 16 true (0),
.last 16 (4,false),
.cycle 10 5 true (4),
.cycle 9 7 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2080, 4096, 32, 128, 256, 8, 128, 4096, 32, 4096],[128, 2048, 4096, 1, 32, 32, 128, 2048, 32, 1, 32, 32, 4096],5136⟩,
.cycle 9 11 true (1),
.cycle 5 10 true (1),
.last 17 (4,false),
.cycle 77 4 false (9),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 13 2 true (4),
.cycle 0 16 true (0),
.last 16 (4,false),
.cycle 10 5 true (4)
]),
.cycle 10 5 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.split 14 (4,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 13 2 true (5),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 10 5 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 14 1 true (6),
.cycle 11 4 true (4),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.last 16 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 10 6 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (6),
.cycle 8 7 true (3)
]),
.cycle 8 6 true (3)
])
theorem kid23_part602_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part602) = true := by rfl

def kid23_part603 : Audit := .cycle 6 5 true (2)
theorem kid23_part603_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part603) = true := by rfl

def kid23_part604 : Audit := .cycle 9 2 true (3)
theorem kid23_part604_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part604) = true := by rfl

def kid23_part605 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 7 7 true (2),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 13 (4,false),
.cycle 11 4 true (2),
.cycle 21 7 false (2),
.last 19 (4,false),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 7 7 true (2),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 17 (4,false)
]),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 64, 5, 64],[2, 32, 4, 1, 64, 5, 64],80⟩,
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 21 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,false),
.cycle 9 9 true (2),
.last 13 (4,false),
.last 16 (4,false),
.cycle 7 7 true (3),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 25 9 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
]),
.cycle 0 15 true (0),
.cycle 9 4 true (2),
.cycle 19 5 false (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.split 12 (4,true) (byMove [
.cycle 14 4 true (1),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.cycle 25 1 false (1),
.last 13 (4,false),
.last 17 (4,false),
.cycle 6 7 true (2),
.last 16 (4,false),
.last 14 (4,false),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 1 16 true (1),
.cycle 19 5 false (2),
.last 19 (4,false),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 6 7 true (2),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.last 15 (4,false)
]),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 0 19 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 5 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
]),
.cycle 10 2 true (3)
])
theorem kid23_part605_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part605) = true := by rfl

def kid23_part606 : Audit := .cycle 1 12 true (1)
theorem kid23_part606_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part606) = true := by rfl

def kid23_part608 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 23 5 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (2),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 13 3 true (3),
.cycle 6 9 true (2),
.cycle 9 6 true (2),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 11 4 true (2),
.cycle 23 5 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (2)
])
theorem kid23_part608_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part608) = true := by rfl

def kid23_part609 : Audit := .cycle 1 20 true (1)
theorem kid23_part609_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part609) = true := by rfl

def kid23_part610 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 13 (4,false),
.last 17 (4,false),
.cycle 21 7 false (2),
.cycle 25 1 false (-1),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 31 1 false (1)
])
theorem kid23_part610_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part610) = true := by rfl

def kid23_part611 : Audit := .cycle 7 7 true (2)
theorem kid23_part611_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part611) = true := by rfl

def kid23_part612 : Audit := .split 13 (4,false) (byMove [
.cycle 9 12 true (0),
.cycle 26 13 false (1),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.last 18 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 17 1 true (3),
.last 16 (2,true),
.cycle 15 8 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.last 18 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.last 18 (2,true),
.cycle 21 1 true (-1),
.cycle 18 5 false (0)
])
theorem kid23_part612_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part612) = true := by rfl

def kid23_part613 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 21 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.last 17 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.last 25 (2,true),
.last 14 (2,true),
.cycle 7 9 true (1),
.last 21 (2,true),
.cycle 12 2 true (1),
.cycle 15 6 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.last 17 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.last 23 (2,true),
.last 14 (2,true),
.cycle 7 9 true (1),
.last 19 (2,true),
.last 22 (2,true)
])
theorem kid23_part613_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part613) = true := by rfl

def kid23_part614 : Audit := .cycle 1 12 true (1)
theorem kid23_part614_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part614) = true := by rfl

def kid23_part615 : Audit := .cycle 7 5 true (3)
theorem kid23_part615_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part615) = true := by rfl

def kid23_part616 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 28 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 9 9 true (2),
.last 13 (4,false),
.cycle 12 3 true (4),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 28 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
])
theorem kid23_part616_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part616) = true := by rfl

def kid23_part617 : Audit := .cycle 0 13 true (0)
theorem kid23_part617_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part617) = true := by rfl

def kid23_part618 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (2),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.last 16 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 4096, 128, 256, 8, 128, 4, 16, 4096],[128, 2048, 4096, 1, 16, 4096, 128, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 8, 4096, 128, 256, 8, 128, 8, 16, 4096],[128, 2048, 4096, 1, 16, 1, 128, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.cycle 13 1 true (5),
.last 16 (2,true),
.cycle 7 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 9 9 true (2),
.cycle 33 1 false (7),
.last 16 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3)
])
theorem kid23_part618_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part618) = true := by rfl

def kid23_part619 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 1 24 true (1),
.last 14 (2,true),
.cycle 7 9 true (2),
.last 17 (2,true),
.last 20 (2,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 17 (2,true),
.cycle 12 2 true (3),
.cycle 9 6 true (2),
.last 20 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.last 20 (2,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 17 (2,true),
.cycle 10 4 true (3)
])
theorem kid23_part619_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part619) = true := by rfl

def kid23_part620 : Audit := .cycle 9 4 true (2)
theorem kid23_part620_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part620) = true := by rfl

def kid23_part621 : Audit := .split 16 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 22 7 false (1),
.cycle 20 1 false (0),
.cycle 9 10 true (1),
.cycle 20 3 false (0),
.last 22 (4,false),
.cycle 6 11 true (1),
.cycle 17 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 1 18 true (1),
.last 23 (4,false),
.last 18 (4,false),
.cycle 21 9 false (2),
.cycle 20 5 false (1),
.cycle 17 12 true (-1),
.cycle 9 10 true (1),
.cycle 20 3 false (0),
.last 22 (4,false),
.cycle 23 15 false (4),
.cycle 20 11 false (3),
.cycle 2 17 true (1),
.cycle 1 18 true (1),
.cycle 20 9 false (2),
.cycle 20 7 false (2)
])
theorem kid23_part621_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part621) = true := by rfl

def kid23_part622 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.cycle 7 13 true (0),
.last 13 (4,false),
.cycle 1 33 true (-1),
.cycle 6 7 true (2),
.cycle 1 18 true (1),
.cycle 34 1 false (8),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 19 5 false (2),
.cycle 15 12 true (-2),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.last 13 (4,false),
.last 28 (4,false),
.cycle 6 7 true (2),
.cycle 9 4 true (2),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 5 11 true (1)
])
theorem kid23_part622_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part622) = true := by rfl

def kid23_part623 : Audit := .cycle 5 7 true (1)
theorem kid23_part623_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part623) = true := by rfl

def kid23_part624 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 33 11 true (0),
.last 14 (2,true),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 9 6 true (1),
.cycle 12 4 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.cycle 13 2 true (1),
.cycle 15 6 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 18 7 false (2),
.cycle 17 5 false (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.cycle 16 3 false (0)
])
theorem kid23_part624_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part624) = true := by rfl

def kid23_part625 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 21 (2,true),
.last 14 (2,true),
.cycle 21 1 false (-1),
.last 17 (2,true),
.last 18 (2,true),
.cycle 9 6 true (1),
.last 23 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.last 21 (2,true),
.cycle 12 2 true (1),
.cycle 15 6 false (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 21 1 false (-1),
.last 17 (2,true),
.last 18 (2,true),
.last 30 (2,true),
.last 21 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.last 19 (2,true),
.last 22 (2,true)
])
theorem kid23_part625_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part625) = true := by rfl

def kid23_part626 : Audit := .cycle 1 12 true (1)
theorem kid23_part626_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part626) = true := by rfl

def kid23_part627 : Audit := .cycle 7 5 true (3)
theorem kid23_part627_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part627) = true := by rfl

def kid23_part628 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 3 true (4),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
])
theorem kid23_part628_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part628) = true := by rfl

def kid23_part629 : Audit := .cycle 0 13 true (0)
theorem kid23_part629_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part629) = true := by rfl

def kid23_part630 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.last 16 (2,true),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.cycle 11 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3)
])
theorem kid23_part630_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part630) = true := by rfl

def kid23_part631 : Audit := .cycle 10 2 true (3)
theorem kid23_part631_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part631) = true := by rfl

def kid23_part607 : Audit := .split 11 (4,true) (byMove [(kid23_part608),(kid23_part609),(kid23_part610),(kid23_part611),(kid23_part612),(kid23_part613),(kid23_part614),(kid23_part615),(kid23_part616),(kid23_part617),(kid23_part618),(kid23_part619),(kid23_part620),(kid23_part621),(kid23_part622),(kid23_part623),(kid23_part624),(kid23_part625),(kid23_part626),(kid23_part627),(kid23_part628),(kid23_part629),(kid23_part630),(kid23_part631)])

theorem kid23_part607_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part607) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part608),(kid23_part609),(kid23_part610),(kid23_part611),(kid23_part612),(kid23_part613),(kid23_part614),(kid23_part615),(kid23_part616),(kid23_part617),(kid23_part618),(kid23_part619),(kid23_part620),(kid23_part621),(kid23_part622),(kid23_part623),(kid23_part624),(kid23_part625),(kid23_part626),(kid23_part627),(kid23_part628),(kid23_part629),(kid23_part630),(kid23_part631)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part608_checked

  · exact kid23_part614_checked

  · exact kid23_part620_checked

  · exact kid23_part626_checked

  · exact kid23_part609_checked

  · exact kid23_part615_checked

  · exact kid23_part621_checked

  · exact kid23_part627_checked

  · exact kid23_part610_checked

  · exact kid23_part616_checked

  · exact kid23_part622_checked

  · exact kid23_part628_checked

  · exact kid23_part611_checked

  · exact kid23_part617_checked

  · exact kid23_part623_checked

  · exact kid23_part629_checked

  · exact kid23_part612_checked

  · exact kid23_part618_checked

  · exact kid23_part624_checked

  · exact kid23_part630_checked

  · exact kid23_part613_checked

  · exact kid23_part619_checked

  · exact kid23_part625_checked

  · exact kid23_part631_checked

def kid23_part632 : Audit := .split 19 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 13 8 false (1),
.cycle 22 1 false (-2),
.cycle 15 9 false (1),
.split 20 (4,true) (byMove [
.cycle 39 15 true (-1),
.cycle 15 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 15 9 false (1),
.cycle 24 25 true (0),
.cycle 35 13 true (0),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 17 4 true (-2),
.cycle 15 11 false (1),
.cycle 18 3 false (-1),
.cycle 15 11 false (1),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 15 10 false (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2304, 4096, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 2048, 4096, 1, 128, 256, 128, 2048, 256, 1, 128, 256, 4096],5136⟩,
.cycle 35 13 true (0),
.cycle 15 11 false (1),
.last 21 (4,false),
.cycle 13 8 false (1)
]),
.cycle 16 4 false (0),
.cycle 9 12 false (4),
.cycle 11 10 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 31 11 true (0),
.split 20 (4,true) (byMove [
.last 74 (4,false),
.cycle 1 36 true (-2),
.cycle 15 13 false (1),
.proven (BB6.Agent11Raw39Pumps.M2557.table) (fun m hm => BB6.Agent11Raw39Pumps.M2557.never m hm),
.last 21 (4,false),
.cycle 13 8 false (1),
.cycle 31 11 true (0),
.cycle 35 9 true (1),
.last 51 (4,false),
.cycle 1 32 true (-2),
.last 25 (4,false),
.last 44 (4,false),
.cycle 15 10 false (1),
.last 35 (4,false),
.cycle 35 13 true (0),
.cycle 15 11 false (1),
.last 21 (4,false),
.cycle 13 8 false (1),
.cycle 10 14 false (4),
.cycle 9 12 false (4),
.cycle 21 17 true (1),
.cycle 11 18 false (4),
.last 25 (4,false),
.cycle 11 10 false (3)
]),
.cycle 12 8 false (2),
.cycle 15 8 false (1),
.cycle 14 6 false (1),
.cycle 15 11 false (1),
.cycle 15 9 false (1),
.split 20 (4,true) (byMove [
.cycle 22 4 true (-3),
.cycle 13 21 false (2),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 15 9 false (1),
.cycle 14 7 false (1),
.last 22 (4,false),
.cycle 15 10 true (-2),
.last 27 (4,false),
.cycle 16 5 false (0),
.cycle 15 9 false (1),
.cycle 18 3 false (-1),
.cycle 15 11 false (1),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 17 4 false (-1),
.cycle 15 10 false (1),
.cycle 15 8 false (1),
.cycle 19 2 true (-2),
.cycle 9 14 false (4),
.last 27 (4,false),
.cycle 15 6 false (1)
]),
.cycle 16 4 false (0),
.cycle 15 10 false (2),
.cycle 15 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 15 14 false (3),
.split 20 (4,true) (byMove [
.last 74 (4,false),
.cycle 15 10 false (1),
.last 22 (4,false),
.cycle 9 14 false (4),
.last 23 (4,false),
.cycle 15 6 false (1),
.cycle 15 14 false (3),
.cycle 15 12 false (2),
.cycle 21 16 true (1),
.cycle 1 32 true (-2),
.last 25 (4,false),
.cycle 15 10 false (1),
.cycle 15 10 false (1),
.cycle 15 8 false (1),
.cycle 19 2 true (-1),
.cycle 9 14 false (4),
.last 23 (4,false),
.cycle 15 6 false (1),
.cycle 15 12 false (3),
.cycle 15 10 false (2),
.last 58 (4,false),
.cycle 15 16 false (4),
.last 25 (4,false),
.cycle 15 8 false (1)
]),
.cycle 15 6 false (1)
])
theorem kid23_part632_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part632) = true := by rfl

def kid23_part633 : Audit := .cycle 0 11 true (0)
theorem kid23_part633_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part633) = true := by rfl

def kid23_part634 : Audit := .cycle 1 10 true (1)
theorem kid23_part634_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part634) = true := by rfl

def kid23_part635 : Audit := .cycle 2 9 true (1)
theorem kid23_part635_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part635) = true := by rfl

def kid23_part636 : Audit := .cycle 1 13 true (1)
theorem kid23_part636_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part636) = true := by rfl

def kid23_part637 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 23 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 12 3 true (4),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.cycle 8 5 true (3)
]),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.last 29 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 23 1 false (1),
.last 15 (2,true),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 17 1 false (-1),
.cycle 12 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.cycle 8 5 true (3)
]),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 9 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 37 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 10 5 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.last 24 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3)
]),
.cycle 6 6 true (2),
.cycle 9 3 true (3),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 17 (4,true),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 23 6 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (4),
.cycle 9 5 true (3),
.last 15 (4,true),
.cycle 9 9 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (4)
]),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 7 11 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 17 1 false (-1),
.last 29 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 49 1 false (9),
.cycle 10 3 true (4),
.cycle 9 5 true (3),
.cycle 9 7 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 17 1 false (-1),
.cycle 12 2 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.cycle 10 3 true (4)
]),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 24 (2,true),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.cycle 12 5 true (4),
.last 16 (2,true),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 24 (2,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.cycle 8 6 true (3)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part637_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part637) = true := by rfl

def kid23_part638 : Audit := .cycle 8 3 true (3)
theorem kid23_part638_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part638) = true := by rfl

def kid23_part566 : Audit := .split 10 (5,true) (byMove [(kid23_part567),(kid23_part568),(kid23_part569),(kid23_part570),(kid23_part571),(kid23_part596),(kid23_part597),(kid23_part598),(kid23_part599),(kid23_part600),(kid23_part601),(kid23_part602),(kid23_part603),(kid23_part604),(kid23_part605),(kid23_part606),(kid23_part607),(kid23_part632),(kid23_part633),(kid23_part634),(kid23_part635),(kid23_part636),(kid23_part637),(kid23_part638)])

theorem kid23_part566_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (kid23_part566) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (5,true) (some mv)) (byMove [(kid23_part567),(kid23_part568),(kid23_part569),(kid23_part570),(kid23_part571),(kid23_part596),(kid23_part597),(kid23_part598),(kid23_part599),(kid23_part600),(kid23_part601),(kid23_part602),(kid23_part603),(kid23_part604),(kid23_part605),(kid23_part606),(kid23_part607),(kid23_part632),(kid23_part633),(kid23_part634),(kid23_part635),(kid23_part636),(kid23_part637),(kid23_part638)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part567_checked

  · exact kid23_part597_checked

  · exact kid23_part603_checked

  · exact kid23_part633_checked

  · exact kid23_part568_checked

  · exact kid23_part598_checked

  · exact kid23_part604_checked

  · exact kid23_part634_checked

  · exact kid23_part569_checked

  · exact kid23_part599_checked

  · exact kid23_part605_checked

  · exact kid23_part635_checked

  · exact kid23_part570_checked

  · exact kid23_part600_checked

  · exact kid23_part606_checked

  · exact kid23_part636_checked

  · exact kid23_part571_checked

  · exact kid23_part601_checked

  · exact kid23_part607_checked

  · exact kid23_part637_checked

  · exact kid23_part596_checked

  · exact kid23_part602_checked

  · exact kid23_part632_checked

  · exact kid23_part638_checked

def kid23_part640 : Audit := .cycle 1 13 true (1)
theorem kid23_part640_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part640) = true := by rfl

def kid23_part641 : Audit := .cycle 1 16 true (1)
theorem kid23_part641_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part641) = true := by rfl

def kid23_part642 : Audit := .cycle 21 1 false (1)
theorem kid23_part642_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part642) = true := by rfl

def kid23_part643 : Audit := .cycle 7 5 true (2)
theorem kid23_part643_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part643) = true := by rfl

def kid23_part645 : Audit := .cycle 0 15 true (0)
theorem kid23_part645_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part645) = true := by rfl

def kid23_part646 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (1),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.last 23 (4,false),
.last 23 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 13 8 true (1),
.cycle 3 16 true (1),
.last 19 (4,false),
.cycle 0 22 true (0),
.last 27 (4,false),
.cycle 17 2 true (3),
.cycle 9 10 true (1),
.cycle 1 20 true (1),
.last 23 (4,false),
.last 23 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.last 25 (4,false)
])
theorem kid23_part646_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part646) = true := by rfl

def kid23_part647 : Audit := .cycle 21 1 false (1)
theorem kid23_part647_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part647) = true := by rfl

def kid23_part648 : Audit := .cycle 0 17 true (0)
theorem kid23_part648_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part648) = true := by rfl

def kid23_part649 : Audit := .split 11 (4,false) (byMove [
.last 20 (5,true),
.last 23 (5,true),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 15 1 true (3),
.cycle 7 9 true (1),
.cycle 13 6 false (2),
.last 13 (5,true),
.last 40 (5,true),
.cycle 0 17 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 15 21 false (4),
.cycle 0 15 true (0),
.last 18 (5,true),
.cycle 1 22 true (1),
.cycle 19 1 true (-1),
.cycle 15 3 false (0)
])
theorem kid23_part649_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part649) = true := by rfl

def kid23_part650 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.last 21 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 21 (5,true),
.last 26 (5,true),
.last 28 (5,true),
.last 20 (5,true),
.cycle 14 1 false (0),
.cycle 0 23 true (-1),
.cycle 0 21 true (-1),
.last 26 (5,true),
.last 28 (5,true),
.last 28 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 21 (5,true),
.last 19 (5,true),
.last 17 (5,true),
.last 20 (5,true),
.last 28 (5,true),
.last 16 (5,true),
.cycle 11 3 false (1)
])
theorem kid23_part650_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part650) = true := by rfl

def kid23_part651 : Audit := .cycle 7 5 true (2)
theorem kid23_part651_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part651) = true := by rfl

def kid23_part652 : Audit := .cycle 1 13 true (1)
theorem kid23_part652_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part652) = true := by rfl

def kid23_part653 : Audit := .cycle 0 13 true (0)
theorem kid23_part653_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part653) = true := by rfl

def kid23_part654 : Audit := .split 17 (5,true) (byMove [
.cycle 3 19 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 7 13 true (0),
.cycle 34 1 false (4),
.cycle 0 27 true (-1),
.cycle 1 18 true (0),
.last 21 (4,false),
.last 19 (4,false),
.cycle 0 19 true (0),
.last 26 (4,false),
.cycle 0 22 true (0),
.cycle 18 11 true (2),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 5 13 true (0),
.cycle 1 20 true (0),
.cycle 14 8 true (-1),
.cycle 1 18 true (0),
.cycle 1 27 true (0),
.cycle 3 17 true (0),
.cycle 0 19 true (0),
.cycle 3 16 true (0),
.cycle 18 9 true (2)
])
theorem kid23_part654_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part654) = true := by rfl

def kid23_part655 : Audit := .split 11 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.last 12 (5,true),
.last 14 (5,true),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 19 1 false (5),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.last 12 (5,true)
])
theorem kid23_part655_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part655) = true := by rfl

def kid23_part656 : Audit := .cycle 1 14 true (1)
theorem kid23_part656_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part656) = true := by rfl

def kid23_part657 : Audit := .cycle 17 5 false (2)
theorem kid23_part657_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part657) = true := by rfl

def kid23_part658 : Audit := .split 15 (5,true) (byMove [
.cycle 1 25 true (0),
.last 19 (4,false),
.last 17 (4,false),
.cycle 0 21 true (0),
.cycle 16 3 false (0),
.last 33 (4,false),
.cycle 0 22 true (0),
.cycle 0 19 true (0),
.last 25 (4,false),
.cycle 22 3 false (2),
.last 16 (4,false),
.cycle 0 44 true (0),
.cycle 19 3 false (1),
.cycle 14 2 true (0),
.last 17 (4,false),
.cycle 0 21 true (0),
.cycle 16 3 false (0),
.cycle 23 3 false (1),
.cycle 0 22 true (0),
.cycle 0 19 true (0),
.cycle 2 21 true (0),
.cycle 1 26 true (0),
.last 16 (4,false),
.cycle 17 3 false (1)
])
theorem kid23_part658_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part658) = true := by rfl

def kid23_part659 : Audit := .cycle 7 7 true (1)
theorem kid23_part659_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part659) = true := by rfl

def kid23_part660 : Audit := .cycle 18 1 false (0)
theorem kid23_part660_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part660) = true := by rfl

def kid23_part661 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.last 23 (5,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 6 12 true (1),
.cycle 9 8 true (1),
.last 21 (5,true),
.cycle 7 7 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 22 (5,true),
.last 19 (5,true),
.cycle 14 3 false (0),
.cycle 7 7 true (1),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid23_part661_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part661) = true := by rfl

def kid23_part662 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.last 21 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 21 (5,true),
.last 16 (5,true),
.last 24 (5,true),
.last 20 (5,true),
.cycle 14 1 false (0),
.last 31 (5,true),
.last 29 (5,true),
.last 26 (5,true),
.last 28 (5,true),
.last 18 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 21 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.last 20 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.cycle 11 3 false (1)
])
theorem kid23_part662_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part662) = true := by rfl

def kid23_part663 : Audit := .cycle 7 5 true (2)
theorem kid23_part663_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part663) = true := by rfl

def kid23_part664 : Audit := .cycle 1 13 true (1)
theorem kid23_part664_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part664) = true := by rfl

def kid23_part665 : Audit := .cycle 0 13 true (0)
theorem kid23_part665_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part665) = true := by rfl

def kid23_part666 : Audit := .cycle 4 7 true (1)
theorem kid23_part666_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part666) = true := by rfl

def kid23_part667 : Audit := .split 11 (4,false) (byMove [
.cycle 1 17 true (1),
.last 27 (5,true),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 30 (5,true),
.cycle 5 7 true (1),
.cycle 13 3 true (3),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.last 12 (5,true)
])
theorem kid23_part667_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part667) = true := by rfl

def kid23_part668 : Audit := .split 13 (4,false) (byMove [
.cycle 1 18 true (0),
.last 25 (5,true),
.cycle 17 1 false (-1),
.cycle 25 1 false (-1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 9 6 true (1),
.cycle 1 16 true (1),
.last 19 (5,true),
.last 16 (5,true),
.cycle 5 11 true (1),
.cycle 15 8 false (2),
.last 15 (5,true),
.last 30 (5,true),
.cycle 25 1 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.cycle 18 9 false (2),
.cycle 1 16 true (1),
.last 18 (5,true),
.last 16 (5,true),
.cycle 17 3 false (1)
])
theorem kid23_part668_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part668) = true := by rfl

def kid23_part644 : Audit := .split 10 (4,true) (byMove [(kid23_part645),(kid23_part646),(kid23_part647),(kid23_part648),(kid23_part649),(kid23_part650),(kid23_part651),(kid23_part652),(kid23_part653),(kid23_part654),(kid23_part655),(kid23_part656),(kid23_part657),(kid23_part658),(kid23_part659),(kid23_part660),(kid23_part661),(kid23_part662),(kid23_part663),(kid23_part664),(kid23_part665),(kid23_part666),(kid23_part667),(kid23_part668)])

theorem kid23_part644_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part644) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part645),(kid23_part646),(kid23_part647),(kid23_part648),(kid23_part649),(kid23_part650),(kid23_part651),(kid23_part652),(kid23_part653),(kid23_part654),(kid23_part655),(kid23_part656),(kid23_part657),(kid23_part658),(kid23_part659),(kid23_part660),(kid23_part661),(kid23_part662),(kid23_part663),(kid23_part664),(kid23_part665),(kid23_part666),(kid23_part667),(kid23_part668)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part645_checked

  · exact kid23_part651_checked

  · exact kid23_part657_checked

  · exact kid23_part663_checked

  · exact kid23_part646_checked

  · exact kid23_part652_checked

  · exact kid23_part658_checked

  · exact kid23_part664_checked

  · exact kid23_part647_checked

  · exact kid23_part653_checked

  · exact kid23_part659_checked

  · exact kid23_part665_checked

  · exact kid23_part648_checked

  · exact kid23_part654_checked

  · exact kid23_part660_checked

  · exact kid23_part666_checked

  · exact kid23_part649_checked

  · exact kid23_part655_checked

  · exact kid23_part661_checked

  · exact kid23_part667_checked

  · exact kid23_part650_checked

  · exact kid23_part656_checked

  · exact kid23_part662_checked

  · exact kid23_part668_checked

def kid23_part669 : Audit := .split 10 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 7 12 true (1),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.split 11 (4,false) (byMove [
.last 21 (4,true),
.cycle 19 11 false (2),
.last 25 (4,true),
.cycle 0 17 true (0),
.last 12 (4,true),
.cycle 0 17 false (4),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 20 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 7 9 true (1),
.cycle 13 6 false (2),
.last 14 (4,true),
.last 28 (4,true),
.cycle 0 17 true (0),
.last 12 (4,true),
.last 21 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 19 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.cycle 12 11 false (2)
]),
.cycle 0 64 true (-2),
.cycle 7 5 true (2),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 0 19 true (0),
.split 11 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.last 20 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 7 12 true (2),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 17 true (0),
.cycle 7 10 true (2),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 18 (4,true),
.last 14 (4,true),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 28 (4,true)
]),
.cycle 1 14 true (1),
.cycle 17 5 false (2),
.cycle 13 2 true (0),
.cycle 7 7 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.last 21 (4,true),
.last 20 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 9 false (1),
.last 16 (4,true),
.last 35 (4,true),
.last 32 (4,true),
.cycle 7 7 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.last 16 (4,true),
.last 14 (4,true),
.cycle 7 7 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 17 8 true (-2),
.cycle 7 5 true (2),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 11 (4,false) (byMove [
.cycle 1 17 true (1),
.last 35 (4,true),
.cycle 0 84 true (-2),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 55 28 true (3),
.cycle 14 12 true (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 17 true (0),
.cycle 6 10 true (2),
.last 14 (4,true),
.last 31 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 6 true (2)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 47, 64],[2, 32, 47, 1, 64, 32, 64],80⟩
])
theorem kid23_part669_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part669) = true := by rfl

def kid23_part670 : Audit := .cycle 1 10 true (1)
theorem kid23_part670_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part670) = true := by rfl

def kid23_part671 : Audit := .cycle 7 3 true (3)
theorem kid23_part671_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part671) = true := by rfl

def kid23_part672 : Audit := .split 19 (5,true) (byMove [
.cycle 1 31 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 47, 64, 5, 64],[2, 32, 4, 1, 64, 13, 64],80⟩,
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.split 20 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 27 true (0),
.cycle 35 1 false (3),
.cycle 0 35 true (0),
.last 22 (4,false),
.last 22 (4,false),
.cycle 7 15 true (2),
.cycle 1 31 true (1),
.cycle 0 23 true (0),
.cycle 3 25 true (1),
.last 21 (4,false),
.cycle 1 24 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 2048, 4096, 128, 2048, 4, 1, 2048, 4, 4096],5136⟩,
.cycle 13 14 true (2),
.cycle 0 25 true (0),
.cycle 1 35 true (1),
.last 22 (4,false),
.last 22 (4,false),
.cycle 7 15 true (2),
.cycle 1 31 true (1),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 21 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 2048, 4096, 128, 2048, 4, 1, 2048, 4, 4096],5136⟩
]),
.cycle 0 29 true (0),
.cycle 1 20 true (1),
.cycle 1 35 true (1),
.cycle 10 10 true (2),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (2),
.last 28 (4,false),
.last 21 (4,false),
.cycle 0 24 true (0),
.cycle 7 15 true (2),
.last 31 (4,false),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 21 (4,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 16777216, 1, 128, 256, 32768, 128, 16777216, 1048580, 128, 256, 2097152, 2048, 16777216, 262144, 128, 256, 8, 65536, 16777216, 1, 16777216],[128, 2048, 4, 1, 128, 16, 128, 2048, 16384, 4096, 132, 65536, 128, 2048, 1048576, 262144, 4, 4194304, 128, 2048, 4, 1, 128, 16, 16777216],23151632⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 36 (4,false)
]),
.cycle 0 24 true (0),
.cycle 6 17 true (2),
.cycle 18 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 64, 5, 64],[2, 32, 4, 1, 64, 5, 64],80⟩,
.cycle 5 15 true (1),
.split 20 (4,true) (byMove [
.cycle 9 14 true (2),
.cycle 52 1 false (10),
.cycle 1 24 true (1),
.cycle 7 21 true (2),
.last 22 (4,false),
.last 22 (4,false),
.cycle 6 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 2, 4096, 128, 2048, 4, 1, 2, 2048, 4096],5136⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 1 22 true (1),
.last 23 (4,false),
.last 22 (4,false),
.cycle 17 4 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5136⟩,
.cycle 48 1 false (10),
.cycle 5 21 true (1),
.last 22 (4,false),
.last 22 (4,false),
.cycle 6 15 true (2),
.cycle 7 17 true (2),
.cycle 9 12 true (2),
.cycle 1 22 true (1),
.last 23 (4,false),
.cycle 19 2 true (4)
]),
.cycle 16 8 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 30 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.last 22 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 29 (4,false),
.cycle 3 18 true (1),
.last 21 (4,false),
.cycle 0 24 true (0),
.cycle 6 15 true (2),
.last 23 (4,false),
.cycle 9 12 true (2),
.cycle 1 22 true (1),
.last 24 (4,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (2)
]),
.cycle 8 13 true (2)
])
theorem kid23_part672_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part672) = true := by rfl

def kid23_part673 : Audit := .cycle 0 11 true (0)
theorem kid23_part673_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part673) = true := by rfl

def kid23_part675 : Audit := .cycle 0 11 true (0)
theorem kid23_part675_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part675) = true := by rfl

def kid23_part676 : Audit := .cycle 1 10 true (1)
theorem kid23_part676_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part676) = true := by rfl

def kid23_part677 : Audit := .cycle 2 9 true (1)
theorem kid23_part677_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part677) = true := by rfl

def kid23_part678 : Audit := .cycle 1 13 true (1)
theorem kid23_part678_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part678) = true := by rfl

def kid23_part679 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part679_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part679) = true := by rfl

def kid23_part680 : Audit := .cycle 0 17 true (0)
theorem kid23_part680_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part680) = true := by rfl

def kid23_part681 : Audit := .cycle 0 11 true (0)
theorem kid23_part681_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part681) = true := by rfl

def kid23_part682 : Audit := .cycle 1 10 true (1)
theorem kid23_part682_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part682) = true := by rfl

def kid23_part683 : Audit := .split 19 (5,true) (byMove [
.last 23 (4,false),
.last 25 (4,false),
.last 21 (4,false),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 0 29 true (0),
.cycle 1 20 true (1),
.cycle 1 35 true (1),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 10 10 true (2),
.cycle 0 24 true (0),
.cycle 6 17 true (2),
.cycle 18 2 true (4),
.last 23 (4,false),
.cycle 5 15 true (1),
.last 37 (4,false),
.cycle 16 8 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 21 (4,false),
.cycle 0 21 true (0),
.last 29 (4,false),
.cycle 8 13 true (2)
])
theorem kid23_part683_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part683) = true := by rfl

def kid23_part684 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 19 (4,false),
.cycle 0 19 true (0),
.cycle 3 16 true (1),
.cycle 0 23 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 11 8 true (2),
.cycle 3 15 true (1),
.last 18 (4,false),
.cycle 0 21 true (0),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.cycle 9 9 true (2),
.cycle 1 19 true (1),
.cycle 0 20 true (0),
.cycle 14 8 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 18 (4,false),
.cycle 8 10 true (2)
])
theorem kid23_part684_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part684) = true := by rfl

def kid23_part685 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 11 3 true (4),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 31 1 false (7),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part685_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part685) = true := by rfl

def kid23_part686 : Audit := .cycle 0 14 true (0)
theorem kid23_part686_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part686) = true := by rfl

def kid23_part687 : Audit := .cycle 7 5 true (3)
theorem kid23_part687_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part687) = true := by rfl

def kid23_part688 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 17 (5,true),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 13 1 true (5),
.cycle 0 17 true (0),
.cycle 7 8 true (3),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 17 (5,true),
.cycle 9 9 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3)
])
theorem kid23_part688_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part688) = true := by rfl

def kid23_part689 : Audit := .cycle 0 13 true (0)
theorem kid23_part689_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part689) = true := by rfl

def kid23_part690 : Audit := .cycle 4 7 true (1)
theorem kid23_part690_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part690) = true := by rfl

def kid23_part691 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 20 true (1),
.last 21 (5,true),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 5 11 true (1),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 17 3 false (1),
.last 12 (5,true)
])
theorem kid23_part691_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part691) = true := by rfl

def kid23_part692 : Audit := .cycle 5 11 true (1)
theorem kid23_part692_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part692) = true := by rfl

def kid23_part693 : Audit := .cycle 0 11 true (0)
theorem kid23_part693_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part693) = true := by rfl

def kid23_part694 : Audit := .cycle 1 10 true (1)
theorem kid23_part694_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part694) = true := by rfl

def kid23_part695 : Audit := .cycle 2 9 true (1)
theorem kid23_part695_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part695) = true := by rfl

def kid23_part696 : Audit := .cycle 1 13 true (1)
theorem kid23_part696_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part696) = true := by rfl

def kid23_part697 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part697_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part697) = true := by rfl

def kid23_part698 : Audit := .cycle 8 3 true (3)
theorem kid23_part698_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part698) = true := by rfl

def kid23_part674 : Audit := .split 10 (4,true) (byMove [(kid23_part675),(kid23_part676),(kid23_part677),(kid23_part678),(kid23_part679),(kid23_part680),(kid23_part681),(kid23_part682),(kid23_part683),(kid23_part684),(kid23_part685),(kid23_part686),(kid23_part687),(kid23_part688),(kid23_part689),(kid23_part690),(kid23_part691),(kid23_part692),(kid23_part693),(kid23_part694),(kid23_part695),(kid23_part696),(kid23_part697),(kid23_part698)])

theorem kid23_part674_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part674) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid23_part675),(kid23_part676),(kid23_part677),(kid23_part678),(kid23_part679),(kid23_part680),(kid23_part681),(kid23_part682),(kid23_part683),(kid23_part684),(kid23_part685),(kid23_part686),(kid23_part687),(kid23_part688),(kid23_part689),(kid23_part690),(kid23_part691),(kid23_part692),(kid23_part693),(kid23_part694),(kid23_part695),(kid23_part696),(kid23_part697),(kid23_part698)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part675_checked

  · exact kid23_part681_checked

  · exact kid23_part687_checked

  · exact kid23_part693_checked

  · exact kid23_part676_checked

  · exact kid23_part682_checked

  · exact kid23_part688_checked

  · exact kid23_part694_checked

  · exact kid23_part677_checked

  · exact kid23_part683_checked

  · exact kid23_part689_checked

  · exact kid23_part695_checked

  · exact kid23_part678_checked

  · exact kid23_part684_checked

  · exact kid23_part690_checked

  · exact kid23_part696_checked

  · exact kid23_part679_checked

  · exact kid23_part685_checked

  · exact kid23_part691_checked

  · exact kid23_part697_checked

  · exact kid23_part680_checked

  · exact kid23_part686_checked

  · exact kid23_part692_checked

  · exact kid23_part698_checked

def kid23_part699 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 19 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 1 13 true (1),
.last 12 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 16908288, 2176, 1, 8192, 16384, 8, 131200, 2176, 16385, 524288, 1048576, 512, 128, 16777216, 16385, 524288, 1048576, 2097152, 27009024, 25690112, 18087936, 16777216],[128, 2048, 32, 1, 16777216, 16385, 8192, 131072, 32, 1, 16777216, 16777216, 524288, 8388608, 2048, 64, 16777216, 16777216, 524288, 8388608, 8388608, 262144, 16777216, 18087936, 16777216],33370446⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (3)
]),
.cycle 0 17 true (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 24 true (0),
.cycle 3 15 true (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 19 true (1),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (4,true),
.last 20 (4,true),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 4 15 true (1),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 0 14 true (0),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 11 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 20 true (1),
.cycle 1 16 true (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 12 11 false (2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (3),
.last 15 (4,true),
.last 14 (4,true),
.cycle 5 11 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 22 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 5 11 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 8 3 true (3)
])
theorem kid23_part699_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part699) = true := by rfl

def kid23_part700 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.cycle 25 9 false (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 9 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.cycle 27 13 false (2),
.cycle 21 5 false (2),
.cycle 1 15 true (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 8 6 true (2)
]),
.cycle 0 25 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 8 true (2),
.cycle 3 10 true (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 10 8 true (2),
.cycle 13 1 true (5),
.cycle 0 17 true (0),
.cycle 7 8 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 6 true (3)
]),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.cycle 6 11 true (2),
.cycle 25 7 false (2),
.cycle 25 9 false (2),
.cycle 7 9 true (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 7 9 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 10 4 true (2),
.cycle 23 9 false (2),
.cycle 21 5 false (2),
.cycle 5 9 true (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 12 2 true (3)
]),
.cycle 18 8 true (-3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 9 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.cycle 9 5 true (2),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2)
]),
.cycle 8 5 true (2)
])
theorem kid23_part700_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part700) = true := by rfl

def kid23_part701 : Audit := .split 11 (5,true) (byMove [
.cycle 1 17 true (1),
.cycle 21 7 false (1),
.cycle 17 5 false (1),
.cycle 7 7 true (2),
.split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 27 17 false (2),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.last 30 (4,false),
.cycle 7 7 true (2),
.cycle 1 17 true (1),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.last 13 (4,false),
.cycle 1 16 true (1),
.cycle 21 7 false (2),
.cycle 18 5 false (1),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 30 (4,false),
.cycle 7 7 true (2),
.cycle 1 17 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 21 7 false (1)
]),
.cycle 0 33 false (4),
.cycle 1 12 true (1),
.cycle 9 7 true (2),
.cycle 15 8 true (3),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 21 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (2),
.last 20 (4,false),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 21 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 9 7 true (2)
]),
.cycle 0 16 true (0),
.cycle 6 9 true (2),
.cycle 10 2 true (2),
.cycle 17 5 false (1),
.cycle 5 7 true (1),
.split 12 (4,true) (byMove [
.cycle 14 6 true (1),
.cycle 1 16 true (1),
.cycle 28 1 false (0),
.cycle 34 1 false (2),
.last 13 (4,false),
.last 28 (4,false),
.cycle 6 7 true (2),
.cycle 9 11 true (2),
.cycle 9 6 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.last 14 (4,false),
.cycle 14 4 true (1),
.cycle 18 5 false (1),
.cycle 5 9 true (1),
.cycle 32 1 false (2),
.last 13 (4,false),
.last 28 (4,false),
.cycle 6 7 true (2),
.cycle 7 9 true (2),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 11 2 true (2)
]),
.cycle 18 8 true (-3),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 16 (4,false),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
]),
.cycle 8 5 true (2)
])
theorem kid23_part701_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part701) = true := by rfl

def kid23_part702 : Audit := .cycle 5 7 true (1)
theorem kid23_part702_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part702) = true := by rfl

def kid23_part703 : Audit := .cycle 5 5 true (1)
theorem kid23_part703_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part703) = true := by rfl

def kid23_part705 : Audit := .cycle 12 4 true (1)
theorem kid23_part705_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part705) = true := by rfl

def kid23_part706 : Audit := .cycle 1 14 true (1)
theorem kid23_part706_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part706) = true := by rfl

def kid23_part707 : Audit := .split 17 (5,true) (byMove [
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 7 13 true (0),
.last 20 (4,false),
.cycle 0 27 true (-1),
.cycle 1 18 true (0),
.last 21 (4,false),
.last 19 (4,false),
.cycle 0 19 true (0),
.cycle 2 17 true (0),
.cycle 0 22 true (0),
.cycle 29 1 false (1),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 5 13 true (0),
.last 20 (4,false),
.cycle 14 8 true (-1),
.cycle 1 18 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 19 true (0),
.last 22 (4,false),
.cycle 25 1 false (1)
])
theorem kid23_part707_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part707) = true := by rfl

def kid23_part708 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 22 true (0),
.cycle 0 23 true (0),
.cycle 0 26 true (0),
.cycle 0 21 true (0),
.proven (BB6.Agent11Raw39Pumps.M2569.table) (fun m hm => BB6.Agent11Raw39Pumps.M2569.never m hm),
.cycle 19 8 true (3),
.cycle 3 18 true (0),
.last 21 (4,false),
.cycle 0 24 true (0),
.cycle 15 9 true (1),
.cycle 19 2 true (3),
.cycle 23 1 false (1),
.cycle 1 22 true (0),
.cycle 28 1 false (2),
.cycle 19 8 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 1 23 true (0),
.last 21 (4,false),
.cycle 15 7 true (1)
])
theorem kid23_part708_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part708) = true := by rfl

def kid23_part709 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.cycle 1 24 false (4),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 14 (5,true),
.cycle 9 4 true (1),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 17 1 true (3),
.cycle 5 9 true (1),
.cycle 13 6 false (2),
.last 13 (5,true),
.last 26 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 14 (5,true),
.last 25 (5,true),
.cycle 1 14 true (1),
.last 16 (5,true),
.cycle 28 1 true (-2),
.last 19 (5,true)
])
theorem kid23_part709_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part709) = true := by rfl

def kid23_part710 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.last 21 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 24 (5,true),
.last 15 (5,true),
.cycle 12 2 true (-1),
.last 19 (5,true),
.last 28 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 22 (5,true),
.last 26 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 21 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid23_part710_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part710) = true := by rfl

def kid23_part711 : Audit := .cycle 6 5 true (2)
theorem kid23_part711_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part711) = true := by rfl

def kid23_part712 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.last 16 (4,false),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 14 (4,false),
.cycle 1 14 true (1),
.last 17 (4,false),
.cycle 5 11 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part712_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part712) = true := by rfl

def kid23_part713 : Audit := .split 12 (4,false) (byMove [
.cycle 14 6 true (1),
.cycle 1 16 true (1),
.last 19 (5,true),
.last 24 (5,true),
.cycle 16 1 false (2),
.last 21 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 27 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 16 1 false (0),
.last 21 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 24 (5,true),
.last 13 (5,true)
])
theorem kid23_part713_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part713) = true := by rfl

def kid23_part714 : Audit := .cycle 1 12 true (1)
theorem kid23_part714_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part714) = true := by rfl

def kid23_part715 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 13 1 true (5),
.cycle 0 17 true (0),
.cycle 7 8 true (2),
.cycle 11 5 true (3),
.cycle 0 16 true (0),
.last 21 (5,true),
.cycle 24 1 false (6),
.cycle 1 17 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.last 17 (5,true)
])
theorem kid23_part715_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part715) = true := by rfl

def kid23_part716 : Audit := .split 11 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.last 15 (4,false),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 6 9 true (2),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.cycle 5 13 true (0),
.last 12 (4,false),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.cycle 8 5 true (2)
])
theorem kid23_part716_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part716) = true := by rfl

def kid23_part717 : Audit := .split 13 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 19 7 false (2),
.cycle 17 5 false (2),
.cycle 7 9 true (1),
.cycle 21 9 false (2),
.last 33 (4,false),
.cycle 1 14 true (1),
.last 17 (4,false),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 12 9 true (2),
.cycle 0 18 true (0),
.cycle 12 11 true (2),
.cycle 12 2 true (2),
.cycle 17 5 false (2),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.cycle 14 8 true (-2),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 17 true (1),
.cycle 0 15 true (0),
.cycle 12 9 true (2),
.cycle 12 7 true (2)
])
theorem kid23_part717_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part717) = true := by rfl

def kid23_part718 : Audit := .split 15 (5,true) (byMove [
.cycle 11 6 true (0),
.last 19 (4,false),
.last 17 (4,false),
.cycle 7 15 true (0),
.cycle 16 3 false (0),
.cycle 11 10 true (-2),
.cycle 0 19 true (0),
.last 21 (4,false),
.last 17 (4,false),
.cycle 3 31 true (0),
.cycle 10 6 true (0),
.cycle 0 22 true (0),
.cycle 17 13 true (1),
.cycle 14 2 true (0),
.last 17 (4,false),
.cycle 5 15 true (0),
.cycle 16 3 false (0),
.cycle 15 8 true (-2),
.cycle 0 19 true (0),
.cycle 1 25 true (0),
.cycle 12 4 true (0),
.cycle 5 11 true (0),
.last 25 (4,false),
.cycle 16 7 true (2)
])
theorem kid23_part718_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part718) = true := by rfl

def kid23_part719 : Audit := .cycle 5 7 true (1)
theorem kid23_part719_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part719) = true := by rfl

def kid23_part720 : Audit := .split 15 (5,true) (byMove [
.cycle 5 15 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 7 11 true (0),
.cycle 28 1 false (2),
.cycle 0 25 true (-1),
.cycle 1 16 true (0),
.last 19 (4,false),
.last 17 (4,false),
.cycle 0 17 true (0),
.cycle 4 13 true (0),
.cycle 0 20 true (0),
.cycle 16 9 true (2),
.cycle 14 2 true (2),
.cycle 18 1 false (0),
.cycle 5 11 true (0),
.cycle 28 1 false (2),
.cycle 12 8 true (-1),
.cycle 1 16 true (0),
.cycle 1 23 true (0),
.cycle 5 13 true (0),
.cycle 0 17 true (0),
.cycle 1 18 true (0),
.cycle 16 7 true (2)
])
theorem kid23_part720_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part720) = true := by rfl

def kid23_part721 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.last 21 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 11 2 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 14 3 false (0),
.cycle 5 7 true (1),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid23_part721_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part721) = true := by rfl

def kid23_part722 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.last 19 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 12 2 true (-1),
.last 17 (5,true),
.last 20 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 22 (5,true),
.last 18 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 21 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid23_part722_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part722) = true := by rfl

def kid23_part723 : Audit := .cycle 6 5 true (2)
theorem kid23_part723_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part723) = true := by rfl

def kid23_part724 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 7 8 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part724_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part724) = true := by rfl

def kid23_part725 : Audit := .cycle 9 2 true (2)
theorem kid23_part725_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part725) = true := by rfl

def kid23_part726 : Audit := .cycle 1 12 true (1)
theorem kid23_part726_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part726) = true := by rfl

def kid23_part727 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 9 5 true (2),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2)
])
theorem kid23_part727_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part727) = true := by rfl

def kid23_part728 : Audit := .split 11 (5,true) (byMove [
.cycle 1 17 true (1),
.last 15 (4,false),
.last 13 (4,false),
.cycle 7 7 true (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 1 12 true (1),
.last 15 (4,false),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 0 16 true (0),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 13 (4,false),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.last 15 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 8 5 true (2),
.cycle 8 5 true (2)
])
theorem kid23_part728_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part728) = true := by rfl

def kid23_part704 : Audit := .split 10 (4,true) (byMove [(kid23_part705),(kid23_part706),(kid23_part707),(kid23_part708),(kid23_part709),(kid23_part710),(kid23_part711),(kid23_part712),(kid23_part713),(kid23_part714),(kid23_part715),(kid23_part716),(kid23_part717),(kid23_part718),(kid23_part719),(kid23_part720),(kid23_part721),(kid23_part722),(kid23_part723),(kid23_part724),(kid23_part725),(kid23_part726),(kid23_part727),(kid23_part728)])

theorem kid23_part704_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part704) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part705),(kid23_part706),(kid23_part707),(kid23_part708),(kid23_part709),(kid23_part710),(kid23_part711),(kid23_part712),(kid23_part713),(kid23_part714),(kid23_part715),(kid23_part716),(kid23_part717),(kid23_part718),(kid23_part719),(kid23_part720),(kid23_part721),(kid23_part722),(kid23_part723),(kid23_part724),(kid23_part725),(kid23_part726),(kid23_part727),(kid23_part728)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part705_checked

  · exact kid23_part711_checked

  · exact kid23_part717_checked

  · exact kid23_part723_checked

  · exact kid23_part706_checked

  · exact kid23_part712_checked

  · exact kid23_part718_checked

  · exact kid23_part724_checked

  · exact kid23_part707_checked

  · exact kid23_part713_checked

  · exact kid23_part719_checked

  · exact kid23_part725_checked

  · exact kid23_part708_checked

  · exact kid23_part714_checked

  · exact kid23_part720_checked

  · exact kid23_part726_checked

  · exact kid23_part709_checked

  · exact kid23_part715_checked

  · exact kid23_part721_checked

  · exact kid23_part727_checked

  · exact kid23_part710_checked

  · exact kid23_part716_checked

  · exact kid23_part722_checked

  · exact kid23_part728_checked

def kid23_part729 : Audit := .split 10 (5,true) (byMove [
.cycle 12 4 true (1),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 0 22 true (0),
.split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.last 32 (4,true),
.cycle 1 20 true (-2),
.last 17 (4,true),
.last 12 (4,true),
.last 26 (4,true),
.last 15 (4,true),
.cycle 9 4 true (1),
.cycle 1 14 true (1),
.last 18 (4,true),
.last 13 (4,true),
.cycle 5 9 true (1),
.cycle 13 6 false (2),
.last 14 (4,true),
.last 27 (4,true),
.last 17 (4,true),
.last 12 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 13 (4,true),
.last 24 (4,true)
]),
.cycle 1 36 true (-2),
.cycle 6 5 true (2),
.cycle 1 12 true (1),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 2 19 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 5 12 true (1),
.cycle 1 16 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.last 15 (4,false),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.cycle 4 15 true (0),
.last 12 (4,false),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false)
]),
.cycle 0 16 true (0),
.cycle 12 11 true (2),
.cycle 13 2 true (0),
.cycle 5 7 true (1),
.cycle 5 11 true (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.last 21 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.last 12 (4,true),
.last 29 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 21 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 12 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 13 8 true (-2),
.cycle 6 5 true (2),
.cycle 1 12 true (1),
.cycle 9 2 true (2),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 1 17 true (1),
.cycle 15 20 true (-2),
.last 21 (4,false),
.cycle 7 7 true (2),
.last 13 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.last 28 (4,false),
.cycle 14 20 true (-2),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.cycle 14 14 true (-2),
.cycle 5 7 true (1),
.last 13 (4,false),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false)
]),
.cycle 8 5 true (2)
])
theorem kid23_part729_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part729) = true := by rfl

def kid23_part730 : Audit := .cycle 1 10 true (1)
theorem kid23_part730_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part730) = true := by rfl

def kid23_part731 : Audit := .cycle 7 3 true (3)
theorem kid23_part731_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part731) = true := by rfl

def kid23_part732 : Audit := .cycle 2 9 true (1)
theorem kid23_part732_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part732) = true := by rfl

def kid23_part733 : Audit := .cycle 0 11 true (0)
theorem kid23_part733_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part733) = true := by rfl

def kid23_part735 : Audit := .cycle 1 11 true (1)
theorem kid23_part735_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part735) = true := by rfl

def kid23_part736 : Audit := .cycle 7 4 true (3)
theorem kid23_part736_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part736) = true := by rfl

def kid23_part737 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 33 1 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 1 14 true (1),
.last 23 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3)
])
theorem kid23_part737_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part737) = true := by rfl

def kid23_part738 : Audit := .cycle 0 12 true (0)
theorem kid23_part738_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part738) = true := by rfl

def kid23_part739 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 17 13 false (1),
.cycle 13 2 true (0),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 0 17 true (0),
.cycle 15 8 false (2),
.last 15 (5,true),
.cycle 0 20 true (-2),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 17 5 false (1)
])
theorem kid23_part739_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part739) = true := by rfl

def kid23_part740 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 17 (4,false),
.cycle 0 20 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 0 17 true (0),
.cycle 1 13 true (1),
.last 17 (4,false),
.cycle 24 8 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (3)
])
theorem kid23_part740_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part740) = true := by rfl

def kid23_part741 : Audit := .cycle 0 11 true (0)
theorem kid23_part741_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part741) = true := by rfl

def kid23_part742 : Audit := .cycle 1 10 true (1)
theorem kid23_part742_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part742) = true := by rfl

def kid23_part743 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 20 (4,false),
.cycle 0 20 true (0),
.cycle 10 9 true (3),
.cycle 0 37 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.last 19 (4,false),
.cycle 0 22 true (0),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.cycle 9 10 true (3),
.cycle 1 20 true (1),
.last 21 (4,false),
.last 27 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
])
theorem kid23_part743_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part743) = true := by rfl

def kid23_part744 : Audit := .cycle 3 8 true (1)
theorem kid23_part744_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part744) = true := by rfl

def kid23_part745 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 40 1 false (8),
.cycle 1 20 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part745_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part745) = true := by rfl

def kid23_part746 : Audit := .cycle 0 14 true (0)
theorem kid23_part746_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part746) = true := by rfl

def kid23_part747 : Audit := .cycle 6 5 true (2)
theorem kid23_part747_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part747) = true := by rfl

def kid23_part748 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 19 (4,false),
.cycle 0 24 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 9 4 true (3),
.cycle 1 14 true (1),
.cycle 22 9 false (2),
.cycle 19 8 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
])
theorem kid23_part748_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part748) = true := by rfl

def kid23_part749 : Audit := .cycle 9 2 true (3)
theorem kid23_part749_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part749) = true := by rfl

def kid23_part750 : Audit := .cycle 1 12 true (1)
theorem kid23_part750_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part750) = true := by rfl

def kid23_part751 : Audit := .split 13 (4,false) (byMove [
.cycle 15 8 false (3),
.last 25 (5,true),
.cycle 13 2 true (0),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 11 4 true (1),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 22 (5,true),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 16 5 false (2),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.last 14 (5,true)
])
theorem kid23_part751_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part751) = true := by rfl

def kid23_part752 : Audit := .split 11 (5,true) (byMove [
.last 15 (4,false),
.cycle 1 20 true (1),
.last 13 (4,false),
.cycle 7 7 true (2),
.last 17 (4,false),
.last 33 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 5 15 true (1),
.cycle 0 16 true (0),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.cycle 5 11 true (1),
.cycle 5 7 true (1),
.last 17 (4,false),
.cycle 16 8 true (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 8 5 true (3)
])
theorem kid23_part752_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part752) = true := by rfl

def kid23_part753 : Audit := .cycle 0 11 true (0)
theorem kid23_part753_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part753) = true := by rfl

def kid23_part754 : Audit := .cycle 1 10 true (1)
theorem kid23_part754_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part754) = true := by rfl

def kid23_part755 : Audit := .cycle 2 9 true (1)
theorem kid23_part755_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part755) = true := by rfl

def kid23_part756 : Audit := .cycle 1 13 true (1)
theorem kid23_part756_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part756) = true := by rfl

def kid23_part757 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 11 2 true (4),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part757_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part757) = true := by rfl

def kid23_part758 : Audit := .cycle 8 3 true (3)
theorem kid23_part758_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part758) = true := by rfl

def kid23_part734 : Audit := .split 10 (4,true) (byMove [(kid23_part735),(kid23_part736),(kid23_part737),(kid23_part738),(kid23_part739),(kid23_part740),(kid23_part741),(kid23_part742),(kid23_part743),(kid23_part744),(kid23_part745),(kid23_part746),(kid23_part747),(kid23_part748),(kid23_part749),(kid23_part750),(kid23_part751),(kid23_part752),(kid23_part753),(kid23_part754),(kid23_part755),(kid23_part756),(kid23_part757),(kid23_part758)])

theorem kid23_part734_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part734) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid23_part735),(kid23_part736),(kid23_part737),(kid23_part738),(kid23_part739),(kid23_part740),(kid23_part741),(kid23_part742),(kid23_part743),(kid23_part744),(kid23_part745),(kid23_part746),(kid23_part747),(kid23_part748),(kid23_part749),(kid23_part750),(kid23_part751),(kid23_part752),(kid23_part753),(kid23_part754),(kid23_part755),(kid23_part756),(kid23_part757),(kid23_part758)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part735_checked

  · exact kid23_part741_checked

  · exact kid23_part747_checked

  · exact kid23_part753_checked

  · exact kid23_part736_checked

  · exact kid23_part742_checked

  · exact kid23_part748_checked

  · exact kid23_part754_checked

  · exact kid23_part737_checked

  · exact kid23_part743_checked

  · exact kid23_part749_checked

  · exact kid23_part755_checked

  · exact kid23_part738_checked

  · exact kid23_part744_checked

  · exact kid23_part750_checked

  · exact kid23_part756_checked

  · exact kid23_part739_checked

  · exact kid23_part745_checked

  · exact kid23_part751_checked

  · exact kid23_part757_checked

  · exact kid23_part740_checked

  · exact kid23_part746_checked

  · exact kid23_part752_checked

  · exact kid23_part758_checked

def kid23_part759 : Audit := .split 10 (5,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 22 9 false (2),
.cycle 0 17 true (0),
.cycle 1 13 true (1),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (3)
]),
.cycle 0 20 true (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 10 8 true (3),
.cycle 3 8 true (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 10 8 true (3),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 0 14 true (0),
.cycle 6 5 true (2),
.cycle 10 2 true (3),
.cycle 9 2 true (3),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 8 7 true (2),
.cycle 1 20 true (1),
.cycle 31 1 false (1),
.cycle 7 7 true (2),
.last 13 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (3),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 10 4 true (2),
.cycle 20 7 false (2),
.cycle 5 11 true (1),
.cycle 5 7 true (1),
.last 13 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (3),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 10 2 true (3)
]),
.cycle 15 8 true (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 8 3 true (3)
])
theorem kid23_part759_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part759) = true := by rfl

def kid23_part639 : Audit := .split 9 (2,true) (byMove [(kid23_part640),(kid23_part641),(kid23_part642),(kid23_part643),(kid23_part644),(kid23_part669),(kid23_part670),(kid23_part671),(kid23_part672),(kid23_part673),(kid23_part674),(kid23_part699),(kid23_part700),(kid23_part701),(kid23_part702),(kid23_part703),(kid23_part704),(kid23_part729),(kid23_part730),(kid23_part731),(kid23_part732),(kid23_part733),(kid23_part734),(kid23_part759)])

theorem kid23_part639_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (kid23_part639) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) 9 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part640),(kid23_part641),(kid23_part642),(kid23_part643),(kid23_part644),(kid23_part669),(kid23_part670),(kid23_part671),(kid23_part672),(kid23_part673),(kid23_part674),(kid23_part699),(kid23_part700),(kid23_part701),(kid23_part702),(kid23_part703),(kid23_part704),(kid23_part729),(kid23_part730),(kid23_part731),(kid23_part732),(kid23_part733),(kid23_part734),(kid23_part759)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part640_checked

  · exact kid23_part670_checked

  · exact kid23_part700_checked

  · exact kid23_part730_checked

  · exact kid23_part641_checked

  · exact kid23_part671_checked

  · exact kid23_part701_checked

  · exact kid23_part731_checked

  · exact kid23_part642_checked

  · exact kid23_part672_checked

  · exact kid23_part702_checked

  · exact kid23_part732_checked

  · exact kid23_part643_checked

  · exact kid23_part673_checked

  · exact kid23_part703_checked

  · exact kid23_part733_checked

  · exact kid23_part644_checked

  · exact kid23_part674_checked

  · exact kid23_part704_checked

  · exact kid23_part734_checked

  · exact kid23_part669_checked

  · exact kid23_part699_checked

  · exact kid23_part729_checked

  · exact kid23_part759_checked

def kid23_part760 : Audit := .cycle 1 10 true (1)
theorem kid23_part760_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (kid23_part760) = true := by rfl

def kid23_part763 : Audit := .cycle 1 13 true (1)
theorem kid23_part763_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part763) = true := by rfl

def kid23_part764 : Audit := .cycle 7 6 true (2)
theorem kid23_part764_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part764) = true := by rfl

def kid23_part765 : Audit := .cycle 29 1 false (1)
theorem kid23_part765_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part765) = true := by rfl

def kid23_part766 : Audit := .cycle 0 14 true (0)
theorem kid23_part766_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part766) = true := by rfl

def kid23_part767 : Audit := .cycle 1 14 true (1)
theorem kid23_part767_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part767) = true := by rfl

def kid23_part768 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.last 23 (4,false),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 23 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 13 8 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 8 true (2),
.cycle 13 2 true (2),
.last 23 (4,false),
.cycle 1 15 true (1),
.cycle 21 5 false (2),
.last 23 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 8 6 true (2)
])
theorem kid23_part768_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part768) = true := by rfl

def kid23_part769 : Audit := .cycle 0 13 true (0)
theorem kid23_part769_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part769) = true := by rfl

def kid23_part770 : Audit := .cycle 1 12 true (1)
theorem kid23_part770_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part770) = true := by rfl

def kid23_part771 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 12 9 true (3),
.cycle 0 22 true (0),
.cycle 1 22 true (1),
.cycle 41 15 false (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 13 8 true (3),
.cycle 3 18 true (1),
.last 21 (4,false),
.last 22 (4,false),
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 256, 1, 128, 2048, 4, 1, 256, 4, 4096],5168⟩,
.cycle 1 22 true (1),
.cycle 9 12 true (2),
.far true 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[4096, 5120, 512, 512, 16777216, 1024, 6144, 5120, 16781312, 512, 16777216, 1024, 4096, 16781312, 512, 2097152, 16777216, 4194304, 25432064, 29627392, 31723520, 2097152, 16777216, 4194304, 16777216],[4096, 4096, 512, 4096, 1, 2048, 6144, 2048, 512, 5120, 4096, 2048, 4096, 4096, 16781312, 5120, 262144, 8388608, 25432064, 8650752, 31724032, 29626368, 262144, 8388608, 16777216],31403506⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (2)
])
theorem kid23_part771_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part771) = true := by rfl

def kid23_part772 : Audit := .cycle 3 10 true (1)
theorem kid23_part772_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part772) = true := by rfl

def kid23_part773 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 13 1 true (5),
.last 16 (5,true),
.cycle 7 8 true (2),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 0 20 true (0),
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 6 true (3)
])
theorem kid23_part773_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part773) = true := by rfl

def kid23_part774 : Audit := .split 14 (4,false) (byMove [
.cycle 10 5 true (2),
.last 21 (5,true),
.last 27 (5,true),
.cycle 7 10 true (2),
.cycle 0 20 true (0),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.cycle 5 10 true (1),
.last 19 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 15 (5,true)
])
theorem kid23_part774_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part774) = true := by rfl

def kid23_part775 : Audit := .cycle 6 7 true (2)
theorem kid23_part775_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part775) = true := by rfl

def kid23_part776 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 23 5 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 27 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (3),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 6 9 true (2),
.cycle 13 2 true (3),
.cycle 23 5 false (1),
.cycle 1 16 true (1),
.cycle 9 6 true (2),
.last 27 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (2)
])
theorem kid23_part776_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part776) = true := by rfl

def kid23_part777 : Audit := .cycle 5 11 true (1)
theorem kid23_part777_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part777) = true := by rfl

def kid23_part778 : Audit := .cycle 1 14 true (1)
theorem kid23_part778_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part778) = true := by rfl

def kid23_part779 : Audit := .cycle 9 4 true (2)
theorem kid23_part779_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part779) = true := by rfl

def kid23_part780 : Audit := .split 13 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 25 7 false (2),
.last 23 (4,false),
.cycle 7 9 true (2),
.cycle 0 19 true (0),
.last 23 (4,false),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 25 7 false (2),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 16 (4,false),
.cycle 6 11 true (2),
.cycle 13 2 true (2),
.last 23 (4,false),
.cycle 5 9 true (1),
.cycle 21 5 false (2),
.last 23 (4,false),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 8 7 true (2)
])
theorem kid23_part780_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part780) = true := by rfl

def kid23_part781 : Audit := .cycle 0 13 true (0)
theorem kid23_part781_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part781) = true := by rfl

def kid23_part782 : Audit := .cycle 1 12 true (1)
theorem kid23_part782_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part782) = true := by rfl

def kid23_part783 : Audit := .cycle 2 11 true (1)
theorem kid23_part783_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part783) = true := by rfl

def kid23_part784 : Audit := .cycle 1 15 true (1)
theorem kid23_part784_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part784) = true := by rfl

def kid23_part785 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (4),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.last 16 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.cycle 9 5 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2)
])
theorem kid23_part785_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part785) = true := by rfl

def kid23_part786 : Audit := .cycle 8 5 true (2)
theorem kid23_part786_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part786) = true := by rfl

def kid23_part762 : Audit := .split 12 (2,true) (byMove [(kid23_part763),(kid23_part764),(kid23_part765),(kid23_part766),(kid23_part767),(kid23_part768),(kid23_part769),(kid23_part770),(kid23_part771),(kid23_part772),(kid23_part773),(kid23_part774),(kid23_part775),(kid23_part776),(kid23_part777),(kid23_part778),(kid23_part779),(kid23_part780),(kid23_part781),(kid23_part782),(kid23_part783),(kid23_part784),(kid23_part785),(kid23_part786)])

theorem kid23_part762_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part762) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid23_part763),(kid23_part764),(kid23_part765),(kid23_part766),(kid23_part767),(kid23_part768),(kid23_part769),(kid23_part770),(kid23_part771),(kid23_part772),(kid23_part773),(kid23_part774),(kid23_part775),(kid23_part776),(kid23_part777),(kid23_part778),(kid23_part779),(kid23_part780),(kid23_part781),(kid23_part782),(kid23_part783),(kid23_part784),(kid23_part785),(kid23_part786)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part763_checked

  · exact kid23_part769_checked

  · exact kid23_part775_checked

  · exact kid23_part781_checked

  · exact kid23_part764_checked

  · exact kid23_part770_checked

  · exact kid23_part776_checked

  · exact kid23_part782_checked

  · exact kid23_part765_checked

  · exact kid23_part771_checked

  · exact kid23_part777_checked

  · exact kid23_part783_checked

  · exact kid23_part766_checked

  · exact kid23_part772_checked

  · exact kid23_part778_checked

  · exact kid23_part784_checked

  · exact kid23_part767_checked

  · exact kid23_part773_checked

  · exact kid23_part779_checked

  · exact kid23_part785_checked

  · exact kid23_part768_checked

  · exact kid23_part774_checked

  · exact kid23_part780_checked

  · exact kid23_part786_checked

def kid23_part787 : Audit := .cycle 1 16 true (1)
theorem kid23_part787_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part787) = true := by rfl

def kid23_part789 : Audit := .cycle 0 15 true (0)
theorem kid23_part789_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part789) = true := by rfl

def kid23_part790 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (1),
.cycle 35 1 false (1),
.cycle 0 20 true (0),
.cycle 1 20 true (1),
.cycle 24 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 13 8 true (1),
.cycle 3 16 true (1),
.last 19 (4,false),
.last 20 (4,false),
.cycle 43 1 false (1),
.cycle 17 2 true (3),
.cycle 35 1 false (1),
.cycle 1 20 true (1),
.cycle 9 10 true (1),
.cycle 24 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 39 1 false (1)
])
theorem kid23_part790_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part790) = true := by rfl

def kid23_part791 : Audit := .cycle 21 1 false (1)
theorem kid23_part791_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part791) = true := by rfl

def kid23_part792 : Audit := .cycle 0 17 true (0)
theorem kid23_part792_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part792) = true := by rfl

def kid23_part793 : Audit := .split 11 (4,false) (byMove [
.last 20 (5,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.last 23 (5,true),
.last 14 (5,true),
.cycle 13 6 false (2),
.last 13 (5,true),
.last 40 (5,true),
.cycle 0 17 true (0),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 41 1 false (-1),
.cycle 0 15 true (0),
.last 18 (5,true),
.cycle 1 22 true (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1)
])
theorem kid23_part793_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part793) = true := by rfl

def kid23_part794 : Audit := .cycle 14 1 false (0)
theorem kid23_part794_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part794) = true := by rfl

def kid23_part795 : Audit := .cycle 7 5 true (2)
theorem kid23_part795_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part795) = true := by rfl

def kid23_part796 : Audit := .cycle 1 12 true (1)
theorem kid23_part796_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part796) = true := by rfl

def kid23_part797 : Audit := .cycle 0 13 true (0)
theorem kid23_part797_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part797) = true := by rfl

def kid23_part798 : Audit := .split 17 (5,true) (byMove [
.cycle 3 18 true (0),
.cycle 22 1 false (2),
.cycle 34 1 false (4),
.cycle 7 13 true (0),
.cycle 20 1 false (2),
.last 21 (4,false),
.cycle 1 18 true (0),
.cycle 26 20 true (4),
.cycle 19 8 true (2),
.cycle 0 19 true (0),
.cycle 2 17 true (0),
.last 20 (4,false),
.cycle 18 11 true (2),
.cycle 16 2 true (2),
.cycle 1 20 true (0),
.cycle 5 13 true (0),
.cycle 20 1 false (2),
.last 21 (4,false),
.cycle 1 18 true (0),
.cycle 1 27 true (0),
.cycle 3 16 true (0),
.cycle 0 19 true (0),
.cycle 3 17 true (0),
.cycle 18 9 true (2)
])
theorem kid23_part798_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part798) = true := by rfl

def kid23_part799 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 25 (5,true),
.cycle 0 13 true (0),
.last 21 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 14 1 true (4),
.last 12 (5,true)
])
theorem kid23_part799_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part799) = true := by rfl

def kid23_part800 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 1 16 true (1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 21 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.last 13 (5,true)
])
theorem kid23_part800_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part800) = true := by rfl

def kid23_part801 : Audit := .cycle 17 5 false (2)
theorem kid23_part801_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part801) = true := by rfl

def kid23_part802 : Audit := .split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 27 1 false (-1),
.cycle 15 5 false (1),
.cycle 0 22 true (0),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 7 9 true (1),
.cycle 1 18 true (1),
.cycle 0 17 true (0),
.cycle 3 18 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 19 9 false (2),
.cycle 13 2 true (1),
.cycle 15 5 false (1),
.cycle 1 22 true (1),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 12 7 true (1),
.cycle 1 18 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 17 7 false (2)
])
theorem kid23_part802_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part802) = true := by rfl

def kid23_part803 : Audit := .cycle 7 7 true (1)
theorem kid23_part803_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part803) = true := by rfl

def kid23_part804 : Audit := .cycle 18 1 false (0)
theorem kid23_part804_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part804) = true := by rfl

def kid23_part805 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 9 6 true (1),
.last 21 (5,true),
.cycle 10 2 true (1),
.cycle 7 7 true (1),
.cycle 25 1 false (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 27 1 false (-1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 7 7 true (1),
.cycle 16 1 false (0),
.last 12 (5,true)
])
theorem kid23_part805_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part805) = true := by rfl

def kid23_part806 : Audit := .cycle 14 1 false (0)
theorem kid23_part806_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part806) = true := by rfl

def kid23_part807 : Audit := .cycle 7 5 true (2)
theorem kid23_part807_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part807) = true := by rfl

def kid23_part808 : Audit := .cycle 1 12 true (1)
theorem kid23_part808_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part808) = true := by rfl

def kid23_part809 : Audit := .cycle 0 13 true (0)
theorem kid23_part809_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part809) = true := by rfl

def kid23_part810 : Audit := .cycle 4 7 true (1)
theorem kid23_part810_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part810) = true := by rfl

def kid23_part811 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (1),
.last 21 (5,true),
.cycle 10 2 true (2),
.cycle 7 7 true (2),
.cycle 25 1 false (1),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 9 4 true (2),
.cycle 5 7 true (1),
.last 19 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 14 1 true (4),
.last 12 (5,true)
])
theorem kid23_part811_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part811) = true := by rfl

def kid23_part812 : Audit := .split 19 (5,true) (byMove [
.cycle 35 1 false (1),
.cycle 27 1 false (1),
.cycle 27 1 false (1),
.cycle 7 15 true (0),
.cycle 25 1 false (1),
.last 23 (4,false),
.cycle 1 20 true (0),
.cycle 28 22 true (4),
.cycle 24 8 true (2),
.cycle 0 21 true (0),
.cycle 2 19 true (0),
.last 22 (4,false),
.cycle 37 1 false (1),
.cycle 18 2 true (2),
.cycle 19 2 true (2),
.cycle 5 15 true (0),
.cycle 25 1 false (1),
.last 23 (4,false),
.cycle 1 20 true (0),
.cycle 33 1 false (1),
.cycle 33 1 false (1),
.cycle 0 21 true (0),
.cycle 31 1 false (1),
.cycle 33 1 false (1)
])
theorem kid23_part812_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part812) = true := by rfl

def kid23_part788 : Audit := .split 10 (2,true) (byMove [(kid23_part789),(kid23_part790),(kid23_part791),(kid23_part792),(kid23_part793),(kid23_part794),(kid23_part795),(kid23_part796),(kid23_part797),(kid23_part798),(kid23_part799),(kid23_part800),(kid23_part801),(kid23_part802),(kid23_part803),(kid23_part804),(kid23_part805),(kid23_part806),(kid23_part807),(kid23_part808),(kid23_part809),(kid23_part810),(kid23_part811),(kid23_part812)])

theorem kid23_part788_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part788) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part789),(kid23_part790),(kid23_part791),(kid23_part792),(kid23_part793),(kid23_part794),(kid23_part795),(kid23_part796),(kid23_part797),(kid23_part798),(kid23_part799),(kid23_part800),(kid23_part801),(kid23_part802),(kid23_part803),(kid23_part804),(kid23_part805),(kid23_part806),(kid23_part807),(kid23_part808),(kid23_part809),(kid23_part810),(kid23_part811),(kid23_part812)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part789_checked

  · exact kid23_part795_checked

  · exact kid23_part801_checked

  · exact kid23_part807_checked

  · exact kid23_part790_checked

  · exact kid23_part796_checked

  · exact kid23_part802_checked

  · exact kid23_part808_checked

  · exact kid23_part791_checked

  · exact kid23_part797_checked

  · exact kid23_part803_checked

  · exact kid23_part809_checked

  · exact kid23_part792_checked

  · exact kid23_part798_checked

  · exact kid23_part804_checked

  · exact kid23_part810_checked

  · exact kid23_part793_checked

  · exact kid23_part799_checked

  · exact kid23_part805_checked

  · exact kid23_part811_checked

  · exact kid23_part794_checked

  · exact kid23_part800_checked

  · exact kid23_part806_checked

  · exact kid23_part812_checked

def kid23_part813 : Audit := .cycle 7 5 true (2)
theorem kid23_part813_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part813) = true := by rfl

def kid23_part815 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (0),
.cycle 7 14 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 1 24 true (0),
.cycle 0 30 true (-2),
.cycle 0 21 true (0),
.cycle 13 20 true (1),
.cycle 15 8 true (1),
.cycle 3 18 true (0),
.cycle 0 22 true (0),
.last 25 (2,true),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 131072, 16384, 262144, 8192, 16384, 8, 128, 16384, 1, 8192, 16384, 8, 128, 16384, 131072, 262144],[128, 2048, 262144, 1, 8, 131072, 8192, 131072, 262144, 1, 131072, 131072, 8192, 131072, 262144, 1, 131072, 131072, 262144],262176⟩,
.cycle 19 2 true (3),
.last 21 (2,true),
.cycle 1 22 true (0),
.cycle 9 12 true (0),
.last 39 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 1 23 true (0),
.cycle 1 22 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 131072, 16384, 262144, 8192, 16384, 8, 128, 16384, 1, 8192, 16384, 8, 128, 16384, 131072, 262144],[128, 2048, 262144, 1, 8, 2048, 8192, 131072, 262144, 1, 131072, 131072, 8192, 131072, 262144, 1, 131072, 131072, 262144],262176⟩
])
theorem kid23_part815_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part815) = true := by rfl

def kid23_part816 : Audit := .split 23 (5,true) (byMove [
.cycle 50 11 false (1),
.cycle 24 11 false (1),
.last 24 (2,true),
.cycle 0 29 true (-2),
.cycle 24 11 false (0),
.cycle 13 44 false (3),
.last 26 (2,true),
.cycle 0 27 true (-2),
.last 32 (2,true),
.cycle 3 21 false (4),
.cycle 50 11 false (1),
.cycle 26 11 false (1),
.cycle 28 11 false (0),
.cycle 22 2 true (0),
.last 24 (2,true),
.cycle 0 29 true (-2),
.cycle 24 11 false (0),
.cycle 11 26 false (1),
.last 26 (2,true),
.cycle 0 27 true (-2),
.cycle 46 11 false (1),
.last 28 (2,true),
.cycle 28 11 false (0),
.cycle 26 11 false (0)
])
theorem kid23_part816_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part816) = true := by rfl

def kid23_part817 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 17 true (0),
.last 20 (5,true),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 20 1 false (-2),
.last 16 (5,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 17 true (0),
.last 20 (5,true),
.cycle 24 1 false (0),
.cycle 0 19 true (0),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
])
theorem kid23_part817_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part817) = true := by rfl

def kid23_part818 : Audit := .cycle 0 17 true (0)
theorem kid23_part818_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part818) = true := by rfl

def kid23_part819 : Audit := .cycle 13 1 false (-1)
theorem kid23_part819_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part819) = true := by rfl

def kid23_part820 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 23 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 35 2 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 1 20 true (0),
.cycle 22 2 false (0),
.cycle 0 19 true (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid23_part820_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part820) = true := by rfl

def kid23_part821 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (5,true),
.cycle 3 12 true (1),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.cycle 0 26 true (0),
.last 16 (5,true),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 9 6 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 0 24 true (0)
])
theorem kid23_part821_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part821) = true := by rfl

def kid23_part822 : Audit := .cycle 0 15 true (0)
theorem kid23_part822_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part822) = true := by rfl

def kid23_part823 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 26 1 false (2),
.last 20 (2,true),
.cycle 7 15 true (0),
.cycle 24 1 false (2),
.last 24 (2,true),
.cycle 1 20 true (0),
.cycle 0 26 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 13 20 true (0),
.last 23 (2,true),
.cycle 32 1 false (2),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 5 15 true (0),
.cycle 24 1 false (2),
.last 24 (2,true),
.cycle 1 20 true (0),
.cycle 28 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 26 1 false (2),
.cycle 28 1 false (2)
])
theorem kid23_part823_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part823) = true := by rfl

def kid23_part824 : Audit := .cycle 21 1 false (1)
theorem kid23_part824_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part824) = true := by rfl

def kid23_part825 : Audit := .cycle 15 1 true (3)
theorem kid23_part825_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part825) = true := by rfl

def kid23_part826 : Audit := .split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 7 16 true (1),
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.cycle 11 4 true (1),
.cycle 18 3 false (0),
.cycle 7 9 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 23 true (0),
.cycle 15 4 true (3),
.cycle 18 3 true (4),
.cycle 19 9 false (1),
.last 16 (2,true),
.cycle 7 11 true (1),
.cycle 26 1 false (0),
.cycle 13 2 true (1),
.cycle 18 3 false (0),
.last 27 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 15 4 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part826_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part826) = true := by rfl

def kid23_part827 : Audit := .cycle 13 6 false (2)
theorem kid23_part827_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part827) = true := by rfl

def kid23_part828 : Audit := .split 13 (5,true) (byMove [
.cycle 1 23 true (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 0 19 true (0),
.last 17 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.last 22 (2,true),
.last 24 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 21 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.cycle 0 19 true (0),
.last 17 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 19 true (0),
.last 18 (2,true),
.last 27 (2,true),
.last 19 (2,true)
])
theorem kid23_part828_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part828) = true := by rfl

def kid23_part829 : Audit := .split 12 (2,true) (byMove [
.last 24 (5,true),
.cycle 14 10 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 40 (5,true),
.last 20 (5,true),
.cycle 0 17 true (0),
.last 48 (5,true),
.cycle 15 1 false (3),
.cycle 3 14 true (0),
.cycle 0 21 true (-1),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 19 8 true (-2),
.last 19 (5,true),
.cycle 0 17 true (0),
.proven (BB6.Agent11Raw39Counter2575.Init.table) (fun m hm => BB6.Agent11Raw39Counter2575.never m hm),
.last 20 (5,true),
.cycle 1 19 true (0),
.last 26 (5,true),
.last 13 (5,true)
])
theorem kid23_part829_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part829) = true := by rfl

def kid23_part830 : Audit := .cycle 0 17 true (0)
theorem kid23_part830_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part830) = true := by rfl

def kid23_part831 : Audit := .cycle 13 1 false (-1)
theorem kid23_part831_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part831) = true := by rfl

def kid23_part832 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 16 2 false (0),
.last 13 (2,true),
.last 16 (2,true),
.cycle 14 2 false (0),
.cycle 14 2 false (2),
.cycle 22 2 false (-2),
.last 14 (2,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 17 2 false (-1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1)
])
theorem kid23_part832_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part832) = true := by rfl

def kid23_part833 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.last 30 (5,true),
.cycle 20 1 false (0),
.cycle 0 16 true (0),
.cycle 15 21 false (4),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (5,true),
.cycle 3 12 true (1),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.last 41 (5,true),
.last 16 (5,true),
.last 23 (5,true),
.cycle 1 16 true (1),
.last 28 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.last 37 (5,true)
])
theorem kid23_part833_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part833) = true := by rfl

def kid23_part834 : Audit := .cycle 0 15 true (0)
theorem kid23_part834_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part834) = true := by rfl

def kid23_part835 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (1),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 2 20 true (1),
.cycle 0 26 true (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 13 8 true (1),
.cycle 3 16 true (1),
.cycle 2 18 true (1),
.last 21 (2,true),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 131072, 256, 262144, 8192, 16384, 8, 128, 16384, 1, 8192, 16384, 8, 128, 16384, 131072, 262144],[128, 2048, 262144, 1, 8, 131072, 8192, 131072, 262144, 1, 131072, 131072, 8192, 131072, 262144, 1, 131072, 131072, 262144],262176⟩,
.cycle 17 2 true (3),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 9 10 true (1),
.last 33 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 2 18 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 131072, 256, 262144, 8192, 16384, 8, 128, 16384, 1, 8192, 16384, 8, 128, 16384, 131072, 262144],[128, 2048, 262144, 1, 8, 2048, 8192, 131072, 262144, 1, 131072, 131072, 8192, 131072, 262144, 1, 131072, 131072, 262144],262176⟩
])
theorem kid23_part835_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part835) = true := by rfl

def kid23_part836 : Audit := .split 16 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 7 10 true (1),
.cycle 37 1 false (1),
.cycle 0 18 true (0),
.cycle 1 22 true (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.last 24 (5,true),
.cycle 3 14 true (1),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 0 30 true (0),
.last 18 (5,true),
.cycle 5 15 true (1),
.cycle 1 18 true (1),
.cycle 9 8 true (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 1 20 true (1),
.cycle 0 28 true (0)
])
theorem kid23_part836_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part836) = true := by rfl

def kid23_part837 : Audit := .cycle 19 1 true (-1)
theorem kid23_part837_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part837) = true := by rfl

def kid23_part838 : Audit := .cycle 14 3 false (0)
theorem kid23_part838_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part838) = true := by rfl

def kid23_part814 : Audit := .split 11 (4,false) (byMove [(kid23_part815),(kid23_part816),(kid23_part817),(kid23_part818),(kid23_part819),(kid23_part820),(kid23_part821),(kid23_part822),(kid23_part823),(kid23_part824),(kid23_part825),(kid23_part826),(kid23_part827),(kid23_part828),(kid23_part829),(kid23_part830),(kid23_part831),(kid23_part832),(kid23_part833),(kid23_part834),(kid23_part835),(kid23_part836),(kid23_part837),(kid23_part838)])

theorem kid23_part814_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part814) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid23_part815),(kid23_part816),(kid23_part817),(kid23_part818),(kid23_part819),(kid23_part820),(kid23_part821),(kid23_part822),(kid23_part823),(kid23_part824),(kid23_part825),(kid23_part826),(kid23_part827),(kid23_part828),(kid23_part829),(kid23_part830),(kid23_part831),(kid23_part832),(kid23_part833),(kid23_part834),(kid23_part835),(kid23_part836),(kid23_part837),(kid23_part838)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part815_checked

  · exact kid23_part821_checked

  · exact kid23_part827_checked

  · exact kid23_part833_checked

  · exact kid23_part816_checked

  · exact kid23_part822_checked

  · exact kid23_part828_checked

  · exact kid23_part834_checked

  · exact kid23_part817_checked

  · exact kid23_part823_checked

  · exact kid23_part829_checked

  · exact kid23_part835_checked

  · exact kid23_part818_checked

  · exact kid23_part824_checked

  · exact kid23_part830_checked

  · exact kid23_part836_checked

  · exact kid23_part819_checked

  · exact kid23_part825_checked

  · exact kid23_part831_checked

  · exact kid23_part837_checked

  · exact kid23_part820_checked

  · exact kid23_part826_checked

  · exact kid23_part832_checked

  · exact kid23_part838_checked

def kid23_part840 : Audit := .cycle 0 15 true (0)
theorem kid23_part840_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part840) = true := by rfl

def kid23_part841 : Audit := .cycle 7 12 true (1)
theorem kid23_part841_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part841) = true := by rfl

def kid23_part842 : Audit := .cycle 21 1 false (1)
theorem kid23_part842_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part842) = true := by rfl

def kid23_part843 : Audit := .cycle 0 17 true (0)
theorem kid23_part843_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part843) = true := by rfl

def kid23_part844 : Audit := .split 11 (4,false) (byMove [
.cycle 1 24 true (0),
.cycle 1 25 false (4),
.last 12 (2,true),
.cycle 0 17 true (0),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 22 3 false (0),
.cycle 10 4 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 0 17 true (0),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 2 20 true (1),
.last 16 (2,true),
.cycle 23 1 true (-3),
.cycle 17 4 false (-1)
])
theorem kid23_part844_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part844) = true := by rfl

def kid23_part845 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 22 15 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (2,true),
.cycle 11 5 false (1),
.last 15 (2,true),
.last 26 (2,true),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 13 7 false (-1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (2,true),
.cycle 13 6 false (0),
.last 15 (2,true),
.cycle 7 10 false (4),
.cycle 13 4 false (-1),
.cycle 13 4 false (-1)
])
theorem kid23_part845_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part845) = true := by rfl

def kid23_part846 : Audit := .cycle 7 5 true (2)
theorem kid23_part846_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part846) = true := by rfl

def kid23_part847 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 17 (4,false),
.cycle 0 64 true (0),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 15 (4,false),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part847_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part847) = true := by rfl

def kid23_part848 : Audit := .cycle 0 13 true (0)
theorem kid23_part848_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part848) = true := by rfl

def kid23_part849 : Audit := .cycle 0 19 true (0)
theorem kid23_part849_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part849) = true := by rfl

def kid23_part850 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (-2),
.cycle 15 2 false (1),
.cycle 1 12 true (1),
.cycle 25 5 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 20 3 false (0),
.cycle 11 4 true (3),
.cycle 7 10 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.cycle 16 1 false (-2),
.cycle 16 2 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩
])
theorem kid23_part850_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part850) = true := by rfl

def kid23_part851 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.last 32 (2,true),
.last 17 (2,true),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 6 7 true (2),
.cycle 27 5 false (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 3 false (0),
.cycle 14 3 true (4),
.cycle 20 5 true (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 5 23 true (0),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 6 7 true (2),
.cycle 7 10 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.cycle 14 3 true (4)
])
theorem kid23_part851_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part851) = true := by rfl

def kid23_part852 : Audit := .cycle 17 5 false (2)
theorem kid23_part852_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part852) = true := by rfl

def kid23_part853 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 23 (4,false),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 7 7 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 17 2 true (3),
.last 13 (4,false),
.last 14 (4,false),
.cycle 17 2 true (0),
.cycle 13 2 true (1),
.cycle 35 2 true (3),
.cycle 1 18 true (1),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 17 2 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 15 2 true (0)
])
theorem kid23_part853_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part853) = true := by rfl

def kid23_part854 : Audit := .cycle 7 7 true (1)
theorem kid23_part854_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part854) = true := by rfl

def kid23_part855 : Audit := .cycle 18 1 false (0)
theorem kid23_part855_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part855) = true := by rfl

def kid23_part856 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 41 9 true (0),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 14 (2,true),
.cycle 15 5 false (1),
.last 12 (2,true),
.cycle 7 7 true (1),
.cycle 14 3 false (0),
.cycle 10 2 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 14 (2,true),
.cycle 18 5 false (0),
.last 12 (2,true),
.cycle 7 7 true (1),
.cycle 16 3 false (-1),
.cycle 15 4 false (0)
])
theorem kid23_part856_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part856) = true := by rfl

def kid23_part857 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 11 15 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (2,true),
.cycle 11 5 false (1),
.last 15 (2,true),
.cycle 17 8 true (-2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 13 7 false (-1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (2,true),
.cycle 18 6 false (-2),
.last 15 (2,true),
.cycle 10 10 false (2),
.cycle 13 4 false (-1),
.cycle 13 4 false (-1)
])
theorem kid23_part857_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part857) = true := by rfl

def kid23_part858 : Audit := .cycle 7 5 true (2)
theorem kid23_part858_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part858) = true := by rfl

def kid23_part859 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 14 true (1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.cycle 7 7 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part859_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part859) = true := by rfl

def kid23_part860 : Audit := .cycle 0 13 true (0)
theorem kid23_part860_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part860) = true := by rfl

def kid23_part861 : Audit := .cycle 4 7 true (1)
theorem kid23_part861_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part861) = true := by rfl

def kid23_part862 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 23 27 false (2),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 16 1 false (-2),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 17 5 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.cycle 11 4 true (3),
.cycle 6 10 true (2),
.cycle 15 3 true (3),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 16 1 false (-2),
.cycle 9 4 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 true (4),
.cycle 8 6 true (2)
])
theorem kid23_part862_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part862) = true := by rfl

def kid23_part863 : Audit := .split 16 (4,false) (byMove [
.last 19 (2,true),
.cycle 22 21 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.last 19 (2,true),
.cycle 13 5 false (1),
.last 17 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 8, 1, 128, 256, 8, 128, 8, 2048, 4096],[128, 2048, 4096, 1, 2176, 2048, 128, 2048, 4096, 1, 2048, 2048, 4096],4096⟩,
.cycle 14 3 false (0),
.cycle 13 5 false (1),
.cycle 13 13 false (1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.last 19 (2,true),
.cycle 13 8 false (1),
.last 17 (2,true),
.cycle 7 12 false (4),
.cycle 13 6 false (1),
.cycle 13 8 false (1)
])
theorem kid23_part863_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part863) = true := by rfl

def kid23_part839 : Audit := .split 10 (5,true) (byMove [(kid23_part840),(kid23_part841),(kid23_part842),(kid23_part843),(kid23_part844),(kid23_part845),(kid23_part846),(kid23_part847),(kid23_part848),(kid23_part849),(kid23_part850),(kid23_part851),(kid23_part852),(kid23_part853),(kid23_part854),(kid23_part855),(kid23_part856),(kid23_part857),(kid23_part858),(kid23_part859),(kid23_part860),(kid23_part861),(kid23_part862),(kid23_part863)])

theorem kid23_part839_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part839) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part840),(kid23_part841),(kid23_part842),(kid23_part843),(kid23_part844),(kid23_part845),(kid23_part846),(kid23_part847),(kid23_part848),(kid23_part849),(kid23_part850),(kid23_part851),(kid23_part852),(kid23_part853),(kid23_part854),(kid23_part855),(kid23_part856),(kid23_part857),(kid23_part858),(kid23_part859),(kid23_part860),(kid23_part861),(kid23_part862),(kid23_part863)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part840_checked

  · exact kid23_part846_checked

  · exact kid23_part852_checked

  · exact kid23_part858_checked

  · exact kid23_part841_checked

  · exact kid23_part847_checked

  · exact kid23_part853_checked

  · exact kid23_part859_checked

  · exact kid23_part842_checked

  · exact kid23_part848_checked

  · exact kid23_part854_checked

  · exact kid23_part860_checked

  · exact kid23_part843_checked

  · exact kid23_part849_checked

  · exact kid23_part855_checked

  · exact kid23_part861_checked

  · exact kid23_part844_checked

  · exact kid23_part850_checked

  · exact kid23_part856_checked

  · exact kid23_part862_checked

  · exact kid23_part845_checked

  · exact kid23_part851_checked

  · exact kid23_part857_checked

  · exact kid23_part863_checked

def kid23_part864 : Audit := .cycle 1 10 true (1)
theorem kid23_part864_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part864) = true := by rfl

def kid23_part865 : Audit := .cycle 7 3 true (3)
theorem kid23_part865_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part865) = true := by rfl

def kid23_part867 : Audit := .cycle 0 11 true (0)
theorem kid23_part867_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part867) = true := by rfl

def kid23_part868 : Audit := .cycle 1 10 true (1)
theorem kid23_part868_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part868) = true := by rfl

def kid23_part869 : Audit := .cycle 2 9 true (1)
theorem kid23_part869_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part869) = true := by rfl

def kid23_part870 : Audit := .cycle 1 13 true (1)
theorem kid23_part870_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part870) = true := by rfl

def kid23_part871 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 21 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.last 14 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 12 10 true (-2),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part871_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part871) = true := by rfl

def kid23_part872 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.cycle 0 38 true (-2),
.cycle 20 1 false (-2),
.cycle 27 1 false (-1),
.cycle 0 19 true (0),
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 11 6 true (1),
.cycle 19 3 false (1),
.cycle 0 17 true (0),
.last 25 (5,true),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 24 (5,true),
.cycle 27 1 false (-1),
.cycle 19 1 false (-1),
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 20 9 false (2),
.last 17 (5,true),
.cycle 0 17 true (0),
.last 24 (5,true),
.last 16 (5,true)
])
theorem kid23_part872_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part872) = true := by rfl

def kid23_part873 : Audit := .cycle 0 11 true (0)
theorem kid23_part873_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part873) = true := by rfl

def kid23_part874 : Audit := .cycle 1 10 true (1)
theorem kid23_part874_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part874) = true := by rfl

def kid23_part875 : Audit := .split 19 (5,true) (byMove [
.cycle 1 31 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 8, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 1 20 true (1),
.cycle 1 35 true (1),
.cycle 10 10 true (2),
.cycle 0 21 true (0),
.cycle 11 10 true (2),
.last 22 (4,false),
.cycle 6 17 true (2),
.cycle 18 2 true (4),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 1, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 5 15 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.last 23 (4,false),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.last 29 (4,false),
.cycle 8 13 true (2)
])
theorem kid23_part875_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part875) = true := by rfl

def kid23_part876 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 3 16 true (1),
.cycle 0 19 true (0),
.cycle 11 9 true (2),
.last 21 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 11 8 true (2),
.cycle 3 15 true (1),
.last 18 (4,false),
.last 19 (4,false),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 9 true (2),
.last 21 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 18 (4,false),
.cycle 8 10 true (2)
])
theorem kid23_part876_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part876) = true := by rfl

def kid23_part877 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.last 23 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 11 1 true (5),
.last 14 (5,true),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 32 1 false (8),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part877_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part877) = true := by rfl

def kid23_part878 : Audit := .split 12 (4,false) (byMove [
.cycle 14 5 true (4),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 7 15 true (2),
.last 23 (5,true),
.last 20 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 23 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 13 (5,true)
])
theorem kid23_part878_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part878) = true := by rfl

def kid23_part879 : Audit := .cycle 7 5 true (3)
theorem kid23_part879_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part879) = true := by rfl

def kid23_part880 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 23 5 false (1),
.cycle 0 16 true (0),
.cycle 13 9 true (2),
.last 26 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (3),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 6 9 true (2),
.cycle 13 2 true (3),
.cycle 23 5 false (1),
.cycle 1 16 true (1),
.cycle 9 6 true (3),
.last 26 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (3)
])
theorem kid23_part880_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part880) = true := by rfl

def kid23_part881 : Audit := .cycle 0 13 true (0)
theorem kid23_part881_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part881) = true := by rfl

def kid23_part882 : Audit := .cycle 4 7 true (1)
theorem kid23_part882_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part882) = true := by rfl

def kid23_part883 : Audit := .split 11 (4,false) (byMove [
.cycle 9 6 true (2),
.cycle 1 20 true (1),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 21 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 20 (5,true),
.cycle 5 7 true (1),
.cycle 18 1 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.last 20 (5,true),
.last 12 (5,true)
])
theorem kid23_part883_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part883) = true := by rfl

def kid23_part884 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.last 27 (5,true),
.cycle 20 1 false (-2),
.last 19 (5,true),
.cycle 28 1 false (2),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.cycle 19 3 false (1),
.cycle 5 11 true (1),
.cycle 12 4 true (1),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 23 (5,true),
.last 19 (5,true),
.cycle 19 1 false (-1),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.cycle 5 11 true (1),
.cycle 19 7 false (2),
.last 16 (5,true)
])
theorem kid23_part884_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part884) = true := by rfl

def kid23_part885 : Audit := .cycle 0 11 true (0)
theorem kid23_part885_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part885) = true := by rfl

def kid23_part886 : Audit := .cycle 1 10 true (1)
theorem kid23_part886_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part886) = true := by rfl

def kid23_part887 : Audit := .cycle 2 9 true (1)
theorem kid23_part887_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part887) = true := by rfl

def kid23_part888 : Audit := .cycle 1 13 true (1)
theorem kid23_part888_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part888) = true := by rfl

def kid23_part889 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.last 21 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.last 14 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.last 21 (5,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part889_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part889) = true := by rfl

def kid23_part890 : Audit := .cycle 8 3 true (3)
theorem kid23_part890_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part890) = true := by rfl

def kid23_part866 : Audit := .split 10 (2,true) (byMove [(kid23_part867),(kid23_part868),(kid23_part869),(kid23_part870),(kid23_part871),(kid23_part872),(kid23_part873),(kid23_part874),(kid23_part875),(kid23_part876),(kid23_part877),(kid23_part878),(kid23_part879),(kid23_part880),(kid23_part881),(kid23_part882),(kid23_part883),(kid23_part884),(kid23_part885),(kid23_part886),(kid23_part887),(kid23_part888),(kid23_part889),(kid23_part890)])

theorem kid23_part866_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part866) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid23_part867),(kid23_part868),(kid23_part869),(kid23_part870),(kid23_part871),(kid23_part872),(kid23_part873),(kid23_part874),(kid23_part875),(kid23_part876),(kid23_part877),(kid23_part878),(kid23_part879),(kid23_part880),(kid23_part881),(kid23_part882),(kid23_part883),(kid23_part884),(kid23_part885),(kid23_part886),(kid23_part887),(kid23_part888),(kid23_part889),(kid23_part890)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part867_checked

  · exact kid23_part873_checked

  · exact kid23_part879_checked

  · exact kid23_part885_checked

  · exact kid23_part868_checked

  · exact kid23_part874_checked

  · exact kid23_part880_checked

  · exact kid23_part886_checked

  · exact kid23_part869_checked

  · exact kid23_part875_checked

  · exact kid23_part881_checked

  · exact kid23_part887_checked

  · exact kid23_part870_checked

  · exact kid23_part876_checked

  · exact kid23_part882_checked

  · exact kid23_part888_checked

  · exact kid23_part871_checked

  · exact kid23_part877_checked

  · exact kid23_part883_checked

  · exact kid23_part889_checked

  · exact kid23_part872_checked

  · exact kid23_part878_checked

  · exact kid23_part884_checked

  · exact kid23_part890_checked

def kid23_part891 : Audit := .cycle 0 11 true (0)
theorem kid23_part891_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part891) = true := by rfl

def kid23_part893 : Audit := .cycle 0 12 true (0)
theorem kid23_part893_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part893) = true := by rfl

def kid23_part894 : Audit := .cycle 1 11 true (1)
theorem kid23_part894_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part894) = true := by rfl

def kid23_part895 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 2 20 true (1),
.last 24 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (2),
.cycle 3 17 true (1),
.cycle 2 19 true (1),
.last 22 (2,true),
.cycle 6 14 true (2),
.cycle 18 2 true (4),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 9 11 true (2),
.last 24 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (2,true),
.cycle 8 12 true (2)
])
theorem kid23_part895_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part895) = true := by rfl

def kid23_part896 : Audit := .cycle 3 9 true (1)
theorem kid23_part896_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part896) = true := by rfl

def kid23_part897 : Audit := .cycle 19 1 false (1)
theorem kid23_part897_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part897) = true := by rfl

def kid23_part898 : Audit := .split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 7 16 true (1),
.cycle 31 2 false (3),
.cycle 0 21 true (0),
.cycle 17 2 false (-1),
.cycle 18 2 false (2),
.cycle 7 9 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 23 true (0),
.cycle 19 2 false (1),
.cycle 20 2 false (2),
.cycle 43 2 false (1),
.last 16 (2,true),
.cycle 7 11 true (1),
.cycle 29 2 false (3),
.cycle 17 2 false (-1),
.cycle 19 2 false (3),
.cycle 7 9 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 13 2 true (2),
.cycle 29 2 false (3)
])
theorem kid23_part898_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part898) = true := by rfl

def kid23_part899 : Audit := .cycle 0 12 true (0)
theorem kid23_part899_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part899) = true := by rfl

def kid23_part900 : Audit := .cycle 1 11 true (1)
theorem kid23_part900_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part900) = true := by rfl

def kid23_part901 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 4096, 128, 256, 8, 128, 4, 16, 4096],[128, 2048, 4096, 1, 16, 8, 128, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.last 22 (2,true),
.cycle 0 27 true (0),
.last 24 (2,true),
.last 26 (2,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 4096, 128, 256, 8, 128, 4, 16, 4096],[128, 2048, 4096, 1, 16, 16, 128, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.last 26 (2,true),
.cycle 6 22 true (2),
.cycle 20 2 true (4),
.last 22 (2,true),
.cycle 1 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 4096, 128, 256, 8, 128, 4, 16, 4096],[128, 2048, 4096, 1, 16, 4096, 128, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.last 26 (2,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 9 13 true (2),
.cycle 8 16 true (2)
])
theorem kid23_part901_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part901) = true := by rfl

def kid23_part902 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 8, 17, 64],[2, 32, 64, 1, 16, 25, 64],64⟩,
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 0 29 true (0),
.cycle 1 20 true (1),
.cycle 1 35 true (1),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 10 true (2),
.cycle 0 24 true (0),
.cycle 6 17 true (2),
.cycle 18 2 true (4),
.last 20 (2,true),
.cycle 5 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 8, 17, 64],[2, 32, 64, 1, 16, 17, 64],64⟩,
.cycle 16 8 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 3 27 true (1),
.cycle 8 13 true (2)
])
theorem kid23_part902_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part902) = true := by rfl

def kid23_part903 : Audit := .cycle 11 1 true (5)
theorem kid23_part903_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part903) = true := by rfl

def kid23_part904 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 11 4 true (5),
.cycle 41 3 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 26 (2,true),
.cycle 1 25 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.cycle 7 9 true (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 5 17 true (1),
.cycle 13 2 true (5),
.cycle 60 3 false (10),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3)
])
theorem kid23_part904_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part904) = true := by rfl

def kid23_part905 : Audit := .cycle 7 6 true (3)
theorem kid23_part905_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part905) = true := by rfl

def kid23_part906 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 11 3 true (4),
.last 17 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.cycle 9 5 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.cycle 8 6 true (3)
])
theorem kid23_part906_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part906) = true := by rfl

def kid23_part907 : Audit := .cycle 0 14 true (0)
theorem kid23_part907_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part907) = true := by rfl

def kid23_part908 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 4 16 true (1),
.cycle 39 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 8 true (2),
.cycle 3 15 true (1),
.cycle 4 15 true (1),
.cycle 5 15 true (1),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 9 9 true (2),
.cycle 30 1 false (-2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (2)
])
theorem kid23_part908_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part908) = true := by rfl

def kid23_part909 : Audit := .cycle 31 1 false (7)
theorem kid23_part909_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part909) = true := by rfl

def kid23_part910 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 5 12 true (1),
.last 22 (2,true),
.last 19 (2,true),
.cycle 17 2 false (-1),
.cycle 18 2 false (2),
.cycle 0 18 true (0),
.cycle 47 2 false (9),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 31 2 false (7),
.cycle 31 2 false (7),
.cycle 16 18 true (2),
.last 16 (2,true),
.last 20 (2,true),
.cycle 1 25 true (0),
.cycle 17 2 false (-1),
.cycle 22 2 false (6),
.cycle 0 18 true (0),
.cycle 7 10 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 59 2 false (9),
.cycle 8 10 true (2)
])
theorem kid23_part910_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part910) = true := by rfl

def kid23_part911 : Audit := .cycle 0 12 true (0)
theorem kid23_part911_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part911) = true := by rfl

def kid23_part912 : Audit := .cycle 1 11 true (1)
theorem kid23_part912_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part912) = true := by rfl

def kid23_part913 : Audit := .cycle 2 10 true (1)
theorem kid23_part913_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part913) = true := by rfl

def kid23_part914 : Audit := .cycle 1 14 true (1)
theorem kid23_part914_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part914) = true := by rfl

def kid23_part915 : Audit := .cycle 11 1 true (5)
theorem kid23_part915_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part915) = true := by rfl

def kid23_part916 : Audit := .cycle 8 4 true (3)
theorem kid23_part916_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part916) = true := by rfl

def kid23_part892 : Audit := .split 11 (4,false) (byMove [(kid23_part893),(kid23_part894),(kid23_part895),(kid23_part896),(kid23_part897),(kid23_part898),(kid23_part899),(kid23_part900),(kid23_part901),(kid23_part902),(kid23_part903),(kid23_part904),(kid23_part905),(kid23_part906),(kid23_part907),(kid23_part908),(kid23_part909),(kid23_part910),(kid23_part911),(kid23_part912),(kid23_part913),(kid23_part914),(kid23_part915),(kid23_part916)])

theorem kid23_part892_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part892) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid23_part893),(kid23_part894),(kid23_part895),(kid23_part896),(kid23_part897),(kid23_part898),(kid23_part899),(kid23_part900),(kid23_part901),(kid23_part902),(kid23_part903),(kid23_part904),(kid23_part905),(kid23_part906),(kid23_part907),(kid23_part908),(kid23_part909),(kid23_part910),(kid23_part911),(kid23_part912),(kid23_part913),(kid23_part914),(kid23_part915),(kid23_part916)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part893_checked

  · exact kid23_part899_checked

  · exact kid23_part905_checked

  · exact kid23_part911_checked

  · exact kid23_part894_checked

  · exact kid23_part900_checked

  · exact kid23_part906_checked

  · exact kid23_part912_checked

  · exact kid23_part895_checked

  · exact kid23_part901_checked

  · exact kid23_part907_checked

  · exact kid23_part913_checked

  · exact kid23_part896_checked

  · exact kid23_part902_checked

  · exact kid23_part908_checked

  · exact kid23_part914_checked

  · exact kid23_part897_checked

  · exact kid23_part903_checked

  · exact kid23_part909_checked

  · exact kid23_part915_checked

  · exact kid23_part898_checked

  · exact kid23_part904_checked

  · exact kid23_part910_checked

  · exact kid23_part916_checked

def kid23_part918 : Audit := .cycle 0 11 true (0)
theorem kid23_part918_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part918) = true := by rfl

def kid23_part919 : Audit := .cycle 1 10 true (1)
theorem kid23_part919_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part919) = true := by rfl

def kid23_part920 : Audit := .cycle 2 9 true (1)
theorem kid23_part920_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part920) = true := by rfl

def kid23_part921 : Audit := .cycle 1 13 true (1)
theorem kid23_part921_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part921) = true := by rfl

def kid23_part922 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 10 4 true (3),
.cycle 6 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part922_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part922) = true := by rfl

def kid23_part923 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.cycle 0 38 true (-2),
.last 16 (2,true),
.cycle 27 1 false (-1),
.cycle 18 1 false (0),
.cycle 17 2 false (-1),
.cycle 1 16 true (1),
.cycle 11 6 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 14 3 true (1),
.cycle 19 3 false (1),
.cycle 17 7 false (2),
.last 22 (2,true),
.last 16 (2,true),
.cycle 27 1 false (-1),
.cycle 19 1 false (-1),
.cycle 17 2 false (-1),
.cycle 1 16 true (1),
.cycle 20 9 false (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 14 3 true (1),
.cycle 17 4 false (1)
])
theorem kid23_part923_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part923) = true := by rfl

def kid23_part924 : Audit := .cycle 0 11 true (0)
theorem kid23_part924_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part924) = true := by rfl

def kid23_part925 : Audit := .cycle 1 10 true (1)
theorem kid23_part925_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part925) = true := by rfl

def kid23_part926 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (2),
.cycle 21 8 true (4),
.last 21 (4,false),
.last 22 (4,false),
.cycle 7 15 true (2),
.cycle 23 8 true (5),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 21 (4,false),
.last 26 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 35 8 true (8)
])
theorem kid23_part926_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part926) = true := by rfl

def kid23_part927 : Audit := .cycle 3 15 true (1)
theorem kid23_part927_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part927) = true := by rfl

def kid23_part928 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 19 true (1),
.cycle 3 9 true (1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 41 (2,true),
.cycle 0 24 true (0),
.cycle 11 1 true (5),
.cycle 10 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 15 true (1),
.cycle 32 1 false (6),
.cycle 31 2 false (7),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part928_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part928) = true := by rfl

def kid23_part929 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 22 (2,true),
.last 17 (2,true),
.cycle 20 1 false (0),
.cycle 21 2 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.cycle 10 3 true (4),
.cycle 14 5 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 5 15 true (1),
.cycle 32 1 false (6),
.cycle 31 2 false (7),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.cycle 10 3 true (4)
])
theorem kid23_part929_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part929) = true := by rfl

def kid23_part930 : Audit := .cycle 7 5 true (3)
theorem kid23_part930_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part930) = true := by rfl

def kid23_part931 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 13 2 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 2 true (5),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 13 2 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 13 2 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
])
theorem kid23_part931_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part931) = true := by rfl

def kid23_part932 : Audit := .cycle 0 13 true (0)
theorem kid23_part932_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part932) = true := by rfl

def kid23_part933 : Audit := .cycle 4 7 true (1)
theorem kid23_part933_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part933) = true := by rfl

def kid23_part934 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 18 1 false (0),
.cycle 15 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 3 true (3),
.cycle 10 2 true (3),
.cycle 9 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 18 1 false (0),
.cycle 15 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 3 true (3),
.cycle 9 4 true (3)
])
theorem kid23_part934_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part934) = true := by rfl

def kid23_part935 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.cycle 13 16 false (3),
.last 16 (2,true),
.cycle 24 1 false (-2),
.cycle 18 1 false (0),
.cycle 17 2 false (-1),
.cycle 23 7 false (2),
.cycle 21 5 false (1),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 12 4 true (1),
.cycle 19 3 false (1),
.cycle 17 7 false (2),
.last 22 (2,true),
.last 16 (2,true),
.cycle 24 1 false (-2),
.cycle 19 1 false (-1),
.cycle 17 2 false (-1),
.cycle 19 8 false (3),
.cycle 18 6 false (2),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 19 7 false (2),
.cycle 17 4 false (1)
])
theorem kid23_part935_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part935) = true := by rfl

def kid23_part936 : Audit := .cycle 0 11 true (0)
theorem kid23_part936_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part936) = true := by rfl

def kid23_part937 : Audit := .cycle 1 10 true (1)
theorem kid23_part937_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part937) = true := by rfl

def kid23_part938 : Audit := .cycle 2 9 true (1)
theorem kid23_part938_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part938) = true := by rfl

def kid23_part939 : Audit := .cycle 1 13 true (1)
theorem kid23_part939_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part939) = true := by rfl

def kid23_part940 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 22 1 false (0),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 4 true (4),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.cycle 9 8 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part940_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part940) = true := by rfl

def kid23_part941 : Audit := .cycle 8 3 true (3)
theorem kid23_part941_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part941) = true := by rfl

def kid23_part917 : Audit := .split 10 (5,true) (byMove [(kid23_part918),(kid23_part919),(kid23_part920),(kid23_part921),(kid23_part922),(kid23_part923),(kid23_part924),(kid23_part925),(kid23_part926),(kid23_part927),(kid23_part928),(kid23_part929),(kid23_part930),(kid23_part931),(kid23_part932),(kid23_part933),(kid23_part934),(kid23_part935),(kid23_part936),(kid23_part937),(kid23_part938),(kid23_part939),(kid23_part940),(kid23_part941)])

theorem kid23_part917_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part917) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid23_part918),(kid23_part919),(kid23_part920),(kid23_part921),(kid23_part922),(kid23_part923),(kid23_part924),(kid23_part925),(kid23_part926),(kid23_part927),(kid23_part928),(kid23_part929),(kid23_part930),(kid23_part931),(kid23_part932),(kid23_part933),(kid23_part934),(kid23_part935),(kid23_part936),(kid23_part937),(kid23_part938),(kid23_part939),(kid23_part940),(kid23_part941)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part918_checked

  · exact kid23_part924_checked

  · exact kid23_part930_checked

  · exact kid23_part936_checked

  · exact kid23_part919_checked

  · exact kid23_part925_checked

  · exact kid23_part931_checked

  · exact kid23_part937_checked

  · exact kid23_part920_checked

  · exact kid23_part926_checked

  · exact kid23_part932_checked

  · exact kid23_part938_checked

  · exact kid23_part921_checked

  · exact kid23_part927_checked

  · exact kid23_part933_checked

  · exact kid23_part939_checked

  · exact kid23_part922_checked

  · exact kid23_part928_checked

  · exact kid23_part934_checked

  · exact kid23_part940_checked

  · exact kid23_part923_checked

  · exact kid23_part929_checked

  · exact kid23_part935_checked

  · exact kid23_part941_checked

def kid23_part943 : Audit := .cycle 1 13 true (1)
theorem kid23_part943_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part943) = true := by rfl

def kid23_part944 : Audit := .cycle 7 6 true (2)
theorem kid23_part944_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part944) = true := by rfl

def kid23_part945 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 25 9 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 9 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 8 true (2),
.cycle 21 5 false (1),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.cycle 21 5 false (2),
.cycle 25 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 8 6 true (2)
])
theorem kid23_part945_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part945) = true := by rfl

def kid23_part946 : Audit := .cycle 0 14 true (0)
theorem kid23_part946_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part946) = true := by rfl

def kid23_part947 : Audit := .cycle 6 8 true (2)
theorem kid23_part947_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part947) = true := by rfl

def kid23_part948 : Audit := .split 23 (4,false) (byMove [
.last 26 (2,true),
.cycle 11 34 false (4),
.cycle 25 1 false (-3),
.cycle 24 1 false (-4),
.cycle 23 1 false (-3),
.cycle 22 2 false (-2),
.cycle 1 24 false (4),
.cycle 15 10 false (1),
.last 24 (2,true),
.cycle 0 25 false (4),
.cycle 18 12 false (1),
.cycle 21 3 false (-1),
.cycle 17 7 false (1),
.last 25 (2,true),
.cycle 1 26 false (4),
.cycle 24 1 false (-4),
.cycle 23 1 false (-3),
.cycle 22 2 false (-2),
.cycle 18 24 false (2),
.cycle 18 10 false (1),
.last 24 (2,true),
.cycle 19 26 false (3),
.cycle 18 12 false (1),
.cycle 20 4 false (0)
])
theorem kid23_part948_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part948) = true := by rfl

def kid23_part949 : Audit := .cycle 0 13 true (0)
theorem kid23_part949_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part949) = true := by rfl

def kid23_part950 : Audit := .cycle 1 12 true (1)
theorem kid23_part950_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part950) = true := by rfl

def kid23_part951 : Audit := .cycle 10 8 true (2)
theorem kid23_part951_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part951) = true := by rfl

def kid23_part952 : Audit := .cycle 3 10 true (1)
theorem kid23_part952_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part952) = true := by rfl

def kid23_part953 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 6 10 true (2),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 18 true (2),
.cycle 10 8 true (2),
.cycle 13 1 true (5),
.cycle 12 4 true (4),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 7 14 true (2),
.cycle 7 14 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 6 true (3)
])
theorem kid23_part953_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part953) = true := by rfl

def kid23_part954 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 0 27 true (0),
.last 15 (2,true),
.cycle 7 10 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 32 2 false (0),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 10 true (2),
.cycle 12 3 true (4),
.cycle 10 5 true (2),
.last 21 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 82 2 false (10),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 10 true (2),
.cycle 12 3 true (4)
])
theorem kid23_part954_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part954) = true := by rfl

def kid23_part955 : Audit := .cycle 6 7 true (2)
theorem kid23_part955_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part955) = true := by rfl

def kid23_part956 : Audit := .cycle 11 2 true (3)
theorem kid23_part956_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part956) = true := by rfl

def kid23_part957 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 25 7 false (2),
.cycle 29 1 false (1),
.cycle 7 9 true (2),
.cycle 25 9 false (2),
.cycle 7 11 true (1),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 2048, 1, 128, 2048, 4, 1, 2048, 4, 4096],5168⟩,
.cycle 0 15 true (0),
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.cycle 10 4 true (2),
.cycle 21 5 false (1),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 21 5 false (2),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 6 9 true (2),
.cycle 12 2 true (3)
])
theorem kid23_part957_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part957) = true := by rfl

def kid23_part958 : Audit := .cycle 1 14 true (1)
theorem kid23_part958_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part958) = true := by rfl

def kid23_part959 : Audit := .cycle 9 4 true (2)
theorem kid23_part959_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part959) = true := by rfl

def kid23_part960 : Audit := .split 23 (4,false) (byMove [
.last 26 (2,true),
.cycle 15 20 false (1),
.cycle 25 1 false (-3),
.cycle 24 1 false (-4),
.cycle 23 1 false (-3),
.cycle 22 2 false (-2),
.cycle 18 7 false (1),
.cycle 20 5 false (0),
.last 24 (2,true),
.cycle 18 8 true (-3),
.cycle 16 8 false (1),
.cycle 21 3 false (-1),
.cycle 17 7 false (1),
.last 25 (2,true),
.cycle 18 9 false (1),
.cycle 24 1 false (-4),
.cycle 23 1 false (-3),
.cycle 22 2 false (-2),
.cycle 19 8 false (1),
.cycle 18 6 false (1),
.last 24 (2,true),
.cycle 10 15 false (4),
.cycle 18 8 false (1),
.cycle 20 4 false (0)
])
theorem kid23_part960_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part960) = true := by rfl

def kid23_part961 : Audit := .cycle 0 13 true (0)
theorem kid23_part961_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part961) = true := by rfl

def kid23_part962 : Audit := .cycle 1 12 true (1)
theorem kid23_part962_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part962) = true := by rfl

def kid23_part963 : Audit := .cycle 2 11 true (1)
theorem kid23_part963_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part963) = true := by rfl

def kid23_part964 : Audit := .cycle 1 15 true (1)
theorem kid23_part964_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part964) = true := by rfl

def kid23_part965 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 6 9 true (2),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 9 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 12 4 true (4),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 9 5 true (2),
.cycle 6 10 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2)
])
theorem kid23_part965_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part965) = true := by rfl

def kid23_part966 : Audit := .cycle 8 5 true (2)
theorem kid23_part966_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part966) = true := by rfl

def kid23_part942 : Audit := .split 12 (5,true) (byMove [(kid23_part943),(kid23_part944),(kid23_part945),(kid23_part946),(kid23_part947),(kid23_part948),(kid23_part949),(kid23_part950),(kid23_part951),(kid23_part952),(kid23_part953),(kid23_part954),(kid23_part955),(kid23_part956),(kid23_part957),(kid23_part958),(kid23_part959),(kid23_part960),(kid23_part961),(kid23_part962),(kid23_part963),(kid23_part964),(kid23_part965),(kid23_part966)])

theorem kid23_part942_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part942) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (5,true) (some mv)) (byMove [(kid23_part943),(kid23_part944),(kid23_part945),(kid23_part946),(kid23_part947),(kid23_part948),(kid23_part949),(kid23_part950),(kid23_part951),(kid23_part952),(kid23_part953),(kid23_part954),(kid23_part955),(kid23_part956),(kid23_part957),(kid23_part958),(kid23_part959),(kid23_part960),(kid23_part961),(kid23_part962),(kid23_part963),(kid23_part964),(kid23_part965),(kid23_part966)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part943_checked

  · exact kid23_part949_checked

  · exact kid23_part955_checked

  · exact kid23_part961_checked

  · exact kid23_part944_checked

  · exact kid23_part950_checked

  · exact kid23_part956_checked

  · exact kid23_part962_checked

  · exact kid23_part945_checked

  · exact kid23_part951_checked

  · exact kid23_part957_checked

  · exact kid23_part963_checked

  · exact kid23_part946_checked

  · exact kid23_part952_checked

  · exact kid23_part958_checked

  · exact kid23_part964_checked

  · exact kid23_part947_checked

  · exact kid23_part953_checked

  · exact kid23_part959_checked

  · exact kid23_part965_checked

  · exact kid23_part948_checked

  · exact kid23_part954_checked

  · exact kid23_part960_checked

  · exact kid23_part966_checked

def kid23_part968 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 1 23 true (1),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 6 9 true (2),
.cycle 1 17 true (1),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 9 6 true (2),
.cycle 11 4 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (2)
])
theorem kid23_part968_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part968) = true := by rfl

def kid23_part969 : Audit := .split 16 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 22 5 false (1),
.cycle 20 1 false (0),
.cycle 7 14 true (1),
.cycle 22 3 false (0),
.cycle 17 19 false (1),
.cycle 6 11 true (1),
.cycle 19 5 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 8, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 1 18 true (1),
.last 23 (4,false),
.cycle 0 21 true (0),
.cycle 23 13 false (2),
.cycle 22 7 false (1),
.cycle 17 16 true (-1),
.cycle 7 14 true (1),
.cycle 22 3 false (0),
.cycle 47 15 true (0),
.cycle 21 23 false (4),
.cycle 22 17 false (3),
.cycle 2 17 true (1),
.cycle 1 18 true (1),
.cycle 22 13 false (2),
.cycle 22 11 false (2)
])
theorem kid23_part969_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part969) = true := by rfl

def kid23_part970 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 41 5 false (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 19 1 false (-1),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.last 13 (4,false),
.last 14 (4,false),
.cycle 21 7 false (2),
.cycle 17 5 false (1),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 19 1 false (-1),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 22 11 false (2)
])
theorem kid23_part970_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part970) = true := by rfl

def kid23_part971 : Audit := .cycle 7 7 true (2)
theorem kid23_part971_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part971) = true := by rfl

def kid23_part972 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 7 9 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 3 24 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 21 9 false (1),
.cycle 18 5 false (1),
.cycle 1 50 true (-1),
.cycle 1 20 true (1),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 75 39 false (5),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 19 7 false (1)
])
theorem kid23_part972_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part972) = true := by rfl

def kid23_part973 : Audit := .split 16 (2,true) (byMove [
.last 37 (4,false),
.cycle 13 5 false (1),
.cycle 19 1 false (-1),
.last 26 (4,false),
.cycle 14 3 false (0),
.last 19 (4,false),
.cycle 0 21 true (-1),
.last 37 (4,false),
.last 30 (4,false),
.cycle 3 18 true (-1),
.last 20 (4,false),
.cycle 12 5 false (2),
.last 23 (4,false),
.last 21 (4,false),
.last 28 (4,false),
.last 26 (4,false),
.cycle 14 3 false (0),
.last 19 (4,false),
.cycle 0 21 true (-1),
.last 25 (4,false),
.last 33 (4,false),
.cycle 1 23 true (-1),
.last 23 (4,false),
.last 21 (4,false)
])
theorem kid23_part973_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part973) = true := by rfl

def kid23_part974 : Audit := .cycle 1 12 true (1)
theorem kid23_part974_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part974) = true := by rfl

def kid23_part975 : Audit := .split 16 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 1 23 true (1),
.cycle 37 1 false (1),
.cycle 7 12 true (2),
.cycle 1 27 true (1),
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.cycle 12 5 true (3),
.cycle 10 15 true (2),
.cycle 0 18 true (0),
.last 20 (4,false),
.cycle 1 17 true (1),
.cycle 1 19 true (1),
.cycle 10 7 true (2),
.cycle 1 23 true (1),
.cycle 5 12 true (1),
.cycle 1 21 true (1),
.cycle 1 19 true (1),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 1 19 true (1),
.cycle 1 17 true (1)
])
theorem kid23_part975_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part975) = true := by rfl

def kid23_part976 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 0 20 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (2),
.cycle 13 8 true (2),
.last 13 (4,false),
.last 14 (4,false),
.cycle 7 7 true (2),
.cycle 15 8 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 26 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 17 8 true (4)
])
theorem kid23_part976_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part976) = true := by rfl

def kid23_part977 : Audit := .cycle 0 13 true (0)
theorem kid23_part977_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part977) = true := by rfl

def kid23_part978 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 18 (4,false),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (4,false),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 6 9 true (2),
.last 17 (4,false),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 9 6 true (2),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 8 7 true (2)
])
theorem kid23_part978_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part978) = true := by rfl

def kid23_part979 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.last 24 (2,true),
.last 19 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.cycle 1 15 true (1),
.last 19 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 17 (2,true),
.cycle 12 3 true (4),
.cycle 16 5 true (4),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 5 17 true (1),
.last 18 (2,true),
.last 18 (2,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 5 true (4),
.cycle 12 3 true (4)
])
theorem kid23_part979_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part979) = true := by rfl

def kid23_part980 : Audit := .cycle 6 9 true (2)
theorem kid23_part980_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part980) = true := by rfl

def kid23_part981 : Audit := .cycle 10 2 true (2)
theorem kid23_part981_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part981) = true := by rfl

def kid23_part982 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.cycle 7 13 true (0),
.last 13 (4,false),
.last 28 (4,false),
.cycle 6 7 true (2),
.cycle 15 5 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 1, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 1 14 true (1),
.last 19 (4,false),
.cycle 1 16 true (1),
.cycle 14 4 true (1),
.cycle 17 5 false (1),
.cycle 5 9 true (1),
.cycle 32 1 false (2),
.last 13 (4,false),
.last 49 (4,false),
.cycle 6 7 true (2),
.cycle 7 9 true (2),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
])
theorem kid23_part982_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part982) = true := by rfl

def kid23_part983 : Audit := .cycle 5 7 true (1)
theorem kid23_part983_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part983) = true := by rfl

def kid23_part984 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 9 10 true (1),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 6 9 true (1),
.cycle 17 5 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 4, 4096, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 1 16 true (1),
.last 21 (4,false),
.last 16 (4,false),
.cycle 19 9 false (2),
.cycle 18 5 false (1),
.cycle 15 12 true (-1),
.cycle 9 10 true (1),
.cycle 18 3 false (0),
.last 20 (4,false),
.cycle 19 15 false (4),
.cycle 18 11 false (3),
.cycle 2 15 true (1),
.cycle 1 16 true (1),
.cycle 18 9 false (2),
.cycle 18 7 false (2)
])
theorem kid23_part984_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part984) = true := by rfl

def kid23_part985 : Audit := .split 16 (2,true) (byMove [
.last 51 (4,false),
.cycle 13 5 false (1),
.cycle 19 1 false (-1),
.last 24 (4,false),
.cycle 14 3 false (0),
.last 19 (4,false),
.cycle 11 9 false (3),
.cycle 10 7 false (3),
.last 36 (4,false),
.last 24 (4,false),
.last 29 (4,false),
.cycle 12 5 false (2),
.last 23 (4,false),
.last 21 (4,false),
.last 26 (4,false),
.last 24 (4,false),
.cycle 14 3 false (0),
.last 19 (4,false),
.last 25 (4,false),
.last 23 (4,false),
.last 41 (4,false),
.last 29 (4,false),
.last 23 (4,false),
.last 21 (4,false)
])
theorem kid23_part985_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part985) = true := by rfl

def kid23_part986 : Audit := .cycle 1 12 true (1)
theorem kid23_part986_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part986) = true := by rfl

def kid23_part987 : Audit := .cycle 7 5 true (2)
theorem kid23_part987_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part987) = true := by rfl

def kid23_part988 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 2 14 true (1),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 19 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part988_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part988) = true := by rfl

def kid23_part989 : Audit := .cycle 0 13 true (0)
theorem kid23_part989_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part989) = true := by rfl

def kid23_part990 : Audit := .split 15 (4,false) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 12 4 true (3),
.cycle 14 2 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 9 true (3),
.cycle 3 13 true (1),
.cycle 15 1 true (5),
.cycle 14 4 true (4),
.cycle 6 10 true (2),
.cycle 13 3 true (3),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 9 7 true (2),
.cycle 11 5 true (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 15 1 true (5),
.cycle 8 8 true (2)
])
theorem kid23_part990_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part990) = true := by rfl

def kid23_part991 : Audit := .cycle 8 5 true (2)
theorem kid23_part991_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part991) = true := by rfl

def kid23_part967 : Audit := .split 11 (5,true) (byMove [(kid23_part968),(kid23_part969),(kid23_part970),(kid23_part971),(kid23_part972),(kid23_part973),(kid23_part974),(kid23_part975),(kid23_part976),(kid23_part977),(kid23_part978),(kid23_part979),(kid23_part980),(kid23_part981),(kid23_part982),(kid23_part983),(kid23_part984),(kid23_part985),(kid23_part986),(kid23_part987),(kid23_part988),(kid23_part989),(kid23_part990),(kid23_part991)])

theorem kid23_part967_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part967) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (5,true) (some mv)) (byMove [(kid23_part968),(kid23_part969),(kid23_part970),(kid23_part971),(kid23_part972),(kid23_part973),(kid23_part974),(kid23_part975),(kid23_part976),(kid23_part977),(kid23_part978),(kid23_part979),(kid23_part980),(kid23_part981),(kid23_part982),(kid23_part983),(kid23_part984),(kid23_part985),(kid23_part986),(kid23_part987),(kid23_part988),(kid23_part989),(kid23_part990),(kid23_part991)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part968_checked

  · exact kid23_part974_checked

  · exact kid23_part980_checked

  · exact kid23_part986_checked

  · exact kid23_part969_checked

  · exact kid23_part975_checked

  · exact kid23_part981_checked

  · exact kid23_part987_checked

  · exact kid23_part970_checked

  · exact kid23_part976_checked

  · exact kid23_part982_checked

  · exact kid23_part988_checked

  · exact kid23_part971_checked

  · exact kid23_part977_checked

  · exact kid23_part983_checked

  · exact kid23_part989_checked

  · exact kid23_part972_checked

  · exact kid23_part978_checked

  · exact kid23_part984_checked

  · exact kid23_part990_checked

  · exact kid23_part973_checked

  · exact kid23_part979_checked

  · exact kid23_part985_checked

  · exact kid23_part991_checked

def kid23_part993 : Audit := .cycle 1 17 true (1)
theorem kid23_part993_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part993) = true := by rfl

def kid23_part994 : Audit := .cycle 1 14 true (1)
theorem kid23_part994_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part994) = true := by rfl

def kid23_part995 : Audit := .split 17 (5,true) (byMove [
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 7 13 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 1 18 true (0),
.cycle 1 23 true (0),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,false),
.cycle 29 1 false (1),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 5 13 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 1 18 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 19 true (0),
.cycle 23 1 false (1),
.cycle 25 1 false (1)
])
theorem kid23_part995_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part995) = true := by rfl

def kid23_part996 : Audit := .cycle 7 11 true (0)
theorem kid23_part996_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part996) = true := by rfl

def kid23_part997 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.last 30 (5,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 7 11 true (1),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 1 16 true (1),
.last 14 (5,true),
.cycle 13 6 false (2),
.last 13 (5,true),
.last 26 (5,true),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 22 5 false (2),
.cycle 1 14 true (1),
.last 16 (5,true),
.last 38 (5,true),
.last 22 (5,true)
])
theorem kid23_part997_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part997) = true := by rfl

def kid23_part998 : Audit := .split 18 (5,true) (byMove [
.cycle 0 23 true (-1),
.cycle 1 33 true (-1),
.last 21 (4,false),
.cycle 0 25 true (-1),
.cycle 0 29 true (-1),
.last 21 (4,false),
.cycle 7 13 true (-1),
.last 33 (4,false),
.cycle 0 21 true (-1),
.cycle 3 22 true (-1),
.last 19 (4,false),
.last 20 (4,false),
.last 25 (4,false),
.cycle 18 2 true (1),
.last 21 (4,false),
.cycle 1 25 true (-1),
.cycle 1 29 true (-1),
.last 21 (4,false),
.cycle 24 21 true (2),
.cycle 1 45 true (-1),
.cycle 0 21 true (-1),
.cycle 4 15 true (-1),
.last 19 (4,false),
.last 23 (4,false)
])
theorem kid23_part998_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part998) = true := by rfl

def kid23_part999 : Audit := .cycle 6 5 true (2)
theorem kid23_part999_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part999) = true := by rfl

def kid23_part1000 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 1 18 true (1),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 1 19 true (1),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part1000_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part1000) = true := by rfl

def kid23_part1001 : Audit := .split 23 (5,true) (byMove [
.cycle 1 63 true (0),
.cycle 34 1 false (8),
.cycle 0 56 true (0),
.cycle 7 23 true (0),
.cycle 37 1 false (9),
.last 27 (4,false),
.cycle 0 27 true (0),
.cycle 1 31 true (0),
.cycle 10 14 true (0),
.cycle 3 45 true (0),
.last 52 (4,false),
.last 28 (4,false),
.cycle 24 23 true (2),
.cycle 22 2 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 132, 4096],[128, 2048, 4, 1, 1, 1, 128, 2048, 4, 1, 4, 4, 4096],5168⟩,
.cycle 5 23 true (0),
.cycle 32 1 false (8),
.last 27 (4,false),
.cycle 0 27 true (0),
.cycle 1 43 true (0),
.cycle 2 55 true (0),
.cycle 5 19 true (0),
.cycle 10 16 true (0),
.cycle 24 17 true (4)
])
theorem kid23_part1001_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part1001) = true := by rfl

def kid23_part1002 : Audit := .cycle 1 12 true (1)
theorem kid23_part1002_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part1002) = true := by rfl

def kid23_part1003 : Audit := .cycle 1 14 true (1)
theorem kid23_part1003_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part1003) = true := by rfl

def kid23_part1004 : Audit := .split 11 (5,true) (byMove [
.last 16 (4,false),
.cycle 0 15 true (0),
.last 22 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 14 (4,false),
.cycle 6 9 true (2),
.last 18 (4,false),
.cycle 1 14 true (1),
.cycle 5 13 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part1004_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part1004) = true := by rfl

def kid23_part1005 : Audit := .split 13 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 19 7 false (2),
.cycle 21 9 false (2),
.cycle 7 9 true (1),
.cycle 17 5 false (2),
.last 18 (4,false),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.cycle 12 9 true (2),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.last 16 (4,false),
.cycle 12 11 true (2),
.cycle 12 2 true (2),
.cycle 12 4 true (1),
.cycle 5 9 true (1),
.cycle 17 5 false (2),
.last 18 (4,false),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 12 9 true (2),
.cycle 0 15 true (0),
.last 19 (4,false),
.cycle 12 7 true (2)
])
theorem kid23_part1005_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part1005) = true := by rfl

def kid23_part1006 : Audit := .split 14 (5,true) (byMove [
.cycle 1 25 true (1),
.cycle 13 16 true (-2),
.cycle 15 5 false (1),
.cycle 0 20 true (0),
.cycle 13 24 true (-2),
.last 18 (4,false),
.cycle 6 9 true (1),
.cycle 1 16 true (1),
.cycle 23 8 true (3),
.cycle 1 16 true (1),
.cycle 1 18 true (1),
.last 18 (4,false),
.cycle 12 13 true (1),
.cycle 13 2 true (1),
.cycle 15 5 false (1),
.cycle 1 20 true (1),
.cycle 13 12 true (-2),
.last 18 (4,false),
.cycle 12 7 true (1),
.cycle 1 16 true (1),
.cycle 2 19 true (1),
.cycle 1 16 true (1),
.cycle 12 4 true (1),
.cycle 12 7 true (1)
])
theorem kid23_part1006_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part1006) = true := by rfl

def kid23_part1007 : Audit := .cycle 5 7 true (1)
theorem kid23_part1007_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part1007) = true := by rfl

def kid23_part1008 : Audit := .split 15 (5,true) (byMove [
.cycle 1 20 true (0),
.cycle 20 1 false (0),
.cycle 1 22 true (0),
.cycle 7 11 true (0),
.cycle 18 1 false (0),
.last 19 (4,false),
.cycle 1 16 true (0),
.cycle 1 21 true (0),
.cycle 4 13 true (0),
.cycle 0 17 true (0),
.cycle 0 19 true (0),
.last 18 (4,false),
.cycle 16 9 true (2),
.cycle 14 2 true (2),
.cycle 28 1 false (2),
.cycle 5 11 true (0),
.cycle 18 1 false (0),
.last 19 (4,false),
.cycle 1 16 true (0),
.cycle 1 23 true (0),
.cycle 1 18 true (0),
.cycle 0 17 true (0),
.cycle 5 13 true (0),
.cycle 16 7 true (2)
])
theorem kid23_part1008_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part1008) = true := by rfl

def kid23_part1009 : Audit := .split 11 (4,false) (byMove [
.cycle 13 6 false (2),
.last 19 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.last 17 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 10 2 true (1),
.cycle 5 7 true (1),
.cycle 5 9 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 22 (5,true),
.cycle 5 7 true (1),
.last 19 (5,true),
.last 12 (5,true)
])
theorem kid23_part1009_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part1009) = true := by rfl

def kid23_part1010 : Audit := .split 17 (5,true) (byMove [
.cycle 17 4 true (2),
.last 23 (4,false),
.cycle 21 1 false (1),
.cycle 7 13 true (-1),
.last 21 (4,false),
.last 21 (4,false),
.cycle 1 18 true (-1),
.cycle 1 23 true (-1),
.last 23 (4,false),
.cycle 0 19 true (-1),
.cycle 0 21 true (-1),
.last 20 (4,false),
.cycle 15 15 true (1),
.cycle 16 2 true (2),
.last 35 (4,false),
.cycle 5 13 true (-1),
.last 21 (4,false),
.last 21 (4,false),
.cycle 19 21 true (2),
.cycle 16 7 true (2),
.cycle 17 2 true (3),
.cycle 0 19 true (-1),
.last 27 (4,false),
.cycle 17 7 true (2)
])
theorem kid23_part1010_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part1010) = true := by rfl

def kid23_part1011 : Audit := .cycle 6 5 true (2)
theorem kid23_part1011_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part1011) = true := by rfl

def kid23_part1012 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 7 8 true (2),
.cycle 1 19 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.last 25 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part1012_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part1012) = true := by rfl

def kid23_part1013 : Audit := .cycle 2 11 true (1)
theorem kid23_part1013_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part1013) = true := by rfl

def kid23_part1014 : Audit := .cycle 1 12 true (1)
theorem kid23_part1014_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part1014) = true := by rfl

def kid23_part1015 : Audit := .cycle 9 2 true (2)
theorem kid23_part1015_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part1015) = true := by rfl

def kid23_part1016 : Audit := .split 11 (5,true) (byMove [
.cycle 8 7 true (2),
.cycle 5 11 true (1),
.cycle 5 11 true (1),
.cycle 7 7 true (2),
.cycle 7 9 true (1),
.cycle 0 21 true (-1),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 14 (4,false),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.cycle 10 2 true (2),
.cycle 5 7 true (1),
.cycle 5 9 true (1),
.last 23 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part1016_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part1016) = true := by rfl

def kid23_part992 : Audit := .split 10 (2,true) (byMove [(kid23_part993),(kid23_part994),(kid23_part995),(kid23_part996),(kid23_part997),(kid23_part998),(kid23_part999),(kid23_part1000),(kid23_part1001),(kid23_part1002),(kid23_part1003),(kid23_part1004),(kid23_part1005),(kid23_part1006),(kid23_part1007),(kid23_part1008),(kid23_part1009),(kid23_part1010),(kid23_part1011),(kid23_part1012),(kid23_part1013),(kid23_part1014),(kid23_part1015),(kid23_part1016)])

theorem kid23_part992_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part992) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part993),(kid23_part994),(kid23_part995),(kid23_part996),(kid23_part997),(kid23_part998),(kid23_part999),(kid23_part1000),(kid23_part1001),(kid23_part1002),(kid23_part1003),(kid23_part1004),(kid23_part1005),(kid23_part1006),(kid23_part1007),(kid23_part1008),(kid23_part1009),(kid23_part1010),(kid23_part1011),(kid23_part1012),(kid23_part1013),(kid23_part1014),(kid23_part1015),(kid23_part1016)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part993_checked

  · exact kid23_part999_checked

  · exact kid23_part1005_checked

  · exact kid23_part1011_checked

  · exact kid23_part994_checked

  · exact kid23_part1000_checked

  · exact kid23_part1006_checked

  · exact kid23_part1012_checked

  · exact kid23_part995_checked

  · exact kid23_part1001_checked

  · exact kid23_part1007_checked

  · exact kid23_part1013_checked

  · exact kid23_part996_checked

  · exact kid23_part1002_checked

  · exact kid23_part1008_checked

  · exact kid23_part1014_checked

  · exact kid23_part997_checked

  · exact kid23_part1003_checked

  · exact kid23_part1009_checked

  · exact kid23_part1015_checked

  · exact kid23_part998_checked

  · exact kid23_part1004_checked

  · exact kid23_part1010_checked

  · exact kid23_part1016_checked

def kid23_part1017 : Audit := .cycle 5 5 true (1)
theorem kid23_part1017_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part1017) = true := by rfl

def kid23_part1019 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.last 18 (5,true),
.cycle 13 6 false (2),
.last 15 (5,true),
.cycle 6 9 true (0),
.last 16 (5,true),
.last 26 (5,true),
.cycle 1 16 true (0),
.cycle 0 26 true (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 21 (5,true),
.last 18 (5,true),
.cycle 13 6 false (2),
.last 15 (5,true),
.last 29 (5,true),
.last 16 (5,true),
.cycle 2 15 true (0),
.cycle 1 16 true (0),
.cycle 13 8 false (3),
.last 15 (5,true)
])
theorem kid23_part1019_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part1019) = true := by rfl

def kid23_part1020 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 33 9 true (0),
.last 22 (2,true),
.cycle 7 17 true (-2),
.last 30 (2,true),
.cycle 14 58 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 43, 35, 64],[2, 32, 64, 1, 35, 1, 64],64⟩,
.cycle 14 15 true (-2),
.last 22 (2,true),
.cycle 0 23 true (-2),
.cycle 14 49 true (-2),
.cycle 0 28 true (-2),
.cycle 14 17 true (-2),
.cycle 20 2 true (2),
.last 22 (2,true),
.cycle 5 17 true (-2),
.cycle 31 9 true (0),
.cycle 11 14 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 43, 35, 64],[2, 32, 64, 1, 35, 1, 64],64⟩,
.cycle 14 13 true (-2),
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 43, 43, 43, 64],[2, 32, 64, 1, 43, 8, 64],64⟩,
.cycle 23 13 true (-1),
.cycle 14 13 true (-2)
])
theorem kid23_part1020_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part1020) = true := by rfl

def kid23_part1021 : Audit := .split 12 (2,true) (byMove [
.last 29 (5,true),
.last 20 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 15 (5,true),
.last 16 (5,true),
.cycle 22 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 20 1 false (-2),
.last 16 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 15 (5,true),
.last 16 (5,true),
.last 27 (5,true),
.last 17 (5,true),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
])
theorem kid23_part1021_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part1021) = true := by rfl

def kid23_part1022 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 21 1 false (-1),
.last 16 (2,true),
.cycle 7 11 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 1 16 true (0),
.last 39 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 13 true (0),
.last 23 (2,true),
.cycle 27 1 false (-1),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 5 11 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 1 16 true (0),
.cycle 23 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1)
])
theorem kid23_part1022_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part1022) = true := by rfl

def kid23_part1023 : Audit := .cycle 13 1 false (-1)
theorem kid23_part1023_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part1023) = true := by rfl

def kid23_part1024 : Audit := .split 12 (5,true) (byMove [
.cycle 26 2 false (-2),
.cycle 25 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 20 2 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 23 2 false (-1),
.cycle 0 19 true (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid23_part1024_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part1024) = true := by rfl

def kid23_part1025 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 12 true (1),
.cycle 1 33 false (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 8 true (2),
.cycle 3 12 true (1),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 34, 64],[2, 32, 64, 1, 34, 32, 64],64⟩,
.cycle 13 2 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 9 6 true (1),
.cycle 19 7 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 34, 64],[2, 32, 64, 1, 34, 32, 64],64⟩
])
theorem kid23_part1025_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part1025) = true := by rfl

def kid23_part1026 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 10 6 true (1),
.last 14 (2,true),
.cycle 7 9 true (1),
.cycle 10 8 true (1),
.cycle 15 9 false (1),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 22 true (1),
.cycle 14 8 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.cycle 17 5 false (1),
.cycle 1 14 true (1),
.cycle 1 23 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 9 6 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part1026_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part1026) = true := by rfl

def kid23_part1027 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.last 19 (5,true),
.cycle 7 13 true (0),
.cycle 1 16 true (1),
.cycle 15 3 false (0),
.cycle 6 7 true (1),
.last 14 (5,true),
.last 25 (5,true),
.cycle 1 14 true (1),
.last 31 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 11 2 true (1),
.cycle 15 3 false (0),
.last 23 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (1),
.last 13 (5,true)
])
theorem kid23_part1027_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part1027) = true := by rfl

def kid23_part1028 : Audit := .cycle 5 7 true (1)
theorem kid23_part1028_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part1028) = true := by rfl

def kid23_part1029 : Audit := .cycle 10 2 true (1)
theorem kid23_part1029_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part1029) = true := by rfl

def kid23_part1030 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.last 20 (2,true),
.last 17 (2,true),
.cycle 11 4 true (1),
.cycle 15 3 false (0),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 17 4 true (3),
.cycle 14 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 5 13 true (0),
.cycle 11 2 true (1),
.cycle 15 3 false (0),
.cycle 0 24 true (0),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 4 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part1030_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part1030) = true := by rfl

def kid23_part1031 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 13 8 false (2),
.last 15 (2,true),
.cycle 0 20 true (0),
.cycle 13 6 false (2),
.cycle 13 7 false (2),
.cycle 6 9 true (0),
.cycle 13 16 true (1),
.last 15 (2,true),
.cycle 1 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 20 5 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 13 2 true (1),
.last 15 (2,true),
.cycle 1 20 true (0),
.cycle 13 6 false (2),
.cycle 13 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 32, 35, 64],[2, 32, 64, 1, 35, 1, 64],64⟩,
.cycle 1 16 true (0),
.last 15 (2,true),
.cycle 1 16 true (0),
.cycle 13 8 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part1031_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part1031) = true := by rfl

def kid23_part1032 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.last 19 (2,true),
.last 14 (2,true),
.cycle 7 13 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 0 17 true (0),
.last 36 (2,true),
.last 14 (2,true),
.last 22 (2,true),
.cycle 10 4 true (0),
.last 20 (2,true),
.last 33 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.cycle 5 13 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 0 17 true (0),
.last 25 (2,true),
.last 14 (2,true),
.cycle 5 9 true (0),
.last 19 (2,true),
.last 25 (2,true)
])
theorem kid23_part1032_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part1032) = true := by rfl

def kid23_part1033 : Audit := .split 12 (2,true) (byMove [
.cycle 14 25 true (0),
.last 18 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 18 1 false (6),
.last 16 (5,true),
.last 19 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.last 18 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 2 15 true (0),
.last 16 (5,true),
.last 20 (5,true),
.last 13 (5,true)
])
theorem kid23_part1033_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part1033) = true := by rfl

def kid23_part1034 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 21 1 false (-1),
.last 16 (2,true),
.cycle 7 11 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 1 16 true (0),
.cycle 22 18 true (4),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 5 13 true (0),
.cycle 5 21 true (0),
.cycle 27 1 false (-1),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 5 11 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.cycle 1 16 true (0),
.cycle 23 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1)
])
theorem kid23_part1034_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part1034) = true := by rfl

def kid23_part1035 : Audit := .cycle 13 1 false (-1)
theorem kid23_part1035_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part1035) = true := by rfl

def kid23_part1036 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 26 2 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 1 16 true (0),
.cycle 35 7 true (5),
.last 13 (2,true),
.cycle 3 14 true (0),
.cycle 14 2 false (0),
.cycle 17 2 false (5),
.cycle 34 2 false (-2),
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.last 13 (2,true),
.cycle 1 19 true (0),
.cycle 15 2 false (-1),
.cycle 23 2 false (-1)
])
theorem kid23_part1036_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part1036) = true := by rfl

def kid23_part1037 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 18 9 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 16 7 false (2),
.cycle 14 22 false (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 8 true (2),
.cycle 3 12 true (1),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 34, 64],[2, 32, 64, 1, 34, 32, 64],64⟩,
.cycle 13 2 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 16 7 false (2),
.cycle 15 8 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 34, 64],[2, 32, 64, 1, 34, 32, 64],64⟩
])
theorem kid23_part1037_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part1037) = true := by rfl

def kid23_part1038 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 17 7 false (1),
.last 14 (2,true),
.cycle 7 9 true (1),
.cycle 15 5 false (1),
.cycle 14 11 false (2),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 34 true (-1),
.cycle 7 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 5 false (1),
.cycle 14 6 false (2),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 34, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part1038_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part1038) = true := by rfl

def kid23_part1039 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 16 5 false (0),
.cycle 16 1 false (0),
.last 16 (5,true),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 6 7 true (1),
.last 14 (5,true),
.last 24 (5,true),
.cycle 1 14 true (1),
.cycle 2 18 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.last 16 (5,true),
.cycle 14 3 false (0),
.last 13 (5,true),
.last 25 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 14 5 false (2),
.last 13 (5,true)
])
theorem kid23_part1039_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part1039) = true := by rfl

def kid23_part1040 : Audit := .cycle 5 7 true (1)
theorem kid23_part1040_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part1040) = true := by rfl

def kid23_part1041 : Audit := .cycle 13 3 false (1)
theorem kid23_part1041_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part1041) = true := by rfl

def kid23_part1042 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 16 5 false (0),
.last 13 (2,true),
.cycle 0 18 true (0),
.cycle 14 3 false (0),
.cycle 13 4 false (1),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 13 8 true (2),
.cycle 14 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 1 18 true (1),
.cycle 14 3 false (0),
.cycle 13 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 32, 35, 64],[2, 32, 64, 1, 35, 1, 64],64⟩,
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid23_part1042_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part1042) = true := by rfl

def kid23_part1018 : Audit := .split 11 (4,false) (byMove [(kid23_part1019),(kid23_part1020),(kid23_part1021),(kid23_part1022),(kid23_part1023),(kid23_part1024),(kid23_part1025),(kid23_part1026),(kid23_part1027),(kid23_part1028),(kid23_part1029),(kid23_part1030),(kid23_part1031),(kid23_part1032),(kid23_part1033),(kid23_part1034),(kid23_part1035),(kid23_part1036),(kid23_part1037),(kid23_part1038),(kid23_part1039),(kid23_part1040),(kid23_part1041),(kid23_part1042)])

theorem kid23_part1018_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part1018) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid23_part1019),(kid23_part1020),(kid23_part1021),(kid23_part1022),(kid23_part1023),(kid23_part1024),(kid23_part1025),(kid23_part1026),(kid23_part1027),(kid23_part1028),(kid23_part1029),(kid23_part1030),(kid23_part1031),(kid23_part1032),(kid23_part1033),(kid23_part1034),(kid23_part1035),(kid23_part1036),(kid23_part1037),(kid23_part1038),(kid23_part1039),(kid23_part1040),(kid23_part1041),(kid23_part1042)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1019_checked

  · exact kid23_part1025_checked

  · exact kid23_part1031_checked

  · exact kid23_part1037_checked

  · exact kid23_part1020_checked

  · exact kid23_part1026_checked

  · exact kid23_part1032_checked

  · exact kid23_part1038_checked

  · exact kid23_part1021_checked

  · exact kid23_part1027_checked

  · exact kid23_part1033_checked

  · exact kid23_part1039_checked

  · exact kid23_part1022_checked

  · exact kid23_part1028_checked

  · exact kid23_part1034_checked

  · exact kid23_part1040_checked

  · exact kid23_part1023_checked

  · exact kid23_part1029_checked

  · exact kid23_part1035_checked

  · exact kid23_part1041_checked

  · exact kid23_part1024_checked

  · exact kid23_part1030_checked

  · exact kid23_part1036_checked

  · exact kid23_part1042_checked

def kid23_part1044 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.cycle 17 5 false (2),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 21 27 true (1),
.cycle 1 35 true (1),
.cycle 0 15 true (0),
.cycle 19 7 false (3),
.cycle 0 15 true (0),
.cycle 1 17 true (1),
.cycle 1 21 true (1),
.cycle 12 45 true (-1),
.cycle 5 9 true (1),
.cycle 17 5 false (2),
.cycle 12 4 true (1),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 19 (4,false),
.cycle 1 15 true (1)
])
theorem kid23_part1044_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part1044) = true := by rfl

def kid23_part1045 : Audit := .cycle 1 14 true (1)
theorem kid23_part1045_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part1045) = true := by rfl

def kid23_part1046 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 21 1 false (1),
.cycle 0 24 true (0),
.last 21 (4,false),
.cycle 21 1 false (1),
.cycle 7 13 true (0),
.last 50 (4,false),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.last 19 (4,false),
.last 20 (4,false),
.cycle 25 1 false (1),
.cycle 18 5 false (2),
.cycle 35 1 false (3),
.cycle 1 24 true (0),
.last 21 (4,false),
.cycle 21 1 false (1),
.cycle 0 29 true (0),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 4 15 true (0),
.last 19 (4,false),
.cycle 23 1 false (1)
])
theorem kid23_part1046_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part1046) = true := by rfl

def kid23_part1047 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.cycle 18 1 false (0),
.cycle 0 23 true (0),
.cycle 1 16 true (0),
.cycle 22 1 false (0),
.cycle 7 21 true (0),
.cycle 0 17 true (0),
.cycle 20 1 false (0),
.cycle 1 19 true (0),
.cycle 0 20 true (0),
.cycle 7 13 true (0),
.cycle 0 24 true (0),
.cycle 5 11 true (0),
.cycle 18 1 false (0),
.cycle 0 22 true (0),
.cycle 1 16 true (0),
.cycle 0 25 true (0),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.cycle 7 13 true (0),
.cycle 0 18 true (0)
])
theorem kid23_part1047_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part1047) = true := by rfl

def kid23_part1048 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.cycle 9 25 false (3),
.last 12 (2,true),
.last 15 (2,true),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 7 12 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.cycle 10 4 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 21 8 false (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 4 16 true (1),
.cycle 15 9 false (1),
.cycle 17 4 false (-1)
])
theorem kid23_part1048_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part1048) = true := by rfl

def kid23_part1049 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 22 15 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 1 22 false (4),
.cycle 11 10 false (1),
.last 15 (2,true),
.cycle 1 36 true (-2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 13 7 false (-1),
.last 16 (2,true),
.cycle 1 26 false (4),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 41 (2,true),
.cycle 18 6 false (-2),
.last 15 (2,true),
.cycle 5 10 false (4),
.cycle 13 4 false (-1),
.cycle 13 4 false (-1)
])
theorem kid23_part1049_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part1049) = true := by rfl

def kid23_part1050 : Audit := .cycle 6 5 true (2)
theorem kid23_part1050_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part1050) = true := by rfl

def kid23_part1051 : Audit := .cycle 1 12 true (1)
theorem kid23_part1051_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part1051) = true := by rfl

def kid23_part1052 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 2 19 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.last 16 (4,false),
.cycle 11 14 true (0),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 28 (4,false),
.cycle 13 8 true (3),
.cycle 19 8 true (3),
.cycle 1 14 true (1),
.cycle 4 15 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 12 8 true (3)
])
theorem kid23_part1052_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part1052) = true := by rfl

def kid23_part1053 : Audit := .cycle 1 12 true (1)
theorem kid23_part1053_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part1053) = true := by rfl

def kid23_part1054 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 16 53 true (-3),
.last 14 (2,true),
.cycle 25 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 2 false (1),
.cycle 0 18 true (0),
.cycle 18 7 false (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 16 3 false (0),
.cycle 10 4 true (1),
.cycle 15 10 false (3),
.last 22 (2,true),
.last 14 (2,true),
.cycle 25 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 2 false (0),
.cycle 0 18 true (0),
.cycle 22 9 false (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 18 5 false (0),
.cycle 19 6 false (1)
])
theorem kid23_part1054_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part1054) = true := by rfl

def kid23_part1055 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.last 48 (2,true),
.cycle 7 25 true (0),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 1 15 true (1),
.cycle 11 10 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 26 3 false (0),
.cycle 12 3 true (4),
.cycle 16 5 true (4),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 5 37 true (0),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 11 5 true (3),
.cycle 12 3 true (4)
])
theorem kid23_part1055_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part1055) = true := by rfl

def kid23_part1056 : Audit := .cycle 12 11 true (2)
theorem kid23_part1056_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part1056) = true := by rfl

def kid23_part1057 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.last 23 (4,false),
.cycle 16 1 false (0),
.cycle 15 2 true (3),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 6 7 true (1),
.cycle 13 2 true (3),
.cycle 23 2 true (3),
.cycle 1 14 true (1),
.last 23 (4,false),
.last 20 (4,false),
.cycle 14 2 true (2),
.cycle 13 2 true (1),
.cycle 18 2 true (2),
.cycle 15 2 true (3),
.last 19 (4,false),
.cycle 13 2 true (0),
.cycle 17 2 true (2),
.cycle 13 2 true (3),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 14 2 true (1),
.cycle 13 2 true (2)
])
theorem kid23_part1057_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part1057) = true := by rfl

def kid23_part1058 : Audit := .cycle 5 7 true (1)
theorem kid23_part1058_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part1058) = true := by rfl

def kid23_part1059 : Audit := .cycle 5 11 true (0)
theorem kid23_part1059_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part1059) = true := by rfl

def kid23_part1060 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 41 9 true (0),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 9 6 true (1),
.cycle 16 5 false (0),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 14 3 false (0),
.cycle 10 2 true (1),
.cycle 13 6 false (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 19 8 false (2),
.cycle 18 5 false (0),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 16 3 false (-1),
.cycle 15 4 false (0)
])
theorem kid23_part1060_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part1060) = true := by rfl

def kid23_part1061 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 11 15 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 13 7 false (1),
.cycle 13 5 false (0),
.last 15 (2,true),
.cycle 13 8 true (-2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 13 7 false (-1),
.last 16 (2,true),
.cycle 13 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 13 8 false (1),
.cycle 13 6 false (0),
.last 15 (2,true),
.cycle 10 10 false (2),
.cycle 13 4 false (-1),
.cycle 13 4 false (-1)
])
theorem kid23_part1061_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part1061) = true := by rfl

def kid23_part1062 : Audit := .cycle 6 5 true (2)
theorem kid23_part1062_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part1062) = true := by rfl

def kid23_part1063 : Audit := .cycle 1 12 true (1)
theorem kid23_part1063_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part1063) = true := by rfl

def kid23_part1064 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 18 (4,false),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.last 20 (4,false),
.cycle 2 29 true (1),
.cycle 0 13 true (0),
.last 18 (4,false),
.cycle 2 11 true (1),
.cycle 2 13 true (1),
.cycle 2 15 true (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 16 (4,false),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 2 11 true (1)
])
theorem kid23_part1064_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part1064) = true := by rfl

def kid23_part1065 : Audit := .cycle 1 12 true (1)
theorem kid23_part1065_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part1065) = true := by rfl

def kid23_part1066 : Audit := .cycle 9 2 true (2)
theorem kid23_part1066_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part1066) = true := by rfl

def kid23_part1067 : Audit := .cycle 8 5 true (2)
theorem kid23_part1067_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part1067) = true := by rfl

def kid23_part1043 : Audit := .split 10 (5,true) (byMove [(kid23_part1044),(kid23_part1045),(kid23_part1046),(kid23_part1047),(kid23_part1048),(kid23_part1049),(kid23_part1050),(kid23_part1051),(kid23_part1052),(kid23_part1053),(kid23_part1054),(kid23_part1055),(kid23_part1056),(kid23_part1057),(kid23_part1058),(kid23_part1059),(kid23_part1060),(kid23_part1061),(kid23_part1062),(kid23_part1063),(kid23_part1064),(kid23_part1065),(kid23_part1066),(kid23_part1067)])

theorem kid23_part1043_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part1043) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part1044),(kid23_part1045),(kid23_part1046),(kid23_part1047),(kid23_part1048),(kid23_part1049),(kid23_part1050),(kid23_part1051),(kid23_part1052),(kid23_part1053),(kid23_part1054),(kid23_part1055),(kid23_part1056),(kid23_part1057),(kid23_part1058),(kid23_part1059),(kid23_part1060),(kid23_part1061),(kid23_part1062),(kid23_part1063),(kid23_part1064),(kid23_part1065),(kid23_part1066),(kid23_part1067)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1044_checked

  · exact kid23_part1050_checked

  · exact kid23_part1056_checked

  · exact kid23_part1062_checked

  · exact kid23_part1045_checked

  · exact kid23_part1051_checked

  · exact kid23_part1057_checked

  · exact kid23_part1063_checked

  · exact kid23_part1046_checked

  · exact kid23_part1052_checked

  · exact kid23_part1058_checked

  · exact kid23_part1064_checked

  · exact kid23_part1047_checked

  · exact kid23_part1053_checked

  · exact kid23_part1059_checked

  · exact kid23_part1065_checked

  · exact kid23_part1048_checked

  · exact kid23_part1054_checked

  · exact kid23_part1060_checked

  · exact kid23_part1066_checked

  · exact kid23_part1049_checked

  · exact kid23_part1055_checked

  · exact kid23_part1061_checked

  · exact kid23_part1067_checked

def kid23_part1068 : Audit := .cycle 1 10 true (1)
theorem kid23_part1068_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part1068) = true := by rfl

def kid23_part1069 : Audit := .cycle 7 3 true (3)
theorem kid23_part1069_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part1069) = true := by rfl

def kid23_part1071 : Audit := .cycle 1 11 true (1)
theorem kid23_part1071_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part1071) = true := by rfl

def kid23_part1072 : Audit := .cycle 7 4 true (3)
theorem kid23_part1072_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part1072) = true := by rfl

def kid23_part1073 : Audit := .cycle 25 1 false (1)
theorem kid23_part1073_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part1073) = true := by rfl

def kid23_part1074 : Audit := .cycle 0 12 true (0)
theorem kid23_part1074_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part1074) = true := by rfl

def kid23_part1075 : Audit := .cycle 2 10 true (1)
theorem kid23_part1075_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part1075) = true := by rfl

def kid23_part1076 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 25 (4,false),
.cycle 1 13 true (1),
.last 15 (4,false),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (3)
])
theorem kid23_part1076_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part1076) = true := by rfl

def kid23_part1077 : Audit := .cycle 0 11 true (0)
theorem kid23_part1077_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part1077) = true := by rfl

def kid23_part1078 : Audit := .cycle 1 10 true (1)
theorem kid23_part1078_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part1078) = true := by rfl

def kid23_part1079 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 10 9 true (3),
.cycle 0 20 true (0),
.cycle 2 18 true (1),
.last 35 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.last 19 (4,false),
.last 20 (4,false),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 256, 1, 128, 2048, 4, 1, 256, 4, 4096],5168⟩,
.cycle 1 20 true (1),
.cycle 9 10 true (3),
.last 41 (4,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 8 11 true (3)
])
theorem kid23_part1079_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part1079) = true := by rfl

def kid23_part1080 : Audit := .cycle 3 8 true (1)
theorem kid23_part1080_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part1080) = true := by rfl

def kid23_part1081 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 12 true (1),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 11 1 true (5),
.last 14 (5,true),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1081_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part1081) = true := by rfl

def kid23_part1082 : Audit := .split 12 (4,false) (byMove [
.cycle 10 5 true (3),
.last 17 (5,true),
.last 25 (5,true),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 13 (5,true)
])
theorem kid23_part1082_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part1082) = true := by rfl

def kid23_part1083 : Audit := .cycle 6 5 true (2)
theorem kid23_part1083_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part1083) = true := by rfl

def kid23_part1084 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 21 5 false (1),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 22 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.last 22 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
])
theorem kid23_part1084_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part1084) = true := by rfl

def kid23_part1085 : Audit := .cycle 5 9 true (1)
theorem kid23_part1085_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part1085) = true := by rfl

def kid23_part1086 : Audit := .cycle 1 12 true (1)
theorem kid23_part1086_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part1086) = true := by rfl

def kid23_part1087 : Audit := .cycle 9 2 true (3)
theorem kid23_part1087_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part1087) = true := by rfl

def kid23_part1088 : Audit := .split 11 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 1 20 true (1),
.cycle 18 1 false (0),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 18 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 19 (4,false),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 14 (4,false),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 41 (4,false),
.cycle 5 7 true (1),
.last 15 (4,false),
.last 18 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.cycle 8 5 true (3)
])
theorem kid23_part1088_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part1088) = true := by rfl

def kid23_part1089 : Audit := .cycle 0 11 true (0)
theorem kid23_part1089_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part1089) = true := by rfl

def kid23_part1090 : Audit := .cycle 1 10 true (1)
theorem kid23_part1090_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part1090) = true := by rfl

def kid23_part1091 : Audit := .cycle 2 9 true (1)
theorem kid23_part1091_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part1091) = true := by rfl

def kid23_part1092 : Audit := .cycle 1 13 true (1)
theorem kid23_part1092_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part1092) = true := by rfl

def kid23_part1093 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.last 14 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1093_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part1093) = true := by rfl

def kid23_part1094 : Audit := .cycle 8 3 true (3)
theorem kid23_part1094_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part1094) = true := by rfl

def kid23_part1070 : Audit := .split 10 (2,true) (byMove [(kid23_part1071),(kid23_part1072),(kid23_part1073),(kid23_part1074),(kid23_part1075),(kid23_part1076),(kid23_part1077),(kid23_part1078),(kid23_part1079),(kid23_part1080),(kid23_part1081),(kid23_part1082),(kid23_part1083),(kid23_part1084),(kid23_part1085),(kid23_part1086),(kid23_part1087),(kid23_part1088),(kid23_part1089),(kid23_part1090),(kid23_part1091),(kid23_part1092),(kid23_part1093),(kid23_part1094)])

theorem kid23_part1070_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part1070) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid23_part1071),(kid23_part1072),(kid23_part1073),(kid23_part1074),(kid23_part1075),(kid23_part1076),(kid23_part1077),(kid23_part1078),(kid23_part1079),(kid23_part1080),(kid23_part1081),(kid23_part1082),(kid23_part1083),(kid23_part1084),(kid23_part1085),(kid23_part1086),(kid23_part1087),(kid23_part1088),(kid23_part1089),(kid23_part1090),(kid23_part1091),(kid23_part1092),(kid23_part1093),(kid23_part1094)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1071_checked

  · exact kid23_part1077_checked

  · exact kid23_part1083_checked

  · exact kid23_part1089_checked

  · exact kid23_part1072_checked

  · exact kid23_part1078_checked

  · exact kid23_part1084_checked

  · exact kid23_part1090_checked

  · exact kid23_part1073_checked

  · exact kid23_part1079_checked

  · exact kid23_part1085_checked

  · exact kid23_part1091_checked

  · exact kid23_part1074_checked

  · exact kid23_part1080_checked

  · exact kid23_part1086_checked

  · exact kid23_part1092_checked

  · exact kid23_part1075_checked

  · exact kid23_part1081_checked

  · exact kid23_part1087_checked

  · exact kid23_part1093_checked

  · exact kid23_part1076_checked

  · exact kid23_part1082_checked

  · exact kid23_part1088_checked

  · exact kid23_part1094_checked

def kid23_part1095 : Audit := .cycle 0 11 true (0)
theorem kid23_part1095_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part1095) = true := by rfl

def kid23_part1097 : Audit := .cycle 1 12 true (1)
theorem kid23_part1097_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part1097) = true := by rfl

def kid23_part1098 : Audit := .cycle 7 5 true (3)
theorem kid23_part1098_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part1098) = true := by rfl

def kid23_part1099 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.cycle 8 5 true (3)
])
theorem kid23_part1099_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part1099) = true := by rfl

def kid23_part1100 : Audit := .cycle 0 13 true (0)
theorem kid23_part1100_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part1100) = true := by rfl

def kid23_part1101 : Audit := .cycle 10 2 true (4)
theorem kid23_part1101_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part1101) = true := by rfl

def kid23_part1102 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 2 false (-1),
.cycle 21 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 8 true (3),
.cycle 3 10 true (1),
.cycle 8 6 true (3),
.cycle 29 2 false (1),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 27 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.cycle 8 5 true (3)
])
theorem kid23_part1102_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part1102) = true := by rfl

def kid23_part1103 : Audit := .cycle 0 12 true (0)
theorem kid23_part1103_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part1103) = true := by rfl

def kid23_part1104 : Audit := .cycle 1 11 true (1)
theorem kid23_part1104_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part1104) = true := by rfl

def kid23_part1105 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 10 true (4),
.cycle 8 14 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (4),
.cycle 3 17 true (1),
.cycle 10 20 true (4),
.last 22 (2,true),
.cycle 6 14 true (2),
.cycle 18 2 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 9 11 true (3),
.cycle 9 17 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.cycle 8 12 true (3)
])
theorem kid23_part1105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part1105) = true := by rfl

def kid23_part1106 : Audit := .cycle 3 9 true (1)
theorem kid23_part1106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part1106) = true := by rfl

def kid23_part1107 : Audit := .cycle 11 1 true (5)
theorem kid23_part1107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part1107) = true := by rfl

def kid23_part1108 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 3 19 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.cycle 7 9 true (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 13 2 true (5),
.cycle 9 8 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3)
])
theorem kid23_part1108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part1108) = true := by rfl

def kid23_part1109 : Audit := .cycle 6 6 true (2)
theorem kid23_part1109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part1109) = true := by rfl

def kid23_part1110 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.last 28 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.last 16 (2,true),
.last 22 (2,true),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 9 5 true (3),
.last 36 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.cycle 8 6 true (3)
])
theorem kid23_part1110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part1110) = true := by rfl

def kid23_part1111 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 9 7 true (3),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.last 54 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (5,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.cycle 9 5 true (3),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.last 13 (5,true)
])
theorem kid23_part1111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part1111) = true := by rfl

def kid23_part1112 : Audit := .cycle 1 13 true (1)
theorem kid23_part1112_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part1112) = true := by rfl

def kid23_part1113 : Audit := .cycle 9 3 true (3)
theorem kid23_part1113_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part1113) = true := by rfl

def kid23_part1114 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 9 7 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 21 2 false (-1),
.cycle 21 2 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 9 10 true (3),
.cycle 6 10 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 9 5 true (3),
.cycle 29 2 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 6 true (3)
])
theorem kid23_part1114_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part1114) = true := by rfl

def kid23_part1115 : Audit := .cycle 0 12 true (0)
theorem kid23_part1115_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part1115) = true := by rfl

def kid23_part1116 : Audit := .cycle 1 11 true (1)
theorem kid23_part1116_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part1116) = true := by rfl

def kid23_part1117 : Audit := .cycle 2 10 true (1)
theorem kid23_part1117_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part1117) = true := by rfl

def kid23_part1118 : Audit := .cycle 1 14 true (1)
theorem kid23_part1118_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part1118) = true := by rfl

def kid23_part1119 : Audit := .cycle 11 1 true (5)
theorem kid23_part1119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part1119) = true := by rfl

def kid23_part1120 : Audit := .cycle 8 4 true (3)
theorem kid23_part1120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part1120) = true := by rfl

def kid23_part1096 : Audit := .split 11 (4,false) (byMove [(kid23_part1097),(kid23_part1098),(kid23_part1099),(kid23_part1100),(kid23_part1101),(kid23_part1102),(kid23_part1103),(kid23_part1104),(kid23_part1105),(kid23_part1106),(kid23_part1107),(kid23_part1108),(kid23_part1109),(kid23_part1110),(kid23_part1111),(kid23_part1112),(kid23_part1113),(kid23_part1114),(kid23_part1115),(kid23_part1116),(kid23_part1117),(kid23_part1118),(kid23_part1119),(kid23_part1120)])

theorem kid23_part1096_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part1096) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid23_part1097),(kid23_part1098),(kid23_part1099),(kid23_part1100),(kid23_part1101),(kid23_part1102),(kid23_part1103),(kid23_part1104),(kid23_part1105),(kid23_part1106),(kid23_part1107),(kid23_part1108),(kid23_part1109),(kid23_part1110),(kid23_part1111),(kid23_part1112),(kid23_part1113),(kid23_part1114),(kid23_part1115),(kid23_part1116),(kid23_part1117),(kid23_part1118),(kid23_part1119),(kid23_part1120)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1097_checked

  · exact kid23_part1103_checked

  · exact kid23_part1109_checked

  · exact kid23_part1115_checked

  · exact kid23_part1098_checked

  · exact kid23_part1104_checked

  · exact kid23_part1110_checked

  · exact kid23_part1116_checked

  · exact kid23_part1099_checked

  · exact kid23_part1105_checked

  · exact kid23_part1111_checked

  · exact kid23_part1117_checked

  · exact kid23_part1100_checked

  · exact kid23_part1106_checked

  · exact kid23_part1112_checked

  · exact kid23_part1118_checked

  · exact kid23_part1101_checked

  · exact kid23_part1107_checked

  · exact kid23_part1113_checked

  · exact kid23_part1119_checked

  · exact kid23_part1102_checked

  · exact kid23_part1108_checked

  · exact kid23_part1114_checked

  · exact kid23_part1120_checked

def kid23_part1122 : Audit := .cycle 1 11 true (1)
theorem kid23_part1122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part1122) = true := by rfl

def kid23_part1123 : Audit := .cycle 7 4 true (3)
theorem kid23_part1123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part1123) = true := by rfl

def kid23_part1124 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 17 (4,false),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 19 5 false (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 15 (4,false),
.cycle 23 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (3)
])
theorem kid23_part1124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part1124) = true := by rfl

def kid23_part1125 : Audit := .cycle 0 12 true (0)
theorem kid23_part1125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part1125) = true := by rfl

def kid23_part1126 : Audit := .cycle 8 4 true (3)
theorem kid23_part1126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part1126) = true := by rfl

def kid23_part1127 : Audit := .split 18 (4,false) (byMove [
.last 21 (2,true),
.last 53 (2,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 1 19 false (4),
.cycle 13 7 false (1),
.last 19 (2,true),
.cycle 0 20 true (-2),
.cycle 13 7 false (1),
.cycle 16 3 false (0),
.cycle 15 7 false (1),
.last 20 (2,true),
.cycle 1 21 false (4),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 15 20 false (3),
.cycle 15 8 false (1),
.last 19 (2,true),
.cycle 11 24 false (4),
.cycle 15 8 false (1),
.cycle 15 4 false (1)
])
theorem kid23_part1127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part1127) = true := by rfl

def kid23_part1128 : Audit := .cycle 0 11 true (0)
theorem kid23_part1128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part1128) = true := by rfl

def kid23_part1129 : Audit := .cycle 1 10 true (1)
theorem kid23_part1129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part1129) = true := by rfl

def kid23_part1130 : Audit := .cycle 10 8 true (3)
theorem kid23_part1130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part1130) = true := by rfl

def kid23_part1131 : Audit := .cycle 3 8 true (1)
theorem kid23_part1131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part1131) = true := by rfl

def kid23_part1132 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 6 true (3),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 14 true (3),
.cycle 10 8 true (3),
.cycle 11 1 true (5),
.cycle 10 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 8 true (3),
.cycle 8 8 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part1132) = true := by rfl

def kid23_part1133 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 0 23 true (0),
.last 13 (2,true),
.cycle 7 8 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 25 2 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.cycle 10 5 true (3),
.last 19 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 57 2 false (9),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 10 3 true (4)
])
theorem kid23_part1133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part1133) = true := by rfl

def kid23_part1134 : Audit := .cycle 6 5 true (2)
theorem kid23_part1134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part1134) = true := by rfl

def kid23_part1135 : Audit := .cycle 10 2 true (3)
theorem kid23_part1135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part1135) = true := by rfl

def kid23_part1136 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 17 (4,false),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 2048, 4, 1, 2048, 1, 128, 2048, 4, 1, 2048, 4, 4096],5168⟩,
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 19 5 false (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 15 (4,false),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 10 2 true (3)
])
theorem kid23_part1136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part1136) = true := by rfl

def kid23_part1137 : Audit := .cycle 1 12 true (1)
theorem kid23_part1137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part1137) = true := by rfl

def kid23_part1138 : Audit := .cycle 9 2 true (3)
theorem kid23_part1138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part1138) = true := by rfl

def kid23_part1139 : Audit := .split 18 (4,false) (byMove [
.last 21 (2,true),
.cycle 13 17 false (2),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 15 7 false (1),
.cycle 15 5 false (1),
.last 19 (2,true),
.cycle 15 8 true (-2),
.cycle 14 5 false (1),
.cycle 16 3 false (0),
.cycle 15 7 false (1),
.last 20 (2,true),
.cycle 15 9 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 15 8 false (1),
.cycle 15 6 false (1),
.last 19 (2,true),
.cycle 10 12 false (4),
.cycle 15 6 false (1),
.cycle 15 4 false (1)
])
theorem kid23_part1139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part1139) = true := by rfl

def kid23_part1140 : Audit := .cycle 0 11 true (0)
theorem kid23_part1140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part1140) = true := by rfl

def kid23_part1141 : Audit := .cycle 1 10 true (1)
theorem kid23_part1141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part1141) = true := by rfl

def kid23_part1142 : Audit := .cycle 2 9 true (1)
theorem kid23_part1142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part1142) = true := by rfl

def kid23_part1143 : Audit := .cycle 1 13 true (1)
theorem kid23_part1143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part1143) = true := by rfl

def kid23_part1144 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 4 true (4),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.cycle 8 6 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part1144) = true := by rfl

def kid23_part1145 : Audit := .cycle 8 3 true (3)
theorem kid23_part1145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part1145) = true := by rfl

def kid23_part1121 : Audit := .split 10 (5,true) (byMove [(kid23_part1122),(kid23_part1123),(kid23_part1124),(kid23_part1125),(kid23_part1126),(kid23_part1127),(kid23_part1128),(kid23_part1129),(kid23_part1130),(kid23_part1131),(kid23_part1132),(kid23_part1133),(kid23_part1134),(kid23_part1135),(kid23_part1136),(kid23_part1137),(kid23_part1138),(kid23_part1139),(kid23_part1140),(kid23_part1141),(kid23_part1142),(kid23_part1143),(kid23_part1144),(kid23_part1145)])

theorem kid23_part1121_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part1121) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid23_part1122),(kid23_part1123),(kid23_part1124),(kid23_part1125),(kid23_part1126),(kid23_part1127),(kid23_part1128),(kid23_part1129),(kid23_part1130),(kid23_part1131),(kid23_part1132),(kid23_part1133),(kid23_part1134),(kid23_part1135),(kid23_part1136),(kid23_part1137),(kid23_part1138),(kid23_part1139),(kid23_part1140),(kid23_part1141),(kid23_part1142),(kid23_part1143),(kid23_part1144),(kid23_part1145)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1122_checked

  · exact kid23_part1128_checked

  · exact kid23_part1134_checked

  · exact kid23_part1140_checked

  · exact kid23_part1123_checked

  · exact kid23_part1129_checked

  · exact kid23_part1135_checked

  · exact kid23_part1141_checked

  · exact kid23_part1124_checked

  · exact kid23_part1130_checked

  · exact kid23_part1136_checked

  · exact kid23_part1142_checked

  · exact kid23_part1125_checked

  · exact kid23_part1131_checked

  · exact kid23_part1137_checked

  · exact kid23_part1143_checked

  · exact kid23_part1126_checked

  · exact kid23_part1132_checked

  · exact kid23_part1138_checked

  · exact kid23_part1144_checked

  · exact kid23_part1127_checked

  · exact kid23_part1133_checked

  · exact kid23_part1139_checked

  · exact kid23_part1145_checked

def kid23_part761 : Audit := .split 9 (4,true) (byMove [(kid23_part762),(kid23_part787),(kid23_part788),(kid23_part813),(kid23_part814),(kid23_part839),(kid23_part864),(kid23_part865),(kid23_part866),(kid23_part891),(kid23_part892),(kid23_part917),(kid23_part942),(kid23_part967),(kid23_part992),(kid23_part1017),(kid23_part1018),(kid23_part1043),(kid23_part1068),(kid23_part1069),(kid23_part1070),(kid23_part1095),(kid23_part1096),(kid23_part1121)])

theorem kid23_part761_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (kid23_part761) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) 9 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part762),(kid23_part787),(kid23_part788),(kid23_part813),(kid23_part814),(kid23_part839),(kid23_part864),(kid23_part865),(kid23_part866),(kid23_part891),(kid23_part892),(kid23_part917),(kid23_part942),(kid23_part967),(kid23_part992),(kid23_part1017),(kid23_part1018),(kid23_part1043),(kid23_part1068),(kid23_part1069),(kid23_part1070),(kid23_part1095),(kid23_part1096),(kid23_part1121)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part762_checked

  · exact kid23_part864_checked

  · exact kid23_part942_checked

  · exact kid23_part1068_checked

  · exact kid23_part787_checked

  · exact kid23_part865_checked

  · exact kid23_part967_checked

  · exact kid23_part1069_checked

  · exact kid23_part788_checked

  · exact kid23_part866_checked

  · exact kid23_part992_checked

  · exact kid23_part1070_checked

  · exact kid23_part813_checked

  · exact kid23_part891_checked

  · exact kid23_part1017_checked

  · exact kid23_part1095_checked

  · exact kid23_part814_checked

  · exact kid23_part892_checked

  · exact kid23_part1018_checked

  · exact kid23_part1096_checked

  · exact kid23_part839_checked

  · exact kid23_part917_checked

  · exact kid23_part1043_checked

  · exact kid23_part1121_checked

def kid23_part1147 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 25 7 false (2),
.cycle 6 8 true (2),
.cycle 1 16 true (1),
.last 15 (4,false),
.cycle 1 15 true (1),
.last 15 (4,false),
.cycle 21 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 8 6 true (2)
]),
.cycle 1 14 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 21 true (1),
.cycle 3 10 true (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 13 true (2),
.cycle 1 21 true (1),
.cycle 13 1 true (5),
.last 21 (4,true),
.cycle 7 8 true (2),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 6 true (3)
]),
.cycle 0 20 true (0),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 25 7 false (2),
.last 15 (4,false),
.cycle 7 9 true (2),
.last 15 (4,false),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 1 17 true (1),
.cycle 9 6 true (2),
.last 15 (4,false),
.cycle 5 9 true (1),
.last 15 (4,false),
.cycle 21 5 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 1 15 true (1)
]),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (4),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.last 20 (4,true),
.cycle 6 8 true (2),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 9 5 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2)
]),
.cycle 8 5 true (2)
])
theorem kid23_part1147_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part1147) = true := by rfl

def kid23_part1148 : Audit := .cycle 1 16 true (1)
theorem kid23_part1148_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part1148) = true := by rfl

def kid23_part1149 : Audit := .split 10 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 35 1 false (1),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.split 11 (4,false) (byMove [
.last 22 (4,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.last 12 (4,true),
.cycle 14 1 false (0),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 13 6 false (2),
.last 18 (4,true),
.last 27 (4,true),
.cycle 0 17 true (0),
.last 12 (4,true),
.cycle 14 1 false (0),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 20 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 19 1 false (-1)
]),
.cycle 14 1 false (0),
.cycle 7 5 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 34 1 false (4),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 34, 64],[2, 32, 16, 1, 64, 34, 64],64⟩,
.last 29 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 40 1 false (2),
.cycle 7 11 true (2),
.last 14 (4,true),
.cycle 1 14 true (1),
.cycle 35 1 false (3),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 19 true (0)
]),
.cycle 16 1 false (0),
.cycle 17 5 false (2),
.cycle 15 5 false (1),
.cycle 7 7 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (0),
.last 15 (4,true),
.last 23 (4,true),
.cycle 10 2 true (1),
.cycle 7 7 true (1),
.last 12 (4,true),
.cycle 25 1 false (1),
.last 16 (4,true),
.last 18 (4,true),
.last 20 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (0),
.last 15 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 7 7 true (1),
.last 12 (4,true),
.last 14 (4,true)
]),
.cycle 14 1 false (0),
.cycle 7 5 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 11 (4,false) (byMove [
.cycle 1 16 true (1),
.cycle 33 1 false (1),
.cycle 10 2 true (2),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 25 1 false (1),
.cycle 1 12 true (1),
.cycle 1 23 true (1),
.cycle 12 10 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 6 11 true (2),
.cycle 9 4 true (2),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 27 1 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 7 true (2)
]),
.cycle 27 1 false (1)
])
theorem kid23_part1149_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part1149) = true := by rfl

def kid23_part1150 : Audit := .cycle 7 5 true (2)
theorem kid23_part1150_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part1150) = true := by rfl

def kid23_part1152 : Audit := .cycle 0 15 true (0)
theorem kid23_part1152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part1152) = true := by rfl

def kid23_part1153 : Audit := .split 23 (4,false) (byMove [
.cycle 0 28 true (0),
.cycle 24 13 false (1),
.last 24 (2,true),
.last 27 (2,true),
.cycle 47 1 false (-1),
.cycle 26 1 false (-2),
.cycle 7 18 true (1),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 35 1 false (1),
.cycle 1 25 true (1),
.cycle 28 1 false (0),
.cycle 25 18 false (2),
.last 51 (2,true),
.last 24 (2,true),
.last 27 (2,true),
.last 53 (2,true),
.cycle 26 1 false (-2),
.cycle 40 9 false (2),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.cycle 28 19 false (2),
.cycle 37 3 false (1)
])
theorem kid23_part1153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part1153) = true := by rfl

def kid23_part1154 : Audit := .cycle 21 1 false (1)
theorem kid23_part1154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part1154) = true := by rfl

def kid23_part1155 : Audit := .cycle 0 17 true (0)
theorem kid23_part1155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part1155) = true := by rfl

def kid23_part1156 : Audit := .split 11 (4,false) (byMove [
.cycle 1 24 true (0),
.cycle 25 11 false (0),
.last 12 (2,true),
.cycle 0 17 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 true (3),
.cycle 16 1 false (0),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 0 17 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 2 20 true (1),
.last 16 (2,true),
.cycle 19 1 true (-1),
.cycle 15 3 false (0)
])
theorem kid23_part1156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part1156) = true := by rfl

def kid23_part1157 : Audit := .split 13 (4,false) (byMove [
.last 20 (2,true),
.cycle 35 1 false (-3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-1),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 16 1 false (0),
.cycle 14 1 false (0),
.cycle 19 1 false (-3),
.last 15 (2,true),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 107 (2,true),
.last 15 (2,true),
.last 18 (2,true),
.cycle 21 1 false (-1),
.cycle 18 1 false (-2),
.cycle 11 3 false (1)
])
theorem kid23_part1157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part1157) = true := by rfl

def kid23_part1158 : Audit := .cycle 7 5 true (2)
theorem kid23_part1158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part1158) = true := by rfl

def kid23_part1159 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 16 (4,false),
.cycle 62 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 21 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 17 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part1159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part1159) = true := by rfl

def kid23_part1160 : Audit := .cycle 0 13 true (0)
theorem kid23_part1160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part1160) = true := by rfl

def kid23_part1161 : Audit := .cycle 34 1 false (4)
theorem kid23_part1161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part1161) = true := by rfl

def kid23_part1162 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (-2),
.cycle 1 12 true (1),
.last 17 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.cycle 20 1 false (0),
.cycle 7 11 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 35 1 false (3),
.cycle 19 1 false (5),
.cycle 16 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.cycle 39 3 false (6)
])
theorem kid23_part1162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part1162) = true := by rfl

def kid23_part1163 : Audit := .split 15 (4,false) (byMove [
.cycle 1 32 true (-2),
.cycle 12 13 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 12 8 true (-1),
.last 17 (2,true),
.cycle 1 28 true (-1),
.cycle 16 1 false (0),
.cycle 23 1 true (3),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.last 17 (2,true),
.cycle 12 10 true (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 24 1 false (0),
.last 17 (2,true),
.cycle 1 28 true (-1),
.cycle 12 10 true (-1),
.cycle 23 1 true (3),
.cycle 13 3 false (1)
])
theorem kid23_part1163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part1163) = true := by rfl

def kid23_part1164 : Audit := .cycle 17 5 false (2)
theorem kid23_part1164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part1164) = true := by rfl

def kid23_part1165 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 7 7 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 3 22 true (1),
.last 13 (4,false),
.last 22 (4,false),
.cycle 19 7 false (1),
.cycle 16 5 false (1),
.cycle 1 46 true (-1),
.cycle 1 18 true (1),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 69 35 false (5),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 17 5 false (1)
])
theorem kid23_part1165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part1165) = true := by rfl

def kid23_part1166 : Audit := .cycle 7 7 true (1)
theorem kid23_part1166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part1166) = true := by rfl

def kid23_part1167 : Audit := .cycle 18 1 false (0)
theorem kid23_part1167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part1167) = true := by rfl

def kid23_part1168 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.last 32 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.last 12 (2,true),
.cycle 7 7 true (1),
.cycle 10 2 true (1),
.cycle 18 1 false (0),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (2,true),
.cycle 14 5 false (2),
.last 12 (2,true),
.cycle 7 7 true (1),
.cycle 13 3 false (1),
.cycle 14 3 false (0)
])
theorem kid23_part1168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part1168) = true := by rfl

def kid23_part1169 : Audit := .split 13 (4,false) (byMove [
.last 20 (2,true),
.cycle 12 11 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 25 1 false (-1),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 16 1 false (0),
.cycle 14 1 false (0),
.cycle 19 1 false (-3),
.last 15 (2,true),
.cycle 29 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 20 1 false (-2),
.last 15 (2,true),
.last 18 (2,true),
.cycle 29 1 false (-1),
.cycle 18 1 false (-2),
.cycle 11 3 false (1)
])
theorem kid23_part1169_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part1169) = true := by rfl

def kid23_part1170 : Audit := .cycle 7 5 true (2)
theorem kid23_part1170_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part1170) = true := by rfl

def kid23_part1171 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 14 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 21 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 20 (4,false),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (2)
])
theorem kid23_part1171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part1171) = true := by rfl

def kid23_part1172 : Audit := .cycle 0 13 true (0)
theorem kid23_part1172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part1172) = true := by rfl

def kid23_part1173 : Audit := .cycle 4 7 true (1)
theorem kid23_part1173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part1173) = true := by rfl

def kid23_part1174 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 15 19 false (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 10 2 true (2),
.cycle 16 1 false (-2),
.cycle 1 12 true (1),
.last 17 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.cycle 22 1 false (0),
.cycle 6 11 true (2),
.cycle 9 4 true (2),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 13 3 true (3),
.cycle 16 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (5),
.cycle 8 7 true (2)
])
theorem kid23_part1174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part1174) = true := by rfl

def kid23_part1175 : Audit := .split 13 (4,false) (byMove [
.cycle 1 18 true (0),
.cycle 15 15 false (1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 8 10 true (1),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 27 1 false (1),
.cycle 17 5 true (2),
.cycle 18 1 false (0),
.cycle 15 8 false (2),
.last 21 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.cycle 19 1 false (-1),
.cycle 16 1 false (-2),
.cycle 19 13 false (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 8 12 true (1),
.cycle 19 13 false (3),
.cycle 17 3 false (1)
])
theorem kid23_part1175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part1175) = true := by rfl

def kid23_part1151 : Audit := .split 10 (4,true) (byMove [(kid23_part1152),(kid23_part1153),(kid23_part1154),(kid23_part1155),(kid23_part1156),(kid23_part1157),(kid23_part1158),(kid23_part1159),(kid23_part1160),(kid23_part1161),(kid23_part1162),(kid23_part1163),(kid23_part1164),(kid23_part1165),(kid23_part1166),(kid23_part1167),(kid23_part1168),(kid23_part1169),(kid23_part1170),(kid23_part1171),(kid23_part1172),(kid23_part1173),(kid23_part1174),(kid23_part1175)])

theorem kid23_part1151_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part1151) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part1152),(kid23_part1153),(kid23_part1154),(kid23_part1155),(kid23_part1156),(kid23_part1157),(kid23_part1158),(kid23_part1159),(kid23_part1160),(kid23_part1161),(kid23_part1162),(kid23_part1163),(kid23_part1164),(kid23_part1165),(kid23_part1166),(kid23_part1167),(kid23_part1168),(kid23_part1169),(kid23_part1170),(kid23_part1171),(kid23_part1172),(kid23_part1173),(kid23_part1174),(kid23_part1175)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1152_checked

  · exact kid23_part1158_checked

  · exact kid23_part1164_checked

  · exact kid23_part1170_checked

  · exact kid23_part1153_checked

  · exact kid23_part1159_checked

  · exact kid23_part1165_checked

  · exact kid23_part1171_checked

  · exact kid23_part1154_checked

  · exact kid23_part1160_checked

  · exact kid23_part1166_checked

  · exact kid23_part1172_checked

  · exact kid23_part1155_checked

  · exact kid23_part1161_checked

  · exact kid23_part1167_checked

  · exact kid23_part1173_checked

  · exact kid23_part1156_checked

  · exact kid23_part1162_checked

  · exact kid23_part1168_checked

  · exact kid23_part1174_checked

  · exact kid23_part1157_checked

  · exact kid23_part1163_checked

  · exact kid23_part1169_checked

  · exact kid23_part1175_checked

def kid23_part1176 : Audit := .cycle 13 1 false (-1)
theorem kid23_part1176_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part1176) = true := by rfl

def kid23_part1177 : Audit := .cycle 1 10 true (1)
theorem kid23_part1177_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part1177) = true := by rfl

def kid23_part1178 : Audit := .cycle 7 3 true (3)
theorem kid23_part1178_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part1178) = true := by rfl

def kid23_part1179 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 24 8 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 12 8 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 23 1 false (1),
.cycle 6 6 true (2),
.cycle 12 8 true (2),
.cycle 12 10 true (-2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (3)
]),
.cycle 18 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 10 true (2),
.cycle 11 8 true (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 12 8 true (2),
.cycle 3 9 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.cycle 9 10 true (2),
.cycle 11 1 true (5),
.last 18 (4,true),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 12 8 true (2),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 32 1 false (8),
.cycle 7 5 true (3),
.cycle 13 8 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 1 20 true (1),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 12 true (2),
.cycle 12 8 true (2),
.cycle 9 4 true (2),
.last 24 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 8 true (3)
]),
.cycle 18 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 12 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 12 8 true (4),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.last 16 (4,true),
.cycle 6 6 true (2),
.cycle 12 8 true (4),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 8 3 true (3)
])
theorem kid23_part1179_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part1179) = true := by rfl

def kid23_part1180 : Audit := .cycle 0 11 true (0)
theorem kid23_part1180_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part1180) = true := by rfl

def kid23_part1182 : Audit := .cycle 0 11 true (0)
theorem kid23_part1182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part1182) = true := by rfl

def kid23_part1183 : Audit := .cycle 1 10 true (1)
theorem kid23_part1183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part1183) = true := by rfl

def kid23_part1184 : Audit := .cycle 2 9 true (1)
theorem kid23_part1184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part1184) = true := by rfl

def kid23_part1185 : Audit := .cycle 1 13 true (1)
theorem kid23_part1185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part1185) = true := by rfl

def kid23_part1186 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 20 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 23 1 false (1),
.cycle 6 6 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (3)
])
theorem kid23_part1186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part1186) = true := by rfl

def kid23_part1187 : Audit := .cycle 18 1 false (0)
theorem kid23_part1187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part1187) = true := by rfl

def kid23_part1188 : Audit := .cycle 0 11 true (0)
theorem kid23_part1188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part1188) = true := by rfl

def kid23_part1189 : Audit := .cycle 1 10 true (1)
theorem kid23_part1189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part1189) = true := by rfl

def kid23_part1190 : Audit := .cycle 9 10 true (2)
theorem kid23_part1190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part1190) = true := by rfl

def kid23_part1191 : Audit := .split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 18 true (1),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 18 true (2),
.cycle 11 8 true (2),
.cycle 18 1 true (6),
.cycle 1 25 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 9 20 true (2)
])
theorem kid23_part1191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part1191) = true := by rfl

def kid23_part1192 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 19 true (1),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 28 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 9 10 true (2),
.cycle 11 1 true (5),
.cycle 40 1 false (10),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 15 true (1),
.cycle 31 1 false (7),
.cycle 32 1 false (6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part1192) = true := by rfl

def kid23_part1193 : Audit := .split 31 (4,false) (byMove [
.cycle 0 32 true (0),
.cycle 49 1 false (11),
.cycle 33 1 false (7),
.cycle 32 1 false (6),
.cycle 31 1 false (7),
.cycle 32 1 false (6),
.cycle 0 32 true (0),
.cycle 49 1 false (13),
.cycle 33 1 false (9),
.cycle 32 1 false (8),
.cycle 31 1 true (7),
.cycle 32 1 false (8),
.cycle 44 1 false (10),
.last 33 (2,true),
.cycle 0 34 true (0),
.cycle 32 1 false (6),
.cycle 31 1 false (7),
.cycle 32 1 false (6),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 48 1 false (12),
.cycle 1 34 true (0),
.cycle 31 1 true (7),
.cycle 35 1 false (9)
])
theorem kid23_part1193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part1193) = true := by rfl

def kid23_part1194 : Audit := .cycle 7 5 true (3)
theorem kid23_part1194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part1194) = true := by rfl

def kid23_part1195 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 16 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 20 (4,false),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 6 true (2),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 8 5 true (3)
])
theorem kid23_part1195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part1195) = true := by rfl

def kid23_part1196 : Audit := .cycle 0 13 true (0)
theorem kid23_part1196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part1196) = true := by rfl

def kid23_part1197 : Audit := .cycle 4 7 true (1)
theorem kid23_part1197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part1197) = true := by rfl

def kid23_part1198 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 66 1 false (10),
.cycle 7 10 true (2),
.cycle 9 4 true (2),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 3 false (1),
.cycle 8 6 true (3)
])
theorem kid23_part1198_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part1198) = true := by rfl

def kid23_part1199 : Audit := .cycle 18 1 false (0)
theorem kid23_part1199_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part1199) = true := by rfl

def kid23_part1200 : Audit := .cycle 0 11 true (0)
theorem kid23_part1200_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part1200) = true := by rfl

def kid23_part1201 : Audit := .cycle 1 10 true (1)
theorem kid23_part1201_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part1201) = true := by rfl

def kid23_part1202 : Audit := .cycle 2 9 true (1)
theorem kid23_part1202_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part1202) = true := by rfl

def kid23_part1203 : Audit := .cycle 1 13 true (1)
theorem kid23_part1203_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part1203) = true := by rfl

def kid23_part1204 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.cycle 90 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 20 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 6 true (4),
.cycle 6 6 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1204_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part1204) = true := by rfl

def kid23_part1205 : Audit := .cycle 8 3 true (3)
theorem kid23_part1205_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part1205) = true := by rfl

def kid23_part1181 : Audit := .split 10 (4,true) (byMove [(kid23_part1182),(kid23_part1183),(kid23_part1184),(kid23_part1185),(kid23_part1186),(kid23_part1187),(kid23_part1188),(kid23_part1189),(kid23_part1190),(kid23_part1191),(kid23_part1192),(kid23_part1193),(kid23_part1194),(kid23_part1195),(kid23_part1196),(kid23_part1197),(kid23_part1198),(kid23_part1199),(kid23_part1200),(kid23_part1201),(kid23_part1202),(kid23_part1203),(kid23_part1204),(kid23_part1205)])

theorem kid23_part1181_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part1181) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid23_part1182),(kid23_part1183),(kid23_part1184),(kid23_part1185),(kid23_part1186),(kid23_part1187),(kid23_part1188),(kid23_part1189),(kid23_part1190),(kid23_part1191),(kid23_part1192),(kid23_part1193),(kid23_part1194),(kid23_part1195),(kid23_part1196),(kid23_part1197),(kid23_part1198),(kid23_part1199),(kid23_part1200),(kid23_part1201),(kid23_part1202),(kid23_part1203),(kid23_part1204),(kid23_part1205)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1182_checked

  · exact kid23_part1188_checked

  · exact kid23_part1194_checked

  · exact kid23_part1200_checked

  · exact kid23_part1183_checked

  · exact kid23_part1189_checked

  · exact kid23_part1195_checked

  · exact kid23_part1201_checked

  · exact kid23_part1184_checked

  · exact kid23_part1190_checked

  · exact kid23_part1196_checked

  · exact kid23_part1202_checked

  · exact kid23_part1185_checked

  · exact kid23_part1191_checked

  · exact kid23_part1197_checked

  · exact kid23_part1203_checked

  · exact kid23_part1186_checked

  · exact kid23_part1192_checked

  · exact kid23_part1198_checked

  · exact kid23_part1204_checked

  · exact kid23_part1187_checked

  · exact kid23_part1193_checked

  · exact kid23_part1199_checked

  · exact kid23_part1205_checked

def kid23_part1206 : Audit := .cycle 31 1 false (7)
theorem kid23_part1206_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part1206) = true := by rfl

def kid23_part1207 : Audit := .cycle 6 7 true (2)
theorem kid23_part1207_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part1207) = true := by rfl

def kid23_part1208 : Audit := .cycle 9 2 true (2)
theorem kid23_part1208_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part1208) = true := by rfl

def kid23_part1209 : Audit := .split 10 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 7 11 true (0),
.split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.last 20 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.last 18 (4,true),
.last 16 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 19 (4,true),
.last 13 (4,true),
.last 21 (4,true),
.cycle 13 6 false (2),
.last 18 (4,true),
.last 28 (4,true),
.last 16 (4,true),
.last 12 (4,true),
.last 18 (4,true),
.last 16 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 18 (4,true),
.last 13 (4,true),
.last 24 (4,true)
]),
.cycle 20 1 false (0),
.cycle 6 5 true (2),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 64, 39, 64],[2, 32, 4, 1, 64, 5, 64],80⟩,
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 23 1 false (1),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 0 15 true (0),
.cycle 7 11 true (2),
.last 17 (4,false),
.cycle 1 14 true (1),
.cycle 35 1 false (3),
.last 12 (4,false),
.cycle 41 1 false (3),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 1 19 true (1)
]),
.cycle 1 14 true (1),
.cycle 12 4 true (1),
.cycle 15 5 false (1),
.cycle 5 7 true (1),
.cycle 28 1 false (2),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.last 21 (4,true),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.cycle 9 4 true (1),
.cycle 10 2 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 5 9 true (1),
.last 16 (4,true),
.last 18 (4,true),
.last 20 (4,true),
.last 17 (4,true),
.last 12 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 14 (4,true)
]),
.cycle 34 1 false (2),
.cycle 6 5 true (2),
.cycle 7 7 true (2),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 15 (4,false),
.cycle 5 11 true (1),
.last 13 (4,false),
.cycle 7 7 true (2),
.last 13 (4,false),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 0 15 true (0),
.cycle 6 11 true (2),
.cycle 9 4 true (2),
.cycle 10 2 true (2),
.cycle 5 7 true (1),
.last 13 (4,false),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 7 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid23_part1209_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part1209) = true := by rfl

def kid23_part1210 : Audit := .cycle 5 5 true (1)
theorem kid23_part1210_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part1210) = true := by rfl

def kid23_part1212 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.cycle 0 19 true (0),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.last 17 (4,false),
.cycle 12 14 true (2),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 12 15 true (2),
.cycle 12 6 true (1),
.cycle 24 23 true (0),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 12 11 true (2)
])
theorem kid23_part1212_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part1212) = true := by rfl

def kid23_part1213 : Audit := .cycle 1 14 true (1)
theorem kid23_part1213_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part1213) = true := by rfl

def kid23_part1214 : Audit := .split 19 (2,true) (byMove [
.cycle 1 24 true (0),
.cycle 11 10 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 20 1 false (0),
.cycle 31 1 false (3),
.last 25 (4,false),
.cycle 1 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 20 1 false (2),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 35 1 false (3),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 20 1 false (0),
.cycle 17 11 true (1),
.cycle 17 7 true (1),
.cycle 1 22 true (0),
.cycle 35 1 false (3),
.last 20 (4,false),
.last 22 (4,false)
])
theorem kid23_part1214_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part1214) = true := by rfl

def kid23_part1215 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.cycle 0 23 true (0),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.last 19 (4,false),
.cycle 52 1 false (2),
.cycle 0 17 true (0),
.cycle 1 19 true (0),
.last 17 (4,false),
.cycle 7 15 true (0),
.cycle 30 1 false (2),
.cycle 30 1 false (2),
.cycle 5 11 true (0),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 39 1 false (1),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.cycle 7 13 true (0)
])
theorem kid23_part1215_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part1215) = true := by rfl

def kid23_part1216 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.last 21 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 20 (2,true),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 17 1 true (3),
.cycle 14 2 true (-1),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 34 (2,true),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 28 1 true (-2),
.cycle 13 6 false (1)
])
theorem kid23_part1216_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part1216) = true := by rfl

def kid23_part1217 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 12 2 true (-1),
.cycle 12 6 false (0),
.last 15 (2,true),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 23 (2,true),
.cycle 23 1 false (-3),
.last 14 (2,true),
.last 17 (2,true),
.cycle 12 3 false (0),
.cycle 16 1 false (-2)
])
theorem kid23_part1217_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part1217) = true := by rfl

def kid23_part1218 : Audit := .cycle 6 5 true (2)
theorem kid23_part1218_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part1218) = true := by rfl

def kid23_part1219 : Audit := .split 17 (4,false) (byMove [
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 9 19 true (0),
.cycle 39 1 false (3),
.cycle 1 42 true (0),
.cycle 22 1 false (-2),
.cycle 6 12 true (2),
.cycle 11 7 true (3),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 13 5 true (3),
.cycle 16 2 true (3),
.cycle 9 11 true (2),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 9 17 true (0),
.cycle 36 1 false (4),
.cycle 22 1 false (-2),
.cycle 6 12 true (2),
.cycle 11 7 true (3),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 13 5 true (3),
.cycle 9 9 true (2)
])
theorem kid23_part1219_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part1219) = true := by rfl

def kid23_part1220 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 1 12 true (1),
.last 15 (4,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131076, 262144, 262148, 8192, 16384, 8, 128, 262144, 262148, 128, 256, 8, 128, 262144, 4, 262144],[128, 2048, 4, 1, 4, 262144, 8192, 131072, 4, 1, 4, 4, 128, 2048, 4, 1, 4, 4, 262144],330800⟩,
.cycle 0 13 true (0),
.last 47 (4,false),
.last 13 (4,false),
.cycle 7 11 true (2),
.cycle 9 6 true (2),
.cycle 1 14 true (1),
.cycle 35 1 false (3),
.last 12 (4,false),
.last 15 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 23 (4,false),
.last 17 (4,false)
])
theorem kid23_part1220_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part1220) = true := by rfl

def kid23_part1221 : Audit := .cycle 1 12 true (1)
theorem kid23_part1221_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part1221) = true := by rfl

def kid23_part1222 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 15 true (0),
.cycle 47 1 false (5),
.cycle 19 1 false (1),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131088, 4, 262160, 8192, 16384, 8, 128, 4, 262160, 128, 256, 8, 128, 4, 16, 262144],[128, 2048, 262144, 1, 16, 262144, 8192, 131072, 262144, 1, 16, 16, 128, 2048, 262144, 1, 16, 16, 262144],264224⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 8, 51, 64],[2, 32, 64, 1, 16, 17, 64],64⟩,
.cycle 13 1 true (5),
.cycle 20 2 true (-1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 13 true (0),
.cycle 24 1 false (6),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 9 8 true (2)
])
theorem kid23_part1222_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part1222) = true := by rfl

def kid23_part1223 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.last 23 (2,true),
.last 17 (2,true),
.cycle 15 1 false (1),
.cycle 16 1 false (-2),
.cycle 6 7 true (2),
.cycle 11 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 40 1 false (6),
.cycle 11 2 true (2),
.cycle 14 6 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 16 1 false (0),
.cycle 16 1 false (-2),
.cycle 6 7 true (2),
.cycle 7 11 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 10 13 true (2),
.cycle 9 4 true (2)
])
theorem kid23_part1223_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part1223) = true := by rfl

def kid23_part1224 : Audit := .cycle 12 4 true (1)
theorem kid23_part1224_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part1224) = true := by rfl

def kid23_part1225 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 9 10 true (1),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 6 7 true (1),
.last 21 (4,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 131076, 262144, 262148, 8192, 16384, 8, 128, 262144, 262148, 128, 256, 8, 128, 262144, 4, 262144],[128, 2048, 4, 1, 4, 262144, 8192, 131072, 4, 1, 4, 4, 128, 2048, 4, 1, 4, 4, 262144],330800⟩,
.cycle 1 14 true (1),
.last 19 (4,false),
.last 14 (4,false),
.cycle 17 9 false (2),
.cycle 16 5 false (1),
.cycle 13 12 true (-1),
.cycle 9 10 true (1),
.cycle 16 3 false (0),
.last 18 (4,false),
.cycle 16 15 false (4),
.cycle 16 11 false (3),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 16 9 false (2),
.cycle 16 7 false (2)
])
theorem kid23_part1225_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part1225) = true := by rfl

def kid23_part1226 : Audit := .cycle 5 7 true (1)
theorem kid23_part1226_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part1226) = true := by rfl

def kid23_part1227 : Audit := .cycle 28 1 false (2)
theorem kid23_part1227_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part1227) = true := by rfl

def kid23_part1228 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 32 9 true (0),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 6 true (1),
.cycle 9 4 true (1),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 10 2 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 16 7 false (2),
.cycle 15 5 false (1),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 13 3 false (1),
.cycle 14 3 false (0)
])
theorem kid23_part1228_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part1228) = true := by rfl

def kid23_part1229 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 107 1 false (-5),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 6 true (-1),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 34 1 false (2),
.cycle 15 1 false (-1),
.cycle 12 2 true (-1),
.cycle 12 6 false (0),
.last 15 (2,true),
.cycle 12 8 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 20 1 false (-2),
.cycle 12 5 false (1),
.last 14 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 8, 35, 64],[2, 32, 64, 1, 35, 35, 64],64⟩,
.cycle 12 3 false (0),
.cycle 16 1 false (-2)
])
theorem kid23_part1229_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part1229) = true := by rfl

def kid23_part1230 : Audit := .cycle 6 5 true (2)
theorem kid23_part1230_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part1230) = true := by rfl

def kid23_part1231 : Audit := .cycle 7 7 true (2)
theorem kid23_part1231_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part1231) = true := by rfl

def kid23_part1232 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 15 (4,false),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 1 12 true (1),
.last 15 (4,false),
.cycle 9 12 true (2),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 13 (4,false),
.cycle 6 11 true (2),
.cycle 9 4 true (2),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.cycle 8 7 true (2)
])
theorem kid23_part1232_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part1232) = true := by rfl

def kid23_part1233 : Audit := .cycle 1 12 true (1)
theorem kid23_part1233_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part1233) = true := by rfl

def kid23_part1234 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 11 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 11 true (3),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 10 8 true (2),
.cycle 6 8 true (2),
.cycle 11 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.cycle 9 5 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2)
])
theorem kid23_part1234_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part1234) = true := by rfl

def kid23_part1235 : Audit := .cycle 9 2 true (2)
theorem kid23_part1235_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part1235) = true := by rfl

def kid23_part1211 : Audit := .split 10 (4,true) (byMove [(kid23_part1212),(kid23_part1213),(kid23_part1214),(kid23_part1215),(kid23_part1216),(kid23_part1217),(kid23_part1218),(kid23_part1219),(kid23_part1220),(kid23_part1221),(kid23_part1222),(kid23_part1223),(kid23_part1224),(kid23_part1225),(kid23_part1226),(kid23_part1227),(kid23_part1228),(kid23_part1229),(kid23_part1230),(kid23_part1231),(kid23_part1232),(kid23_part1233),(kid23_part1234),(kid23_part1235)])

theorem kid23_part1211_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part1211) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part1212),(kid23_part1213),(kid23_part1214),(kid23_part1215),(kid23_part1216),(kid23_part1217),(kid23_part1218),(kid23_part1219),(kid23_part1220),(kid23_part1221),(kid23_part1222),(kid23_part1223),(kid23_part1224),(kid23_part1225),(kid23_part1226),(kid23_part1227),(kid23_part1228),(kid23_part1229),(kid23_part1230),(kid23_part1231),(kid23_part1232),(kid23_part1233),(kid23_part1234),(kid23_part1235)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1212_checked

  · exact kid23_part1218_checked

  · exact kid23_part1224_checked

  · exact kid23_part1230_checked

  · exact kid23_part1213_checked

  · exact kid23_part1219_checked

  · exact kid23_part1225_checked

  · exact kid23_part1231_checked

  · exact kid23_part1214_checked

  · exact kid23_part1220_checked

  · exact kid23_part1226_checked

  · exact kid23_part1232_checked

  · exact kid23_part1215_checked

  · exact kid23_part1221_checked

  · exact kid23_part1227_checked

  · exact kid23_part1233_checked

  · exact kid23_part1216_checked

  · exact kid23_part1222_checked

  · exact kid23_part1228_checked

  · exact kid23_part1234_checked

  · exact kid23_part1217_checked

  · exact kid23_part1223_checked

  · exact kid23_part1229_checked

  · exact kid23_part1235_checked

def kid23_part1236 : Audit := .cycle 13 1 false (-1)
theorem kid23_part1236_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part1236) = true := by rfl

def kid23_part1237 : Audit := .cycle 1 10 true (1)
theorem kid23_part1237_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part1237) = true := by rfl

def kid23_part1238 : Audit := .cycle 7 3 true (3)
theorem kid23_part1238_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part1238) = true := by rfl

def kid23_part1239 : Audit := .split 10 (2,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 23 1 false (1),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.last 13 (4,false),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (3)
]),
.cycle 2 10 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 17 true (1),
.cycle 3 8 true (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (3),
.cycle 2 17 true (1),
.cycle 11 1 true (5),
.last 17 (4,true),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 2 14 true (1),
.cycle 6 5 true (2),
.cycle 2 11 true (1),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 1 20 true (1),
.last 13 (4,false),
.cycle 7 7 true (2),
.last 13 (4,false),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 2 11 true (1),
.cycle 2 13 true (1),
.cycle 9 4 true (2),
.last 13 (4,false),
.cycle 5 7 true (1),
.last 13 (4,false),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 2 11 true (1)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.last 16 (4,true),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
]),
.cycle 8 3 true (3)
])
theorem kid23_part1239_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part1239) = true := by rfl

def kid23_part1240 : Audit := .cycle 0 11 true (0)
theorem kid23_part1240_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part1240) = true := by rfl

def kid23_part1242 : Audit := .cycle 1 11 true (1)
theorem kid23_part1242_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part1242) = true := by rfl

def kid23_part1243 : Audit := .cycle 7 4 true (3)
theorem kid23_part1243_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part1243) = true := by rfl

def kid23_part1244 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 23 1 false (1),
.cycle 6 6 true (2),
.last 14 (4,false),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 20 (4,false),
.cycle 19 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 8 4 true (3)
])
theorem kid23_part1244_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part1244) = true := by rfl

def kid23_part1245 : Audit := .cycle 0 12 true (0)
theorem kid23_part1245_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part1245) = true := by rfl

def kid23_part1246 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 17 13 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 13 9 true (0),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 20 1 false (0),
.cycle 15 8 false (2),
.cycle 13 3 true (0),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 17 5 false (1)
])
theorem kid23_part1246_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part1246) = true := by rfl

def kid23_part1247 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 9 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 8 true (3),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 23 1 false (-1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3)
])
theorem kid23_part1247_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part1247) = true := by rfl

def kid23_part1248 : Audit := .cycle 0 11 true (0)
theorem kid23_part1248_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part1248) = true := by rfl

def kid23_part1249 : Audit := .cycle 1 10 true (1)
theorem kid23_part1249_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part1249) = true := by rfl

def kid23_part1250 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 10 true (3),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.last 24 (2,true),
.cycle 6 14 true (2),
.cycle 17 3 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 21 (2,true),
.cycle 9 11 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (3)
])
theorem kid23_part1250_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part1250) = true := by rfl

def kid23_part1251 : Audit := .cycle 3 8 true (1)
theorem kid23_part1251_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part1251) = true := by rfl

def kid23_part1252 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 11 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 40 1 false (8),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1252_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part1252) = true := by rfl

def kid23_part1253 : Audit := .split 16 (4,false) (byMove [
.cycle 1 17 true (1),
.cycle 7 10 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 9 14 true (3),
.cycle 15 2 true (5),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 15 9 true (5),
.cycle 3 14 true (1),
.cycle 16 1 true (6),
.cycle 11 6 true (3),
.cycle 6 11 true (2),
.cycle 15 3 true (5),
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 14 3 true (4),
.cycle 9 8 true (3),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 16 1 true (6),
.cycle 8 9 true (3)
])
theorem kid23_part1253_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part1253) = true := by rfl

def kid23_part1254 : Audit := .cycle 6 5 true (2)
theorem kid23_part1254_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part1254) = true := by rfl

def kid23_part1255 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (3),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 9 10 true (3),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 9 7 true (3),
.cycle 9 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3)
])
theorem kid23_part1255_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part1255) = true := by rfl

def kid23_part1256 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 7 9 true (1),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 12 true (2),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 13 (4,false),
.last 15 (4,false),
.cycle 9 4 true (2),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 5 9 true (1),
.cycle 19 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 13 (4,false)
])
theorem kid23_part1256_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part1256) = true := by rfl

def kid23_part1257 : Audit := .cycle 1 12 true (1)
theorem kid23_part1257_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part1257) = true := by rfl

def kid23_part1258 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 25 15 true (-1),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 2 true (0),
.cycle 0 18 true (0),
.cycle 9 6 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.cycle 11 4 true (1),
.cycle 15 8 false (3),
.last 21 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 18 true (0),
.cycle 17 7 false (3),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.cycle 16 5 false (2)
])
theorem kid23_part1258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part1258) = true := by rfl

def kid23_part1259 : Audit := .cycle 9 2 true (3)
theorem kid23_part1259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part1259) = true := by rfl

def kid23_part1260 : Audit := .cycle 0 11 true (0)
theorem kid23_part1260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part1260) = true := by rfl

def kid23_part1261 : Audit := .cycle 1 10 true (1)
theorem kid23_part1261_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part1261) = true := by rfl

def kid23_part1262 : Audit := .cycle 2 9 true (1)
theorem kid23_part1262_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part1262) = true := by rfl

def kid23_part1263 : Audit := .cycle 1 13 true (1)
theorem kid23_part1263_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part1263) = true := by rfl

def kid23_part1264 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.cycle 11 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 9 true (4),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 6 true (4),
.cycle 6 6 true (2),
.cycle 11 3 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 8 4 true (3)
])
theorem kid23_part1264_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part1264) = true := by rfl

def kid23_part1265 : Audit := .cycle 8 3 true (3)
theorem kid23_part1265_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part1265) = true := by rfl

def kid23_part1241 : Audit := .split 10 (4,true) (byMove [(kid23_part1242),(kid23_part1243),(kid23_part1244),(kid23_part1245),(kid23_part1246),(kid23_part1247),(kid23_part1248),(kid23_part1249),(kid23_part1250),(kid23_part1251),(kid23_part1252),(kid23_part1253),(kid23_part1254),(kid23_part1255),(kid23_part1256),(kid23_part1257),(kid23_part1258),(kid23_part1259),(kid23_part1260),(kid23_part1261),(kid23_part1262),(kid23_part1263),(kid23_part1264),(kid23_part1265)])

theorem kid23_part1241_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part1241) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid23_part1242),(kid23_part1243),(kid23_part1244),(kid23_part1245),(kid23_part1246),(kid23_part1247),(kid23_part1248),(kid23_part1249),(kid23_part1250),(kid23_part1251),(kid23_part1252),(kid23_part1253),(kid23_part1254),(kid23_part1255),(kid23_part1256),(kid23_part1257),(kid23_part1258),(kid23_part1259),(kid23_part1260),(kid23_part1261),(kid23_part1262),(kid23_part1263),(kid23_part1264),(kid23_part1265)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1242_checked

  · exact kid23_part1248_checked

  · exact kid23_part1254_checked

  · exact kid23_part1260_checked

  · exact kid23_part1243_checked

  · exact kid23_part1249_checked

  · exact kid23_part1255_checked

  · exact kid23_part1261_checked

  · exact kid23_part1244_checked

  · exact kid23_part1250_checked

  · exact kid23_part1256_checked

  · exact kid23_part1262_checked

  · exact kid23_part1245_checked

  · exact kid23_part1251_checked

  · exact kid23_part1257_checked

  · exact kid23_part1263_checked

  · exact kid23_part1246_checked

  · exact kid23_part1252_checked

  · exact kid23_part1258_checked

  · exact kid23_part1264_checked

  · exact kid23_part1247_checked

  · exact kid23_part1253_checked

  · exact kid23_part1259_checked

  · exact kid23_part1265_checked

def kid23_part1266 : Audit := .cycle 8 3 true (3)
theorem kid23_part1266_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part1266) = true := by rfl

def kid23_part1146 : Audit := .split 9 (5,true) (byMove [(kid23_part1147),(kid23_part1148),(kid23_part1149),(kid23_part1150),(kid23_part1151),(kid23_part1176),(kid23_part1177),(kid23_part1178),(kid23_part1179),(kid23_part1180),(kid23_part1181),(kid23_part1206),(kid23_part1207),(kid23_part1208),(kid23_part1209),(kid23_part1210),(kid23_part1211),(kid23_part1236),(kid23_part1237),(kid23_part1238),(kid23_part1239),(kid23_part1240),(kid23_part1241),(kid23_part1266)])

theorem kid23_part1146_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (kid23_part1146) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) 9 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part1147),(kid23_part1148),(kid23_part1149),(kid23_part1150),(kid23_part1151),(kid23_part1176),(kid23_part1177),(kid23_part1178),(kid23_part1179),(kid23_part1180),(kid23_part1181),(kid23_part1206),(kid23_part1207),(kid23_part1208),(kid23_part1209),(kid23_part1210),(kid23_part1211),(kid23_part1236),(kid23_part1237),(kid23_part1238),(kid23_part1239),(kid23_part1240),(kid23_part1241),(kid23_part1266)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1147_checked

  · exact kid23_part1177_checked

  · exact kid23_part1207_checked

  · exact kid23_part1237_checked

  · exact kid23_part1148_checked

  · exact kid23_part1178_checked

  · exact kid23_part1208_checked

  · exact kid23_part1238_checked

  · exact kid23_part1149_checked

  · exact kid23_part1179_checked

  · exact kid23_part1209_checked

  · exact kid23_part1239_checked

  · exact kid23_part1150_checked

  · exact kid23_part1180_checked

  · exact kid23_part1210_checked

  · exact kid23_part1240_checked

  · exact kid23_part1151_checked

  · exact kid23_part1181_checked

  · exact kid23_part1211_checked

  · exact kid23_part1241_checked

  · exact kid23_part1176_checked

  · exact kid23_part1206_checked

  · exact kid23_part1236_checked

  · exact kid23_part1266_checked

def kid23_part1267 : Audit := .cycle 0 9 true (0)
theorem kid23_part1267_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,0⟩)) (kid23_part1267) = true := by rfl

def kid23_part1268 : Audit := .cycle 1 8 true (1)
theorem kid23_part1268_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,1⟩)) (kid23_part1268) = true := by rfl

def kid23_part1269 : Audit := .cycle 2 7 true (1)
theorem kid23_part1269_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,2⟩)) (kid23_part1269) = true := by rfl

def kid23_part1270 : Audit := .cycle 1 11 true (1)
theorem kid23_part1270_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,3⟩)) (kid23_part1270) = true := by rfl

def kid23_part1272 : Audit := .cycle 1 10 true (1)
theorem kid23_part1272_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid23_part1272) = true := by rfl

def kid23_part1273 : Audit := .cycle 7 3 true (3)
theorem kid23_part1273_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid23_part1273) = true := by rfl

def kid23_part1274 : Audit := .split 10 (2,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 17 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 21 1 false (-1),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 17 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 21 1 false (-1),
.cycle 8 4 true (3)
]),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 17 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 29 3 false (2),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 23 3 false (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 21 3 false (1),
.cycle 8 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 10 9 true (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 52 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.cycle 2 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 42, 16, 64],[2, 32, 4, 1, 64, 32, 64],64⟩,
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 47, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 1 20 true (1),
.last 19 (4,true),
.last 22 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 10 true (3),
.cycle 8 11 true (3)
]),
.cycle 3 8 true (1),
.cycle 2 10 true (1),
.cycle 8 3 true (4),
.cycle 6 5 true (2),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 21 5 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 8 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 10 7 true (3),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 8 5 true (3)
]),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 7 8 true (2),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 17 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.last 21 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 17 1 false (-1),
.cycle 5 7 true (1),
.cycle 17 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true)
]),
.split 11 (5,true) (byMove [
.cycle 10 4 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 21 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 17 (4,true),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 14 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 5 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid23_part1274_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid23_part1274) = true := by rfl

def kid23_part1275 : Audit := .cycle 0 11 true (0)
theorem kid23_part1275_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid23_part1275) = true := by rfl

def kid23_part1276 : Audit := .split 10 (4,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 29 1 false (1),
.cycle 2 13 true (1),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 19 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 33 1 false (1),
.cycle 8 4 true (3)
]),
.cycle 0 12 true (0),
.cycle 15 1 false (-1),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 29 3 false (2),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 17 1 false (-1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 21 3 false (1),
.cycle 8 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 10 9 true (3),
.cycle 52 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.cycle 9 11 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 62, 16, 64],[2, 32, 64, 1, 4, 32, 64],64⟩,
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.last 20 (2,true),
.last 23 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 10 true (3),
.cycle 8 11 true (3)
]),
.cycle 3 8 true (1),
.cycle 21 1 false (1),
.cycle 8 3 true (4),
.cycle 6 5 true (2),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 18 (2,true),
.last 25 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 22 (2,true),
.last 17 (2,true),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 18 (2,true),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 8 5 true (3)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 10 4 true (2),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 7 9 true (1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 5 9 true (1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true)
]),
.cycle 1 12 true (1),
.cycle 15 1 false (-1),
.split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 10 4 true (2),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 20 1 false (-2),
.cycle 15 6 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 4 true (3),
.cycle 10 7 true (3),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 20 1 false (-2),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 8 5 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid23_part1276_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid23_part1276) = true := by rfl

def kid23_part1277 : Audit := .split 10 (5,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.cycle 41 1 false (1),
.cycle 2 13 true (1),
.cycle 6 6 true (2),
.cycle 19 5 false (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 23 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 33 1 false (1),
.cycle 8 4 true (3)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 4 false (1),
.cycle 13 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.cycle 21 4 false (1),
.cycle 17 4 false (1),
.cycle 6 6 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 13 4 false (1),
.cycle 13 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 17 4 false (1),
.cycle 8 4 true (3)
]),
.cycle 16 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 10 8 true (3),
.cycle 3 8 true (1),
.cycle 8 4 true (4),
.cycle 8 3 true (4),
.cycle 6 5 true (2),
.cycle 10 2 true (3),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 14 (4,true),
.last 20 (4,true),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 10, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 19 5 false (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (3)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 7 8 true (2),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 13 4 false (1),
.cycle 13 4 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 19 4 false (1),
.cycle 15 4 false (1),
.cycle 10 4 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 13 4 false (1),
.cycle 13 4 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 10 2 true (3)
]),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 63, 16, 64],[2, 32, 64, 1, 24, 59, 64],64⟩,
.last 15 (2,true),
.cycle 10 8 true (1),
.cycle 15 7 false (1),
.cycle 16 3 false (0),
.cycle 6 9 true (1),
.cycle 16 7 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 0, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 18 5 true (3),
.cycle 18 7 false (2),
.cycle 17 5 false (1),
.last 15 (2,true),
.cycle 10 8 true (1),
.cycle 15 7 false (1),
.cycle 16 3 false (0),
.cycle 20 9 false (4),
.cycle 17 7 false (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 0, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 16 5 false (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid23_part1277_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid23_part1277) = true := by rfl

def kid23_part1278 : Audit := .cycle 0 10 true (0)
theorem kid23_part1278_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid23_part1278) = true := by rfl

def kid23_part1279 : Audit := .cycle 1 9 true (1)
theorem kid23_part1279_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid23_part1279) = true := by rfl

def kid23_part1280 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 2 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 9 true (4),
.cycle 3 16 true (1),
.last 47 (4,true),
.cycle 8 11 true (4),
.cycle 6 13 true (2),
.cycle 37 5 false (1),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 19 (4,true),
.cycle 49 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 10 true (4),
.cycle 8 11 true (4)
]),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 56 1 false (2),
.cycle 56 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 9 true (4),
.cycle 3 16 true (1),
.last 31 (2,true),
.cycle 8 11 true (4),
.cycle 6 13 true (2),
.last 23 (2,true),
.last 19 (2,true),
.cycle 1 20 true (1),
.last 21 (2,true),
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 10 true (4),
.cycle 8 11 true (4)
]),
.cycle 8 12 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 8 true (4),
.cycle 3 15 true (1),
.split 28 (4,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 9 20 true (4),
.cycle 8 21 true (4),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 19 10 true (6),
.cycle 11 18 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 21 true (4),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 4 25 true (1),
.last 30 (2,true),
.cycle 27 4 true (9),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 9 20 true (4),
.cycle 8 21 true (4)
]),
.cycle 8 10 true (4),
.cycle 6 12 true (2),
.cycle 16 2 true (6),
.split 18 (2,true) (byMove [
.cycle 1 22 true (1),
.last 21 (4,true),
.last 27 (4,true),
.cycle 7 14 true (3),
.last 19 (4,true),
.cycle 7 16 true (3),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 4, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 0 22 true (0),
.cycle 15 4 true (5),
.cycle 37 5 false (1),
.cycle 5 16 true (1),
.cycle 5 14 true (1),
.last 19 (4,true),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 17 2 true (6)
]),
.cycle 1 19 true (1),
.split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 7 15 true (3),
.last 19 (2,true),
.cycle 7 14 true (3),
.cycle 56 1 false (2),
.last 21 (2,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 2048, 4096, 1, 16, 4096, 128, 2048, 4096, 1, 16, 16, 4096],4096⟩,
.last 21 (2,true),
.cycle 15 4 true (5),
.last 23 (2,true),
.last 19 (2,true),
.cycle 5 14 true (1),
.last 21 (2,true),
.last 21 (2,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 9 11 true (4),
.cycle 17 2 true (6)
]),
.split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 7 21 true (3),
.last 22 (2,true),
.cycle 16 8 true (4),
.cycle 41 1 false (1),
.cycle 28 3 false (0),
.cycle 6 16 true (2),
.cycle 7 20 true (3),
.last 22 (2,true),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 20 true (4),
.cycle 34 7 false (2),
.cycle 31 5 false (1),
.last 22 (2,true),
.cycle 14 8 true (4),
.last 26 (2,true),
.cycle 28 3 false (0),
.cycle 6 16 true (2),
.cycle 33 7 false (3),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 9 15 true (4),
.cycle 30 5 false (2)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (4),
.cycle 8 10 true (4)
])
theorem kid23_part1280_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid23_part1280) = true := by rfl

def kid23_part1281 : Audit := .cycle 3 7 true (1)
theorem kid23_part1281_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid23_part1281) = true := by rfl

def kid23_part1282 : Audit := .cycle 9 1 true (5)
theorem kid23_part1282_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid23_part1282) = true := by rfl

def kid23_part1283 : Audit := .cycle 8 2 true (4)
theorem kid23_part1283_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid23_part1283) = true := by rfl

def kid23_part1284 : Audit := .cycle 6 4 true (2)
theorem kid23_part1284_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid23_part1284) = true := by rfl

def kid23_part1285 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 9 true (3),
.cycle 3 10 true (1),
.cycle 12 3 true (4),
.cycle 8 5 true (4),
.cycle 6 7 true (2),
.cycle 23 5 false (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (4),
.cycle 8 5 true (4)
]),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 21 (2,true),
.last 23 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 9 true (3),
.cycle 3 10 true (1),
.last 15 (2,true),
.cycle 8 5 true (4),
.cycle 6 7 true (2),
.last 20 (2,true),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 21 (2,true),
.last 24 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (4),
.cycle 8 5 true (4)
]),
.cycle 19 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 8 true (4),
.cycle 3 9 true (1),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 37 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 11 4 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (4),
.cycle 3 12 true (1),
.cycle 12 3 true (5),
.cycle 8 7 true (4),
.cycle 6 9 true (2),
.cycle 10 5 true (4),
.last 24 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (4),
.cycle 8 7 true (4)
]),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 10 2 true (4),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.last 13 (4,true),
.last 33 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 5, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 10 4 true (3),
.cycle 23 5 false (1),
.cycle 5 18 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (4)
]),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 7 9 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.last 21 (2,true),
.last 23 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 16 (2,true),
.last 26 (2,true),
.cycle 10 4 true (3),
.last 20 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.last 21 (2,true),
.last 24 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 5 true (4),
.cycle 11 2 true (4)
]),
.split 16 (4,true) (byMove [
.last 19 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 3072, 4096, 1024, 128, 256, 8, 128, 1024, 1024, 4096],[128, 2048, 4096, 1, 8, 1024, 128, 2048, 4096, 1, 1024, 1024, 4096],4112⟩,
.last 17 (2,true),
.cycle 12 8 true (1),
.last 21 (2,true),
.cycle 18 3 false (0),
.cycle 6 18 true (1),
.cycle 18 14 true (2),
.last 17 (2,true),
.cycle 5 12 true (1),
.last 22 (2,true),
.cycle 20 10 true (3),
.cycle 20 7 false (2),
.cycle 19 5 false (1),
.last 17 (2,true),
.cycle 12 8 true (1),
.last 21 (2,true),
.cycle 18 3 false (0),
.cycle 20 9 false (4),
.cycle 19 7 false (3),
.last 17 (2,true),
.cycle 5 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 3072, 4096, 1024, 128, 256, 8, 128, 1024, 1024, 4096],[128, 2048, 4096, 1, 1024, 1024, 128, 2048, 4096, 1, 1024, 1024, 4096],4112⟩,
.cycle 18 5 false (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1285_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid23_part1285) = true := by rfl

def kid23_part1287 : Audit := .cycle 1 14 true (1)
theorem kid23_part1287_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid23_part1287) = true := by rfl

def kid23_part1288 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 7 8 true (3),
.cycle 0 15 true (0),
.cycle 0 22 true (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 0 20 true (0),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 10 4 true (3),
.cycle 1 15 true (1),
.last 24 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid23_part1288) = true := by rfl

def kid23_part1289 : Audit := .cycle 25 1 false (1)
theorem kid23_part1289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid23_part1289) = true := by rfl

def kid23_part1290 : Audit := .cycle 7 6 true (3)
theorem kid23_part1290_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid23_part1290) = true := by rfl

def kid23_part1291 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.last 24 (5,true),
.cycle 0 46 true (-2),
.cycle 0 18 true (0),
.cycle 0 46 true (-2),
.last 12 (5,true),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 1 15 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 393216, 1, 1024, 8192, 16384, 8, 131200, 133121, 65536, 8192, 16384, 512, 8320, 2080, 65536, 262144],[128, 2048, 65664, 1, 32, 262144, 8192, 131072, 66560, 1, 32, 262144, 8192, 131072, 66560, 64, 2048, 262144, 262144],262414⟩,
.cycle 6 10 true (2),
.last 13 (5,true),
.cycle 14 10 true (-2),
.cycle 1 18 true (1),
.last 20 (5,true),
.last 12 (5,true),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 50 (5,true),
.cycle 8 6 true (3)
])
theorem kid23_part1291_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid23_part1291) = true := by rfl

def kid23_part1292 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 27 (4,true),
.cycle 18 1 false (0),
.cycle 0 18 true (0),
.last 12 (4,true),
.cycle 17 3 false (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 3 15 true (1),
.cycle 1 15 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 11 2 true (2),
.last 29 (4,true),
.cycle 1 18 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 21 3 false (1),
.last 13 (4,true)
])
theorem kid23_part1292_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid23_part1292) = true := by rfl

def kid23_part1293 : Audit := .cycle 1 11 true (1)
theorem kid23_part1293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid23_part1293) = true := by rfl

def kid23_part1294 : Audit := .cycle 7 4 true (3)
theorem kid23_part1294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid23_part1294) = true := by rfl

def kid23_part1295 : Audit := .split 20 (5,true) (byMove [
.cycle 1 32 true (1),
.last 23 (4,true),
.cycle 0 24 true (0),
.cycle 7 16 true (3),
.last 21 (4,true),
.cycle 59 1 false (3),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 11 10 true (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 5, 16, 64],[2, 32, 4, 1, 64, 32, 64],64⟩,
.cycle 6 18 true (2),
.cycle 19 2 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 39, 5, 16, 64],[2, 32, 4, 1, 64, 5, 64],64⟩,
.cycle 5 16 true (1),
.last 21 (4,true),
.last 24 (4,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 2 28 true (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 14 true (3)
])
theorem kid23_part1295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid23_part1295) = true := by rfl

def kid23_part1296 : Audit := .cycle 0 12 true (0)
theorem kid23_part1296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid23_part1296) = true := by rfl

def kid23_part1297 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 23 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid23_part1297) = true := by rfl

def kid23_part1298 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 5, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 3 16 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 24 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid23_part1298) = true := by rfl

def kid23_part1299 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 21 8 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 8 true (3),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 12 6 true (4),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 10 4 true (3),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 18 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid23_part1299) = true := by rfl

def kid23_part1300 : Audit := .split 12 (5,true) (byMove [
.cycle 1 18 true (1),
.last 15 (4,true),
.cycle 21 5 false (1),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 17 8 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 16 8 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 8 true (3),
.cycle 6 10 true (2),
.cycle 11 2 true (3),
.cycle 21 5 false (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (3)
])
theorem kid23_part1300_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid23_part1300) = true := by rfl

def kid23_part1301 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (1),
.cycle 1 22 true (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 1 25 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 14 8 true (2),
.cycle 3 15 true (1),
.cycle 0 21 true (0),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 16, 64],[2, 32, 35, 1, 64, 32, 64],64⟩,
.cycle 16 2 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.last 18 (4,true),
.last 21 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 16, 64],[2, 32, 35, 1, 64, 32, 64],64⟩
])
theorem kid23_part1301_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid23_part1301) = true := by rfl

def kid23_part1302 : Audit := .cycle 5 6 true (1)
theorem kid23_part1302_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid23_part1302) = true := by rfl

def kid23_part1303 : Audit := .split 11 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 7 11 true (2),
.last 20 (5,true),
.last 15 (5,true),
.cycle 22 8 true (-2),
.last 12 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.last 22 (5,true),
.cycle 1 13 true (1),
.cycle 0 17 true (0),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.last 12 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 10 2 true (3),
.cycle 1 13 true (1),
.cycle 9 5 true (3),
.last 12 (5,true)
])
theorem kid23_part1303_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid23_part1303) = true := by rfl

def kid23_part1304 : Audit := .split 11 (5,true) (byMove [
.cycle 10 4 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.last 12 (4,true),
.last 21 (4,true),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 18 (4,true),
.cycle 6 12 true (2),
.cycle 11 2 true (2),
.last 14 (4,true),
.cycle 1 17 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.cycle 10 2 true (3),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 8 6 true (3)
])
theorem kid23_part1304_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid23_part1304) = true := by rfl

def kid23_part1305 : Audit := .cycle 1 11 true (1)
theorem kid23_part1305_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid23_part1305) = true := by rfl

def kid23_part1306 : Audit := .cycle 7 4 true (3)
theorem kid23_part1306_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid23_part1306) = true := by rfl

def kid23_part1307 : Audit := .cycle 2 10 true (1)
theorem kid23_part1307_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid23_part1307) = true := by rfl

def kid23_part1308 : Audit := .cycle 0 12 true (0)
theorem kid23_part1308_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid23_part1308) = true := by rfl

def kid23_part1309 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (4),
.cycle 0 13 true (0),
.cycle 0 22 true (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 24 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1309_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid23_part1309) = true := by rfl

def kid23_part1310 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 19 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (4),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 11 2 true (4),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1310_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid23_part1310) = true := by rfl

def kid23_part1286 : Audit := .split 10 (2,true) (byMove [(kid23_part1287),(kid23_part1288),(kid23_part1289),(kid23_part1290),(kid23_part1291),(kid23_part1292),(kid23_part1293),(kid23_part1294),(kid23_part1295),(kid23_part1296),(kid23_part1297),(kid23_part1298),(kid23_part1299),(kid23_part1300),(kid23_part1301),(kid23_part1302),(kid23_part1303),(kid23_part1304),(kid23_part1305),(kid23_part1306),(kid23_part1307),(kid23_part1308),(kid23_part1309),(kid23_part1310)])

theorem kid23_part1286_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid23_part1286) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid23_part1287),(kid23_part1288),(kid23_part1289),(kid23_part1290),(kid23_part1291),(kid23_part1292),(kid23_part1293),(kid23_part1294),(kid23_part1295),(kid23_part1296),(kid23_part1297),(kid23_part1298),(kid23_part1299),(kid23_part1300),(kid23_part1301),(kid23_part1302),(kid23_part1303),(kid23_part1304),(kid23_part1305),(kid23_part1306),(kid23_part1307),(kid23_part1308),(kid23_part1309),(kid23_part1310)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1287_checked

  · exact kid23_part1293_checked

  · exact kid23_part1299_checked

  · exact kid23_part1305_checked

  · exact kid23_part1288_checked

  · exact kid23_part1294_checked

  · exact kid23_part1300_checked

  · exact kid23_part1306_checked

  · exact kid23_part1289_checked

  · exact kid23_part1295_checked

  · exact kid23_part1301_checked

  · exact kid23_part1307_checked

  · exact kid23_part1290_checked

  · exact kid23_part1296_checked

  · exact kid23_part1302_checked

  · exact kid23_part1308_checked

  · exact kid23_part1291_checked

  · exact kid23_part1297_checked

  · exact kid23_part1303_checked

  · exact kid23_part1309_checked

  · exact kid23_part1292_checked

  · exact kid23_part1298_checked

  · exact kid23_part1304_checked

  · exact kid23_part1310_checked

def kid23_part1311 : Audit := .cycle 1 11 true (1)
theorem kid23_part1311_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid23_part1311) = true := by rfl

def kid23_part1313 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 21 true (0),
.cycle 12 6 true (4),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 21 (5,true),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1313_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid23_part1313) = true := by rfl

def kid23_part1314 : Audit := .cycle 7 7 true (3)
theorem kid23_part1314_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid23_part1314) = true := by rfl

def kid23_part1315 : Audit := .split 11 (2,true) (byMove [
.cycle 0 16 true (0),
.last 24 (5,true),
.cycle 25 1 false (1),
.cycle 0 17 true (0),
.cycle 25 1 false (1),
.last 12 (5,true),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.last 17 (5,true),
.last 21 (5,true),
.last 25 (5,true),
.cycle 6 11 true (2),
.last 13 (5,true),
.cycle 5 16 true (1),
.cycle 1 17 true (1),
.last 19 (5,true),
.last 12 (5,true),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 23 (5,true),
.cycle 8 7 true (3)
])
theorem kid23_part1315_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid23_part1315) = true := by rfl

def kid23_part1316 : Audit := .cycle 7 6 true (3)
theorem kid23_part1316_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid23_part1316) = true := by rfl

def kid23_part1317 : Audit := .cycle 15 1 false (-1)
theorem kid23_part1317_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid23_part1317) = true := by rfl

def kid23_part1318 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 7 22 true (1),
.last 12 (2,true),
.last 15 (2,true),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 3 15 true (1),
.cycle 19 1 false (1),
.cycle 71 3 false (8),
.cycle 6 11 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.last 15 (2,true),
.cycle 17 1 false (-1),
.cycle 16 3 false (0),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 21 3 false (1),
.cycle 8 7 true (3)
])
theorem kid23_part1318_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid23_part1318) = true := by rfl

def kid23_part1319 : Audit := .cycle 1 11 true (1)
theorem kid23_part1319_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid23_part1319) = true := by rfl

def kid23_part1320 : Audit := .cycle 7 4 true (3)
theorem kid23_part1320_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid23_part1320) = true := by rfl

def kid23_part1321 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 22 1 false (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 48 1 false (10),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 22 1 false (0),
.last 21 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1321_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid23_part1321) = true := by rfl

def kid23_part1322 : Audit := .cycle 0 12 true (0)
theorem kid23_part1322_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid23_part1322) = true := by rfl

def kid23_part1323 : Audit := .cycle 47 1 false (9)
theorem kid23_part1323_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid23_part1323) = true := by rfl

def kid23_part1324 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 22 1 false (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (2,true),
.cycle 3 16 true (1),
.cycle 51 1 false (11),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 22 1 false (0),
.cycle 8 6 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid23_part1324) = true := by rfl

def kid23_part1325 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 6 9 true (2),
.cycle 21 8 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 8 true (3),
.cycle 3 11 true (1),
.cycle 7 15 true (3),
.cycle 12 6 true (4),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 22 7 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid23_part1325) = true := by rfl

def kid23_part1326 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 7 11 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.last 18 (2,true),
.last 25 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 15 (2,true),
.last 18 (2,true),
.cycle 6 10 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.last 18 (2,true),
.cycle 19 5 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 7 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid23_part1326) = true := by rfl

def kid23_part1327 : Audit := .split 11 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 10 4 true (2),
.cycle 25 1 false (1),
.last 15 (5,true),
.last 17 (5,true),
.last 12 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.last 23 (5,true),
.cycle 1 13 true (1),
.cycle 1 15 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 12 (5,true),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (3),
.last 12 (5,true)
])
theorem kid23_part1327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid23_part1327) = true := by rfl

def kid23_part1328 : Audit := .cycle 5 6 true (1)
theorem kid23_part1328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid23_part1328) = true := by rfl

def kid23_part1329 : Audit := .cycle 15 1 false (-1)
theorem kid23_part1329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid23_part1329) = true := by rfl

def kid23_part1330 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 10 4 true (2),
.last 12 (2,true),
.cycle 0 17 true (0),
.cycle 20 1 false (-2),
.cycle 15 6 false (1),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 4 true (3),
.cycle 10 8 true (3),
.cycle 6 12 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 1 17 true (1),
.cycle 20 1 false (-2),
.cycle 16 3 false (0),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid23_part1330) = true := by rfl

def kid23_part1331 : Audit := .cycle 1 11 true (1)
theorem kid23_part1331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid23_part1331) = true := by rfl

def kid23_part1332 : Audit := .cycle 7 4 true (3)
theorem kid23_part1332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid23_part1332) = true := by rfl

def kid23_part1333 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 2 15 true (1),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.last 13 (5,true),
.last 19 (5,true),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid23_part1333) = true := by rfl

def kid23_part1334 : Audit := .cycle 0 12 true (0)
theorem kid23_part1334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid23_part1334) = true := by rfl

def kid23_part1335 : Audit := .cycle 9 3 true (4)
theorem kid23_part1335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid23_part1335) = true := by rfl

def kid23_part1336 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (4),
.cycle 19 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (4),
.cycle 3 9 true (1),
.cycle 8 9 true (4),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 11 2 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.cycle 18 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1336_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid23_part1336) = true := by rfl

def kid23_part1312 : Audit := .split 10 (4,true) (byMove [(kid23_part1313),(kid23_part1314),(kid23_part1315),(kid23_part1316),(kid23_part1317),(kid23_part1318),(kid23_part1319),(kid23_part1320),(kid23_part1321),(kid23_part1322),(kid23_part1323),(kid23_part1324),(kid23_part1325),(kid23_part1326),(kid23_part1327),(kid23_part1328),(kid23_part1329),(kid23_part1330),(kid23_part1331),(kid23_part1332),(kid23_part1333),(kid23_part1334),(kid23_part1335),(kid23_part1336)])

theorem kid23_part1312_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid23_part1312) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid23_part1313),(kid23_part1314),(kid23_part1315),(kid23_part1316),(kid23_part1317),(kid23_part1318),(kid23_part1319),(kid23_part1320),(kid23_part1321),(kid23_part1322),(kid23_part1323),(kid23_part1324),(kid23_part1325),(kid23_part1326),(kid23_part1327),(kid23_part1328),(kid23_part1329),(kid23_part1330),(kid23_part1331),(kid23_part1332),(kid23_part1333),(kid23_part1334),(kid23_part1335),(kid23_part1336)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1313_checked

  · exact kid23_part1319_checked

  · exact kid23_part1325_checked

  · exact kid23_part1331_checked

  · exact kid23_part1314_checked

  · exact kid23_part1320_checked

  · exact kid23_part1326_checked

  · exact kid23_part1332_checked

  · exact kid23_part1315_checked

  · exact kid23_part1321_checked

  · exact kid23_part1327_checked

  · exact kid23_part1333_checked

  · exact kid23_part1316_checked

  · exact kid23_part1322_checked

  · exact kid23_part1328_checked

  · exact kid23_part1334_checked

  · exact kid23_part1317_checked

  · exact kid23_part1323_checked

  · exact kid23_part1329_checked

  · exact kid23_part1335_checked

  · exact kid23_part1318_checked

  · exact kid23_part1324_checked

  · exact kid23_part1330_checked

  · exact kid23_part1336_checked

def kid23_part1338 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 12 6 true (4),
.cycle 6 8 true (2),
.cycle 1 16 true (1),
.cycle 1 22 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1338_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid23_part1338) = true := by rfl

def kid23_part1339 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 0 22 true (-1),
.cycle 7 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 15 true (3),
.cycle 3 11 true (1),
.cycle 12 3 true (4),
.cycle 0 20 true (0),
.cycle 6 8 true (2),
.cycle 7 9 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 34 4 false (0),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 8 6 true (3)
])
theorem kid23_part1339_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid23_part1339) = true := by rfl

def kid23_part1340 : Audit := .split 11 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 10 14 true (1),
.cycle 25 1 false (1),
.cycle 0 17 true (0),
.last 12 (4,true),
.cycle 25 1 false (1),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 3 16 true (1),
.last 14 (4,true),
.last 13 (4,true),
.last 15 (4,true),
.cycle 19 5 false (1),
.cycle 5 16 true (1),
.cycle 1 17 true (1),
.last 12 (4,true),
.cycle 23 1 false (1),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 31 1 false (1),
.last 13 (4,true)
])
theorem kid23_part1340_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid23_part1340) = true := by rfl

def kid23_part1341 : Audit := .cycle 7 6 true (3)
theorem kid23_part1341_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid23_part1341) = true := by rfl

def kid23_part1342 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 10 14 true (1),
.last 12 (2,true),
.last 15 (2,true),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 3 16 true (1),
.cycle 15 3 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 6 10 true (2),
.last 16 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 8 false (1),
.cycle 8 6 true (3)
])
theorem kid23_part1342_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid23_part1342) = true := by rfl

def kid23_part1343 : Audit := .cycle 16 3 false (0)
theorem kid23_part1343_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid23_part1343) = true := by rfl

def kid23_part1344 : Audit := .cycle 1 11 true (1)
theorem kid23_part1344_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid23_part1344) = true := by rfl

def kid23_part1345 : Audit := .cycle 7 4 true (3)
theorem kid23_part1345_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid23_part1345) = true := by rfl

def kid23_part1346 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 20 (4,true),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 10 true (3),
.cycle 12 8 true (3),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 14 8 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 20 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1346_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid23_part1346) = true := by rfl

def kid23_part1347 : Audit := .cycle 0 12 true (0)
theorem kid23_part1347_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid23_part1347) = true := by rfl

def kid23_part1348 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 21 4 false (1),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 10 true (3),
.cycle 3 19 true (1),
.cycle 11 3 true (5),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 21 4 false (1),
.cycle 10 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1348_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid23_part1348) = true := by rfl

def kid23_part1349 : Audit := .cycle 8 4 true (4)
theorem kid23_part1349_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid23_part1349) = true := by rfl

def kid23_part1350 : Audit := .cycle 6 8 true (2)
theorem kid23_part1350_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid23_part1350) = true := by rfl

def kid23_part1351 : Audit := .cycle 10 2 true (3)
theorem kid23_part1351_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid23_part1351) = true := by rfl

def kid23_part1352 : Audit := .split 11 (2,true) (byMove [
.cycle 1 18 true (1),
.last 14 (4,true),
.last 20 (4,true),
.cycle 7 12 true (2),
.last 12 (4,true),
.cycle 7 16 true (1),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2052, 4096, 1024, 128, 256, 8, 128, 132, 1024, 4096],[128, 2048, 4, 1, 4096, 1, 128, 2048, 4, 1, 4096, 4, 4096],4112⟩,
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 1 15 true (1),
.cycle 10 4 true (2),
.cycle 19 5 false (1),
.cycle 5 16 true (1),
.cycle 5 12 true (1),
.last 12 (4,true),
.cycle 5 16 true (1),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (3)
])
theorem kid23_part1352_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid23_part1352) = true := by rfl

def kid23_part1353 : Audit := .cycle 5 6 true (1)
theorem kid23_part1353_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid23_part1353) = true := by rfl

def kid23_part1354 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 7 11 true (2),
.last 12 (2,true),
.cycle 7 12 true (2),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 13 3 true (5),
.cycle 14 6 false (2),
.cycle 10 4 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 5 12 true (1),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 5 true (3),
.cycle 10 2 true (3)
])
theorem kid23_part1354_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid23_part1354) = true := by rfl

def kid23_part1355 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 59, 16, 64],[2, 32, 64, 1, 24, 59, 64],64⟩,
.last 15 (2,true),
.cycle 10 8 true (1),
.cycle 15 4 false (1),
.cycle 16 3 false (0),
.cycle 6 16 true (1),
.cycle 16 12 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 17 3 true (5),
.cycle 18 8 true (3),
.cycle 18 7 false (2),
.cycle 17 5 false (1),
.last 15 (2,true),
.cycle 10 8 true (1),
.cycle 15 4 false (1),
.cycle 16 3 false (0),
.cycle 18 9 false (4),
.cycle 17 7 false (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 16 5 false (2)
])
theorem kid23_part1355_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid23_part1355) = true := by rfl

def kid23_part1356 : Audit := .cycle 1 11 true (1)
theorem kid23_part1356_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid23_part1356) = true := by rfl

def kid23_part1357 : Audit := .cycle 7 4 true (3)
theorem kid23_part1357_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid23_part1357) = true := by rfl

def kid23_part1358 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 2 18 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1358_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid23_part1358) = true := by rfl

def kid23_part1359 : Audit := .cycle 0 12 true (0)
theorem kid23_part1359_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid23_part1359) = true := by rfl

def kid23_part1360 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 4 false (1),
.cycle 9 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (4),
.cycle 3 9 true (1),
.cycle 11 3 true (5),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 9 5 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 17 4 false (1),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid23_part1360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid23_part1360) = true := by rfl

def kid23_part1361 : Audit := .cycle 8 4 true (4)
theorem kid23_part1361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid23_part1361) = true := by rfl

def kid23_part1337 : Audit := .split 10 (5,true) (byMove [(kid23_part1338),(kid23_part1339),(kid23_part1340),(kid23_part1341),(kid23_part1342),(kid23_part1343),(kid23_part1344),(kid23_part1345),(kid23_part1346),(kid23_part1347),(kid23_part1348),(kid23_part1349),(kid23_part1350),(kid23_part1351),(kid23_part1352),(kid23_part1353),(kid23_part1354),(kid23_part1355),(kid23_part1356),(kid23_part1357),(kid23_part1358),(kid23_part1359),(kid23_part1360),(kid23_part1361)])

theorem kid23_part1337_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid23_part1337) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid23_part1338),(kid23_part1339),(kid23_part1340),(kid23_part1341),(kid23_part1342),(kid23_part1343),(kid23_part1344),(kid23_part1345),(kid23_part1346),(kid23_part1347),(kid23_part1348),(kid23_part1349),(kid23_part1350),(kid23_part1351),(kid23_part1352),(kid23_part1353),(kid23_part1354),(kid23_part1355),(kid23_part1356),(kid23_part1357),(kid23_part1358),(kid23_part1359),(kid23_part1360),(kid23_part1361)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1338_checked

  · exact kid23_part1344_checked

  · exact kid23_part1350_checked

  · exact kid23_part1356_checked

  · exact kid23_part1339_checked

  · exact kid23_part1345_checked

  · exact kid23_part1351_checked

  · exact kid23_part1357_checked

  · exact kid23_part1340_checked

  · exact kid23_part1346_checked

  · exact kid23_part1352_checked

  · exact kid23_part1358_checked

  · exact kid23_part1341_checked

  · exact kid23_part1347_checked

  · exact kid23_part1353_checked

  · exact kid23_part1359_checked

  · exact kid23_part1342_checked

  · exact kid23_part1348_checked

  · exact kid23_part1354_checked

  · exact kid23_part1360_checked

  · exact kid23_part1343_checked

  · exact kid23_part1349_checked

  · exact kid23_part1355_checked

  · exact kid23_part1361_checked

def kid23_part1362 : Audit := .cycle 0 10 true (0)
theorem kid23_part1362_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid23_part1362) = true := by rfl

def kid23_part1363 : Audit := .cycle 1 9 true (1)
theorem kid23_part1363_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid23_part1363) = true := by rfl

def kid23_part1364 : Audit := .cycle 2 8 true (1)
theorem kid23_part1364_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid23_part1364) = true := by rfl

def kid23_part1365 : Audit := .cycle 1 12 true (1)
theorem kid23_part1365_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid23_part1365) = true := by rfl

def kid23_part1366 : Audit := .cycle 9 1 true (5)
theorem kid23_part1366_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid23_part1366) = true := by rfl

def kid23_part1367 : Audit := .cycle 8 2 true (4)
theorem kid23_part1367_checked : zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid23_part1367) = true := by rfl

def kid23_part1271 : Audit := .split 9 (4,false) (byMove [(kid23_part1272),(kid23_part1273),(kid23_part1274),(kid23_part1275),(kid23_part1276),(kid23_part1277),(kid23_part1278),(kid23_part1279),(kid23_part1280),(kid23_part1281),(kid23_part1282),(kid23_part1283),(kid23_part1284),(kid23_part1285),(kid23_part1286),(kid23_part1311),(kid23_part1312),(kid23_part1337),(kid23_part1362),(kid23_part1363),(kid23_part1364),(kid23_part1365),(kid23_part1366),(kid23_part1367)])

theorem kid23_part1271_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (kid23_part1271) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid23_part1272),(kid23_part1273),(kid23_part1274),(kid23_part1275),(kid23_part1276),(kid23_part1277),(kid23_part1278),(kid23_part1279),(kid23_part1280),(kid23_part1281),(kid23_part1282),(kid23_part1283),(kid23_part1284),(kid23_part1285),(kid23_part1286),(kid23_part1311),(kid23_part1312),(kid23_part1337),(kid23_part1362),(kid23_part1363),(kid23_part1364),(kid23_part1365),(kid23_part1366),(kid23_part1367)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1272_checked

  · exact kid23_part1278_checked

  · exact kid23_part1284_checked

  · exact kid23_part1362_checked

  · exact kid23_part1273_checked

  · exact kid23_part1279_checked

  · exact kid23_part1285_checked

  · exact kid23_part1363_checked

  · exact kid23_part1274_checked

  · exact kid23_part1280_checked

  · exact kid23_part1286_checked

  · exact kid23_part1364_checked

  · exact kid23_part1275_checked

  · exact kid23_part1281_checked

  · exact kid23_part1311_checked

  · exact kid23_part1365_checked

  · exact kid23_part1276_checked

  · exact kid23_part1282_checked

  · exact kid23_part1312_checked

  · exact kid23_part1366_checked

  · exact kid23_part1277_checked

  · exact kid23_part1283_checked

  · exact kid23_part1337_checked

  · exact kid23_part1367_checked

def kid23_part1368 : Audit := .cycle 8 1 true (4)
theorem kid23_part1368_checked : zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some ⟨true,true,5⟩)) (kid23_part1368) = true := by rfl

def kid23 : Audit := .split 8 (5,false) (byMove [(kid23_part1),(kid23_part2),(kid23_part3),(kid23_part100),(kid23_part101),(kid23_part318),(kid23_part391),(kid23_part392),(kid23_part393),(kid23_part466),(kid23_part467),(kid23_part564),(kid23_part565),(kid23_part566),(kid23_part639),(kid23_part760),(kid23_part761),(kid23_part1146),(kid23_part1267),(kid23_part1268),(kid23_part1269),(kid23_part1270),(kid23_part1271),(kid23_part1368)])

theorem check23 : zipCheck 175 (child39 ⟨true,true,5⟩) (kid23) = true := by

  change (zipQueryOK 175 (child39 ⟨true,true,5⟩) 8 (5,false) && allMoves (fun mv => zipCheck 175 (refine (child39 ⟨true,true,5⟩) (5,false) (some mv)) (byMove [(kid23_part1),(kid23_part2),(kid23_part3),(kid23_part100),(kid23_part101),(kid23_part318),(kid23_part391),(kid23_part392),(kid23_part393),(kid23_part466),(kid23_part467),(kid23_part564),(kid23_part565),(kid23_part566),(kid23_part639),(kid23_part760),(kid23_part761),(kid23_part1146),(kid23_part1267),(kid23_part1268),(kid23_part1269),(kid23_part1270),(kid23_part1271),(kid23_part1368)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid23_part1_checked

  · exact kid23_part391_checked

  · exact kid23_part565_checked

  · exact kid23_part1267_checked

  · exact kid23_part2_checked

  · exact kid23_part392_checked

  · exact kid23_part566_checked

  · exact kid23_part1268_checked

  · exact kid23_part3_checked

  · exact kid23_part393_checked

  · exact kid23_part639_checked

  · exact kid23_part1269_checked

  · exact kid23_part100_checked

  · exact kid23_part466_checked

  · exact kid23_part760_checked

  · exact kid23_part1270_checked

  · exact kid23_part101_checked

  · exact kid23_part467_checked

  · exact kid23_part761_checked

  · exact kid23_part1271_checked

  · exact kid23_part318_checked

  · exact kid23_part564_checked

  · exact kid23_part1146_checked

  · exact kid23_part1368_checked

end BB6.Agent11Raw39
