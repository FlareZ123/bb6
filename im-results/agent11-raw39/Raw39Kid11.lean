import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid11_part1 : Audit := .cycle 0 9 true (0)
theorem kid11_part1_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,0⟩)) (kid11_part1) = true := by rfl

def kid11_part2 : Audit := .cycle 1 8 true (1)
theorem kid11_part2_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,1⟩)) (kid11_part2) = true := by rfl

def kid11_part3 : Audit := .cycle 2 7 true (1)
theorem kid11_part3_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (kid11_part3) = true := by rfl

def kid11_part4 : Audit := .cycle 1 11 true (1)
theorem kid11_part4_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (kid11_part4) = true := by rfl

def kid11_part6 : Audit := .cycle 1 10 true (1)
theorem kid11_part6_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part6) = true := by rfl

def kid11_part7 : Audit := .cycle 1 12 true (1)
theorem kid11_part7_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part7) = true := by rfl

def kid11_part9 : Audit := .cycle 0 11 true (0)
theorem kid11_part9_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part9) = true := by rfl

def kid11_part10 : Audit := .cycle 1 10 true (1)
theorem kid11_part10_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part10) = true := by rfl

def kid11_part11 : Audit := .cycle 21 1 false (1)
theorem kid11_part11_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part11) = true := by rfl

def kid11_part12 : Audit := .cycle 1 13 true (0)
theorem kid11_part12_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part12) = true := by rfl

def kid11_part13 : Audit := .cycle 15 1 false (-1)
theorem kid11_part13_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part13) = true := by rfl

def kid11_part14 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (4),
.cycle 26 1 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 26 1 false (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 21 1 false (-3),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 25 1 false (-1),
.cycle 1 15 true (0),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid11_part14_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part14) = true := by rfl

def kid11_part15 : Audit := .cycle 0 11 true (0)
theorem kid11_part15_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part15) = true := by rfl

def kid11_part16 : Audit := .cycle 1 10 true (1)
theorem kid11_part16_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part16) = true := by rfl

def kid11_part17 : Audit := .split 19 (5,true) (byMove [
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 1 35 true (0),
.cycle 23 1 false (3),
.last 21 (4,true),
.cycle 1 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 34, 290, 128, 256, 8, 128, 8, 4096, 4096],[128, 32, 4, 1, 4096, 2, 128, 32, 4, 1, 4096, 2, 4096],6144⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 36, 44, 128, 256, 8, 128, 8, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 43 1 false (5),
.cycle 21 13 true (2),
.cycle 10 12 true (0),
.cycle 1 22 true (0),
.cycle 33 1 false (5),
.cycle 1 24 true (0),
.last 21 (4,true),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.cycle 10 39 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 22 (4,true)
])
theorem kid11_part17_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part17) = true := by rfl

def kid11_part18 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (3),
.cycle 1 20 true (0),
.cycle 20 1 false (2),
.last 19 (4,true),
.cycle 0 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 34, 256, 128, 256, 8, 128, 34, 4096, 4096],[128, 32, 8, 1, 4096, 2, 128, 32, 8, 1, 4096, 2, 4096],6144⟩,
.cycle 19 9 true (1),
.cycle 11 7 true (0),
.cycle 11 9 true (0),
.cycle 29 1 false (3),
.cycle 31 1 false (3),
.cycle 3 17 true (0),
.cycle 0 20 true (0),
.cycle 25 1 false (3),
.cycle 20 1 false (2),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 19 17 true (1),
.cycle 1 20 true (0),
.cycle 9 9 true (0),
.last 19 (4,true)
])
theorem kid11_part18_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part18) = true := by rfl

def kid11_part19 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (3),
.cycle 1 22 true (0),
.cycle 24 1 false (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 34, 256, 128, 256, 8, 128, 34, 4096, 4096],[128, 32, 16, 1, 4096, 2, 128, 32, 16, 1, 4096, 2, 4096],6144⟩,
.cycle 20 11 true (1),
.cycle 13 7 true (0),
.cycle 11 9 true (0),
.cycle 33 1 false (3),
.cycle 37 1 false (3),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.cycle 24 1 false (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 20 21 true (1),
.cycle 1 22 true (0),
.cycle 9 11 true (0),
.last 21 (4,true)
])
theorem kid11_part19_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part19) = true := by rfl

def kid11_part20 : Audit := .cycle 25 1 false (1)
theorem kid11_part20_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part20) = true := by rfl

def kid11_part21 : Audit := .cycle 17 5 false (2)
theorem kid11_part21_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part21) = true := by rfl

def kid11_part22 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 1 17 true (0),
.cycle 23 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 36, 44, 128, 256, 8, 128, 8, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 13 7 true (0),
.cycle 13 9 true (0),
.cycle 33 1 false (1),
.cycle 19 9 false (2),
.cycle 11 4 true (1),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 23 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (1),
.last 16 (4,true)
])
theorem kid11_part22_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part22) = true := by rfl

def kid11_part23 : Audit := .cycle 0 13 true (0)
theorem kid11_part23_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part23) = true := by rfl

def kid11_part24 : Audit := .cycle 18 1 false (0)
theorem kid11_part24_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part24) = true := by rfl

def kid11_part25 : Audit := .cycle 15 1 false (-1)
theorem kid11_part25_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part25) = true := by rfl

def kid11_part26 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.last 20 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 21 1 false (-1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 21 1 false (-3),
.last 15 (5,true),
.cycle 23 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid11_part26_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part26) = true := by rfl

def kid11_part27 : Audit := .cycle 0 11 true (0)
theorem kid11_part27_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part27) = true := by rfl

def kid11_part28 : Audit := .cycle 1 10 true (1)
theorem kid11_part28_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part28) = true := by rfl

def kid11_part29 : Audit := .cycle 2 9 true (1)
theorem kid11_part29_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part29) = true := by rfl

def kid11_part30 : Audit := .cycle 1 13 true (1)
theorem kid11_part30_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part30) = true := by rfl

def kid11_part31 : Audit := .cycle 9 2 true (2)
theorem kid11_part31_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part31) = true := by rfl

def kid11_part32 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.last 21 (5,true),
.cycle 29 1 false (1),
.cycle 21 7 false (2),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
])
theorem kid11_part32_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part32) = true := by rfl

def kid11_part8 : Audit := .split 10 (2,true) (byMove [(kid11_part9),(kid11_part10),(kid11_part11),(kid11_part12),(kid11_part13),(kid11_part14),(kid11_part15),(kid11_part16),(kid11_part17),(kid11_part18),(kid11_part19),(kid11_part20),(kid11_part21),(kid11_part22),(kid11_part23),(kid11_part24),(kid11_part25),(kid11_part26),(kid11_part27),(kid11_part28),(kid11_part29),(kid11_part30),(kid11_part31),(kid11_part32)])

theorem kid11_part8_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part8) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part9),(kid11_part10),(kid11_part11),(kid11_part12),(kid11_part13),(kid11_part14),(kid11_part15),(kid11_part16),(kid11_part17),(kid11_part18),(kid11_part19),(kid11_part20),(kid11_part21),(kid11_part22),(kid11_part23),(kid11_part24),(kid11_part25),(kid11_part26),(kid11_part27),(kid11_part28),(kid11_part29),(kid11_part30),(kid11_part31),(kid11_part32)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part9_checked

  · exact kid11_part15_checked

  · exact kid11_part21_checked

  · exact kid11_part27_checked

  · exact kid11_part10_checked

  · exact kid11_part16_checked

  · exact kid11_part22_checked

  · exact kid11_part28_checked

  · exact kid11_part11_checked

  · exact kid11_part17_checked

  · exact kid11_part23_checked

  · exact kid11_part29_checked

  · exact kid11_part12_checked

  · exact kid11_part18_checked

  · exact kid11_part24_checked

  · exact kid11_part30_checked

  · exact kid11_part13_checked

  · exact kid11_part19_checked

  · exact kid11_part25_checked

  · exact kid11_part31_checked

  · exact kid11_part14_checked

  · exact kid11_part20_checked

  · exact kid11_part26_checked

  · exact kid11_part32_checked

def kid11_part33 : Audit := .cycle 0 11 true (0)
theorem kid11_part33_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part33) = true := by rfl

def kid11_part34 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.last 24 (2,true),
.cycle 23 1 false (3),
.cycle 23 1 false (3),
.cycle 1 20 true (0),
.cycle 27 1 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 32 (2,true),
.cycle 27 1 false (3),
.cycle 21 13 true (2),
.last 21 (2,true),
.cycle 1 22 true (0),
.cycle 33 1 false (5),
.cycle 1 24 true (0),
.cycle 1 24 true (0),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 20 true (0),
.cycle 10 22 true (0)
]),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (3),
.cycle 1 20 true (0),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 46, 46, 64],[2, 32, 64, 1, 8, 2, 64],64⟩,
.last 27 (2,true),
.cycle 11 7 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 31 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 25 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 35 (2,true),
.cycle 1 20 true (0),
.cycle 9 9 true (0),
.cycle 10 9 true (0)
]),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 17 5 false (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.last 17 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,true),
.last 16 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (2),
.cycle 10 2 true (2)
])
theorem kid11_part34_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part34) = true := by rfl

def kid11_part35 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 13 2 false (-1),
.split 12 (4,true) (byMove [
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
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 10 18 true (0),
.cycle 30 1 false (4),
.last 23 (4,true),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.proven (BB6.Agent11Raw39Pumps.M852.table) (fun m hm => BB6.Agent11Raw39Pumps.M852.never m hm),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34734080, 1075838976, 1074790400, 2, 4, 32768, 128, 2097160, 1073741824, 33554432, 67108864, 2097152, 131072, 1073741824, 34734080, 128, 256, 2097152, 1048576, 1110573068, 1110573068, 2, 4, 32768, 128, 2097152, 1073741824, 1073741824],[128, 32, 4, 1, 1073741824, 4, 2, 131072, 16384, 4096, 1073741824, 16384, 33554432, 8388608, 1048576, 262144, 1073741824, 1048576, 128, 8388608, 1048576, 262144, 1073741824, 1048576, 2, 131072, 16384, 4096, 1073741824, 16384, 1073741824],1623263280⟩,
.cycle 12 9 true (0),
.last 25 (4,true),
.cycle 27 1 false (3),
.cycle 7 15 true (0),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34734084, 1110573068, 1110573068, 2, 4, 32768, 128, 2097160, 1073741824, 33554432, 67108864, 2097152, 131072, 1073741824, 34734084, 128, 256, 2097152, 1048580, 1110573068, 1110573068, 2, 4, 32768, 128, 2097152, 1073741824, 1073741824],[128, 32, 1048580, 1, 1073741824, 4, 2, 131072, 1048580, 4096, 1073741824, 16384, 33554432, 8388608, 1048580, 262144, 1073741824, 1048576, 128, 8388608, 1048580, 262144, 1073741824, 1048576, 2, 131072, 1048576, 4096, 1073741824, 16384, 1073741824],1623263280⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.last 23 (4,true),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 42 true (0),
.cycle 1 23 true (0),
.last 34 (4,true),
.last 22 (4,true)
]),
.cycle 10 7 true (0),
.cycle 15 2 false (1),
.split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 25 2 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 25 2 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 2 false (1),
.cycle 15 2 false (1),
.cycle 20 2 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 2 false (2),
.cycle 1 17 true (0),
.cycle 17 2 false (1),
.cycle 13 2 true (0)
]),
.cycle 17 5 false (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 17 5 false (2),
.cycle 19 7 false (2),
.cycle 10 4 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 6 true (1),
.last 14 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 2 false (-1),
.split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 18 2 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 20 2 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 19 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 2 false (0),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (2),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 22 true (0),
.cycle 10 9 true (0),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
])
])
theorem kid11_part35_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part35) = true := by rfl

def kid11_part36 : Audit := .cycle 0 10 true (0)
theorem kid11_part36_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part36) = true := by rfl

def kid11_part37 : Audit := .cycle 1 9 true (1)
theorem kid11_part37_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part37) = true := by rfl

def kid11_part39 : Audit := .cycle 0 18 true (0)
theorem kid11_part39_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part39) = true := by rfl

def kid11_part40 : Audit := .cycle 1 17 true (1)
theorem kid11_part40_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part40) = true := by rfl

def kid11_part41 : Audit := .cycle 2 16 true (1)
theorem kid11_part41_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part41) = true := by rfl

def kid11_part42 : Audit := .cycle 1 20 true (1)
theorem kid11_part42_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part42) = true := by rfl

def kid11_part43 : Audit := .cycle 9 9 true (2)
theorem kid11_part43_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part43) = true := by rfl

def kid11_part44 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 34 1 false (2),
.cycle 35 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 53 1 false (9),
.cycle 37 1 false (3),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 28 1 false (0),
.last 21 (2,true),
.cycle 0 24 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 18 2 true (3)
])
theorem kid11_part44_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part44) = true := by rfl

def kid11_part45 : Audit := .cycle 0 18 true (0)
theorem kid11_part45_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part45) = true := by rfl

def kid11_part46 : Audit := .cycle 1 17 true (1)
theorem kid11_part46_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part46) = true := by rfl

def kid11_part47 : Audit := .split 27 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 10 18 true (2),
.cycle 3 25 true (1),
.cycle 18 11 true (3),
.cycle 8 20 true (2),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 19 9 true (3),
.last 41 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 32, 1, 4096, 4, 4096],6144⟩,
.cycle 7 22 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 30 true (0),
.cycle 12 16 true (2),
.cycle 27 2 true (6),
.cycle 0 32 true (0),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 9 19 true (2),
.last 29 (4,true)
])
theorem kid11_part47_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part47) = true := by rfl

def kid11_part48 : Audit := .cycle 11 7 true (2)
theorem kid11_part48_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part48) = true := by rfl

def kid11_part49 : Audit := .split 29 (4,true) (byMove [
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 10 29 true (2),
.cycle 0 39 true (0),
.cycle 0 33 true (0),
.cycle 8 33 true (2),
.cycle 1 30 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 12, 64],[2, 32, 64, 1, 2, 16, 64],64⟩,
.last 30 (2,true),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 12, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 16 15 true (3),
.last 31 (2,true),
.cycle 1 32 true (1),
.cycle 12 25 true (2),
.last 31 (2,true),
.cycle 1 34 true (1),
.cycle 1 30 true (1),
.cycle 7 23 true (2),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 9 22 true (2),
.cycle 41 2 true (11)
])
theorem kid11_part49_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part49) = true := by rfl

def kid11_part50 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4096, 1, 4096, 32, 128, 32, 4096, 1, 4096, 32, 4096],6144⟩
theorem kid11_part50_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part50) = true := by rfl

def kid11_part51 : Audit := .cycle 7 12 true (2)
theorem kid11_part51_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part51) = true := by rfl

def kid11_part52 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 35 1 false (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 33 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.last 32 (4,true),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.cycle 16 4 true (4),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 33 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.last 21 (4,true)
])
theorem kid11_part52_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part52) = true := by rfl

def kid11_part53 : Audit := .cycle 0 20 true (0)
theorem kid11_part53_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part53) = true := by rfl

def kid11_part54 : Audit := .cycle 4 14 true (1)
theorem kid11_part54_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part54) = true := by rfl

def kid11_part55 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],6144⟩,
.cycle 11 9 true (2),
.last 33 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 32, 1, 4096, 32, 128, 32, 32, 1, 4096, 4096, 4096],6144⟩,
.cycle 7 14 true (2),
.cycle 16 6 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.last 21 (4,true)
])
theorem kid11_part55_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part55) = true := by rfl

def kid11_part56 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 34 1 false (2),
.cycle 35 1 false (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.last 21 (2,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.last 21 (2,true),
.cycle 7 16 true (2),
.cycle 28 1 false (0),
.last 21 (2,true),
.cycle 7 18 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 18 2 true (3)
])
theorem kid11_part56_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part56) = true := by rfl

def kid11_part57 : Audit := .cycle 0 18 true (0)
theorem kid11_part57_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part57) = true := by rfl

def kid11_part58 : Audit := .cycle 1 17 true (1)
theorem kid11_part58_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part58) = true := by rfl

def kid11_part59 : Audit := .cycle 2 16 true (1)
theorem kid11_part59_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part59) = true := by rfl

def kid11_part60 : Audit := .cycle 1 20 true (1)
theorem kid11_part60_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part60) = true := by rfl

def kid11_part61 : Audit := .cycle 9 9 true (2)
theorem kid11_part61_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part61) = true := by rfl

def kid11_part62 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 39 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 22 true (2),
.cycle 11 9 true (2),
.cycle 31 13 true (7),
.cycle 8 26 true (2),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 7 20 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 18 2 true (5)
])
theorem kid11_part62_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part62) = true := by rfl

def kid11_part38 : Audit := .split 17 (5,true) (byMove [(kid11_part39),(kid11_part40),(kid11_part41),(kid11_part42),(kid11_part43),(kid11_part44),(kid11_part45),(kid11_part46),(kid11_part47),(kid11_part48),(kid11_part49),(kid11_part50),(kid11_part51),(kid11_part52),(kid11_part53),(kid11_part54),(kid11_part55),(kid11_part56),(kid11_part57),(kid11_part58),(kid11_part59),(kid11_part60),(kid11_part61),(kid11_part62)])

theorem kid11_part38_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part38) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid11_part39),(kid11_part40),(kid11_part41),(kid11_part42),(kid11_part43),(kid11_part44),(kid11_part45),(kid11_part46),(kid11_part47),(kid11_part48),(kid11_part49),(kid11_part50),(kid11_part51),(kid11_part52),(kid11_part53),(kid11_part54),(kid11_part55),(kid11_part56),(kid11_part57),(kid11_part58),(kid11_part59),(kid11_part60),(kid11_part61),(kid11_part62)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part39_checked

  · exact kid11_part45_checked

  · exact kid11_part51_checked

  · exact kid11_part57_checked

  · exact kid11_part40_checked

  · exact kid11_part46_checked

  · exact kid11_part52_checked

  · exact kid11_part58_checked

  · exact kid11_part41_checked

  · exact kid11_part47_checked

  · exact kid11_part53_checked

  · exact kid11_part59_checked

  · exact kid11_part42_checked

  · exact kid11_part48_checked

  · exact kid11_part54_checked

  · exact kid11_part60_checked

  · exact kid11_part43_checked

  · exact kid11_part49_checked

  · exact kid11_part55_checked

  · exact kid11_part61_checked

  · exact kid11_part44_checked

  · exact kid11_part50_checked

  · exact kid11_part56_checked

  · exact kid11_part62_checked

def kid11_part63 : Audit := .cycle 3 7 true (1)
theorem kid11_part63_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part63) = true := by rfl

def kid11_part64 : Audit := .cycle 9 1 true (3)
theorem kid11_part64_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part64) = true := by rfl

def kid11_part65 : Audit := .cycle 8 2 true (3)
theorem kid11_part65_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part65) = true := by rfl

def kid11_part66 : Audit := .cycle 6 4 true (2)
theorem kid11_part66_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part66) = true := by rfl

def kid11_part68 : Audit := .cycle 0 12 true (0)
theorem kid11_part68_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part68) = true := by rfl

def kid11_part69 : Audit := .cycle 1 11 true (1)
theorem kid11_part69_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part69) = true := by rfl

def kid11_part70 : Audit := .cycle 31 1 false (3)
theorem kid11_part70_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part70) = true := by rfl

def kid11_part71 : Audit := .cycle 21 1 false (1)
theorem kid11_part71_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part71) = true := by rfl

def kid11_part72 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (1),
.cycle 3 12 true (1),
.cycle 12 3 true (1),
.cycle 19 7 false (1),
.cycle 21 9 false (1),
.cycle 18 5 false (1),
.cycle 1 31 true (-1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 18 9 false (2),
.last 16 (4,true)
])
theorem kid11_part72_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part72) = true := by rfl

def kid11_part73 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 false (4),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.cycle 0 21 false (4),
.last 20 (4,true),
.cycle 15 5 false (1),
.cycle 8 24 false (4),
.cycle 12 15 true (-2),
.last 29 (4,true),
.cycle 12 13 false (2),
.cycle 17 3 true (-2),
.cycle 12 8 false (2),
.cycle 12 10 false (2),
.cycle 14 6 false (1),
.cycle 1 23 false (4),
.cycle 1 21 false (4),
.last 20 (4,true),
.cycle 15 5 false (1),
.last 37 (4,true),
.last 36 (4,true),
.cycle 2 18 false (4),
.cycle 8 26 false (4),
.last 24 (4,true),
.last 21 (4,true)
])
theorem kid11_part73_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part73) = true := by rfl

def kid11_part74 : Audit := .cycle 0 12 true (0)
theorem kid11_part74_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part74) = true := by rfl

def kid11_part75 : Audit := .cycle 1 11 true (1)
theorem kid11_part75_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part75) = true := by rfl

def kid11_part76 : Audit := .split 22 (2,true) (byMove [
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 24 18 true (1),
.cycle 0 34 true (0),
.last 26 (4,true),
.cycle 28 1 false (4),
.cycle 1 23 true (0),
.cycle 20 80 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 24 true (0),
.last 23 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 32, 1, 4096, 4, 4096],6144⟩,
.cycle 7 30 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 1 25 true (0),
.cycle 23 16 true (1),
.last 26 (4,true),
.cycle 1 29 true (0),
.cycle 1 23 true (0),
.cycle 1 51 true (0),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 43 (4,true)
])
theorem kid11_part76_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part76) = true := by rfl

def kid11_part77 : Audit := .cycle 0 21 true (0)
theorem kid11_part77_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part77) = true := by rfl

def kid11_part78 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 30 5 false (2),
.cycle 43 1 false (3),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (2),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (2),
.last 16 (4,true)
])
theorem kid11_part78_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part78) = true := by rfl

def kid11_part79 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 26 5 false (2),
.cycle 33 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 25 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 10 12 true (2),
.cycle 3 13 true (1),
.cycle 13 3 true (2),
.cycle 8 8 true (2),
.cycle 6 10 true (2),
.cycle 10 6 true (2),
.cycle 1 19 true (1),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 11 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 9 7 true (2),
.last 17 (4,true)
])
theorem kid11_part79_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part79) = true := by rfl

def kid11_part80 : Audit := .cycle 7 6 true (2)
theorem kid11_part80_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part80) = true := by rfl

def kid11_part81 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 24 5 false (1),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (2),
.cycle 3 11 true (1),
.cycle 12 3 true (2),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (2),
.last 15 (4,true)
])
theorem kid11_part81_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part81) = true := by rfl

def kid11_part82 : Audit := .cycle 0 14 true (0)
theorem kid11_part82_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part82) = true := by rfl

def kid11_part83 : Audit := .cycle 26 1 false (2)
theorem kid11_part83_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part83) = true := by rfl

def kid11_part84 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],6144⟩,
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 18 7 false (2),
.cycle 19 9 false (2),
.cycle 18 5 false (1),
.cycle 15 12 true (-1),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 18 11 false (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid11_part84_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part84) = true := by rfl

def kid11_part85 : Audit := .split 19 (2,true) (byMove [
.cycle 0 38 true (-2),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.far true 5 ⟨0,[0, 1, 2, 3, 3, 1, 4, 4, 4, 4],[65536, 128, 2097152, 512, 128, 16, 65536, 128, 128, 2097152, 524288, 65536, 65536, 65536, 134217728, 512, 128, 4194304, 1073741824, 1375797376, 2097280, 134217728, 33554432, 268435456, 1375797248, 1375797376, 1510015104, 134217728, 33554432, 268435456, 1073741824],[65536, 128, 8, 128, 1073741824, 2048, 65536, 65536, 32768, 128, 1073741824, 8388608, 65536, 128, 2097152, 128, 1073741824, 2048, 1073741824, 301989888, 134217728, 128, 1073741824, 536870912, 1375797248, 301989888, 134217728, 1375797376, 1073741824, 536870912, 1073741824],2009990144⟩,
.last 20 (4,true),
.cycle 15 5 false (1),
.cycle 7 14 false (4),
.cycle 20 17 true (0),
.cycle 0 34 true (-2),
.last 27 (4,true),
.last 23 (4,true),
.cycle 12 8 false (2),
.cycle 12 10 false (2),
.cycle 14 6 false (1),
.cycle 12 20 true (-3),
.far true 5 ⟨0,[0, 1, 2, 3, 3, 1, 4, 4, 4, 4],[65536, 128, 2097152, 512, 128, 16, 65536, 128, 128, 2097152, 524288, 65536, 65536, 65536, 134217728, 512, 128, 4194304, 1073741824, 1375797376, 2097280, 134217728, 33554432, 268435456, 1375797248, 1375797376, 1510015104, 134217728, 33554432, 268435456, 1073741824],[65536, 128, 512, 128, 1073741824, 2048, 65536, 65536, 2097152, 128, 1073741824, 8388608, 65536, 128, 512, 128, 1073741824, 2048, 1073741824, 301989888, 134217728, 128, 1073741824, 536870912, 1375797248, 301989888, 134217728, 1375797376, 1073741824, 536870912, 1073741824],2009990144⟩,
.last 20 (4,true),
.cycle 15 5 false (1),
.last 27 (4,true),
.last 40 (4,true),
.cycle 0 34 true (-2),
.cycle 4 16 false (4),
.last 24 (4,true),
.last 21 (4,true)
])
theorem kid11_part85_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part85) = true := by rfl

def kid11_part86 : Audit := .cycle 0 12 true (0)
theorem kid11_part86_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part86) = true := by rfl

def kid11_part87 : Audit := .cycle 1 11 true (1)
theorem kid11_part87_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part87) = true := by rfl

def kid11_part88 : Audit := .cycle 2 10 true (1)
theorem kid11_part88_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part88) = true := by rfl

def kid11_part89 : Audit := .cycle 1 14 true (1)
theorem kid11_part89_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part89) = true := by rfl

def kid11_part90 : Audit := .cycle 9 3 true (2)
theorem kid11_part90_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part90) = true := by rfl

def kid11_part91 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (3),
.cycle 25 1 false (1),
.last 16 (2,true),
.last 23 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 24 22 true (4),
.cycle 3 46 true (0),
.last 16 (2,true),
.last 17 (2,true),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.last 16 (2,true),
.last 23 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part91_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part91) = true := by rfl

def kid11_part67 : Audit := .split 11 (5,true) (byMove [(kid11_part68),(kid11_part69),(kid11_part70),(kid11_part71),(kid11_part72),(kid11_part73),(kid11_part74),(kid11_part75),(kid11_part76),(kid11_part77),(kid11_part78),(kid11_part79),(kid11_part80),(kid11_part81),(kid11_part82),(kid11_part83),(kid11_part84),(kid11_part85),(kid11_part86),(kid11_part87),(kid11_part88),(kid11_part89),(kid11_part90),(kid11_part91)])

theorem kid11_part67_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part67) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some mv)) (byMove [(kid11_part68),(kid11_part69),(kid11_part70),(kid11_part71),(kid11_part72),(kid11_part73),(kid11_part74),(kid11_part75),(kid11_part76),(kid11_part77),(kid11_part78),(kid11_part79),(kid11_part80),(kid11_part81),(kid11_part82),(kid11_part83),(kid11_part84),(kid11_part85),(kid11_part86),(kid11_part87),(kid11_part88),(kid11_part89),(kid11_part90),(kid11_part91)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part68_checked

  · exact kid11_part74_checked

  · exact kid11_part80_checked

  · exact kid11_part86_checked

  · exact kid11_part69_checked

  · exact kid11_part75_checked

  · exact kid11_part81_checked

  · exact kid11_part87_checked

  · exact kid11_part70_checked

  · exact kid11_part76_checked

  · exact kid11_part82_checked

  · exact kid11_part88_checked

  · exact kid11_part71_checked

  · exact kid11_part77_checked

  · exact kid11_part83_checked

  · exact kid11_part89_checked

  · exact kid11_part72_checked

  · exact kid11_part78_checked

  · exact kid11_part84_checked

  · exact kid11_part90_checked

  · exact kid11_part73_checked

  · exact kid11_part79_checked

  · exact kid11_part85_checked

  · exact kid11_part91_checked

def kid11_part93 : Audit := .cycle 1 14 true (1)
theorem kid11_part93_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part93) = true := by rfl

def kid11_part94 : Audit := .cycle 0 14 true (0)
theorem kid11_part94_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part94) = true := by rfl

def kid11_part95 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (2),
.cycle 1 20 true (0),
.cycle 21 1 false (1),
.last 19 (4,true),
.cycle 0 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 1, 426, 128, 256, 8, 128, 427, 4096, 4096],[128, 32, 34, 1, 4096, 2, 128, 32, 426, 1, 4096, 2, 4096],6144⟩,
.cycle 12 18 true (0),
.cycle 12 7 true (0),
.cycle 0 21 true (0),
.cycle 0 22 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 47 1 false (3),
.cycle 1 20 true (0),
.cycle 9 9 true (0),
.last 19 (4,true)
])
theorem kid11_part95_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part95) = true := by rfl

def kid11_part96 : Audit := .cycle 0 17 true (0)
theorem kid11_part96_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part96) = true := by rfl

def kid11_part97 : Audit := .cycle 11 8 true (-2)
theorem kid11_part97_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part97) = true := by rfl

def kid11_part98 : Audit := .split 12 (4,true) (byMove [
.last 21 (5,true),
.last 30 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 20 true (-2),
.last 25 (5,true),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 28 (5,true),
.last 20 (5,true),
.last 25 (5,true),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 0 20 true (-2),
.last 29 (5,true),
.last 16 (5,true),
.cycle 0 16 true (0),
.last 19 (5,true),
.last 18 (5,true),
.last 22 (5,true),
.cycle 11 2 true (0)
])
theorem kid11_part98_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part98) = true := by rfl

def kid11_part99 : Audit := .cycle 1 11 true (1)
theorem kid11_part99_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part99) = true := by rfl

def kid11_part100 : Audit := .cycle 0 16 true (0)
theorem kid11_part100_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part100) = true := by rfl

def kid11_part101 : Audit := .split 21 (5,true) (byMove [
.cycle 0 46 true (0),
.cycle 1 25 true (0),
.cycle 47 1 false (7),
.cycle 1 52 true (0),
.cycle 1 27 true (0),
.last 23 (4,true),
.cycle 0 42 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 1, 136, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 2, 128, 32, 4, 1, 4096, 2, 4096],6144⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 1, 136, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 1 23 true (0),
.last 22 (4,true),
.cycle 0 28 true (0),
.cycle 23 18 true (3),
.cycle 10 14 true (0),
.cycle 0 48 true (0),
.cycle 41 1 false (7),
.cycle 29 1 false (7),
.last 23 (4,true),
.cycle 1 37 true (0),
.cycle 1 23 true (0),
.cycle 10 54 true (0),
.cycle 1 23 true (0),
.last 22 (4,true),
.last 25 (4,true)
])
theorem kid11_part101_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part101) = true := by rfl

def kid11_part102 : Audit := .cycle 0 12 true (0)
theorem kid11_part102_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part102) = true := by rfl

def kid11_part103 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.cycle 0 20 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.cycle 7 6 true (2),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 1 15 true (1),
.cycle 12 10 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 2 true (3)
])
theorem kid11_part103_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part103) = true := by rfl

def kid11_part104 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.cycle 0 20 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 42 true (0),
.cycle 0 21 true (0),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.cycle 7 6 true (2),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 1 15 true (1),
.cycle 12 10 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 13 (4,true)
])
theorem kid11_part104_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part104) = true := by rfl

def kid11_part105 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 5 false (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 18 true (1),
.cycle 12 7 true (1),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.cycle 12 8 true (1),
.cycle 12 10 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 5 false (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (1),
.last 15 (4,true)
])
theorem kid11_part105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part105) = true := by rfl

def kid11_part106 : Audit := .split 14 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 36 1 false (2),
.cycle 1 24 true (0),
.cycle 15 12 true (-2),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 1, 136, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 20 true (0),
.cycle 12 10 true (1),
.cycle 11 4 true (1),
.cycle 1 17 true (1),
.cycle 31 1 false (1),
.cycle 13 12 true (-2),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 17 (4,true)
])
theorem kid11_part106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part106) = true := by rfl

def kid11_part107 : Audit := .cycle 1 13 true (1)
theorem kid11_part107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part107) = true := by rfl

def kid11_part108 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 25 1 false (1),
.cycle 1 18 true (0),
.cycle 18 1 false (0),
.last 17 (4,true),
.cycle 0 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 1, 384, 128, 256, 8, 128, 34, 4096, 4096],[128, 32, 34, 1, 4096, 2, 128, 32, 128, 1, 4096, 2, 4096],6144⟩,
.cycle 11 16 true (0),
.cycle 11 7 true (0),
.cycle 0 19 true (0),
.cycle 0 20 true (0),
.cycle 27 1 false (1),
.cycle 1 19 true (0),
.cycle 0 18 true (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 1 33 true (0),
.cycle 1 18 true (0),
.cycle 9 7 true (0),
.last 17 (4,true)
])
theorem kid11_part108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part108) = true := by rfl

def kid11_part109 : Audit := .split 18 (5,true) (byMove [
.last 22 (4,true),
.cycle 0 22 true (-2),
.cycle 29 8 true (0),
.last 24 (4,true),
.cycle 19 8 true (-2),
.last 20 (4,true),
.cycle 1 19 true (-2),
.cycle 0 24 true (-2),
.cycle 1 23 true (-2),
.cycle 0 20 true (-2),
.last 19 (4,true),
.cycle 0 24 true (-2),
.last 27 (4,true),
.last 21 (4,true),
.cycle 1 21 true (-2),
.cycle 25 8 true (0),
.cycle 11 8 true (-2),
.last 20 (4,true),
.last 32 (4,true),
.cycle 7 12 true (-2),
.last 20 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 673, 1, 128, 8192, 16384, 8, 160, 33, 16777216, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 11315264, 25427968, 17301504, 16777216],[128, 32, 640, 1, 16777216, 512, 8192, 32, 16777216, 1, 16777216, 32768, 524288, 2048, 16777216, 64, 16777216, 2097152, 524288, 8388608, 19398656, 262144, 16777216, 2097152, 16777216],33503296⟩,
.last 19 (4,true),
.last 21 (4,true)
])
theorem kid11_part109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part109) = true := by rfl

def kid11_part110 : Audit := .split 12 (4,true) (byMove [
.cycle 1 17 true (-1),
.last 20 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 37 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.last 27 (5,true),
.last 19 (5,true),
.last 24 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 28 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (0),
.last 17 (5,true),
.last 21 (5,true),
.cycle 11 2 true (0)
])
theorem kid11_part110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part110) = true := by rfl

def kid11_part111 : Audit := .cycle 1 11 true (1)
theorem kid11_part111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part111) = true := by rfl

def kid11_part112 : Audit := .cycle 7 4 true (2)
theorem kid11_part112_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part112) = true := by rfl

def kid11_part113 : Audit := .cycle 2 10 true (1)
theorem kid11_part113_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part113) = true := by rfl

def kid11_part114 : Audit := .cycle 0 12 true (0)
theorem kid11_part114_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part114) = true := by rfl

def kid11_part115 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 17 true (0),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 0 20 true (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 22 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 2 true (3)
])
theorem kid11_part115_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part115) = true := by rfl

def kid11_part116 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 17 true (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 31 (4,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 17 (4,true),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 13 (4,true)
])
theorem kid11_part116_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part116) = true := by rfl

def kid11_part92 : Audit := .split 10 (2,true) (byMove [(kid11_part93),(kid11_part94),(kid11_part95),(kid11_part96),(kid11_part97),(kid11_part98),(kid11_part99),(kid11_part100),(kid11_part101),(kid11_part102),(kid11_part103),(kid11_part104),(kid11_part105),(kid11_part106),(kid11_part107),(kid11_part108),(kid11_part109),(kid11_part110),(kid11_part111),(kid11_part112),(kid11_part113),(kid11_part114),(kid11_part115),(kid11_part116)])

theorem kid11_part92_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part92) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part93),(kid11_part94),(kid11_part95),(kid11_part96),(kid11_part97),(kid11_part98),(kid11_part99),(kid11_part100),(kid11_part101),(kid11_part102),(kid11_part103),(kid11_part104),(kid11_part105),(kid11_part106),(kid11_part107),(kid11_part108),(kid11_part109),(kid11_part110),(kid11_part111),(kid11_part112),(kid11_part113),(kid11_part114),(kid11_part115),(kid11_part116)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part93_checked

  · exact kid11_part99_checked

  · exact kid11_part105_checked

  · exact kid11_part111_checked

  · exact kid11_part94_checked

  · exact kid11_part100_checked

  · exact kid11_part106_checked

  · exact kid11_part112_checked

  · exact kid11_part95_checked

  · exact kid11_part101_checked

  · exact kid11_part107_checked

  · exact kid11_part113_checked

  · exact kid11_part96_checked

  · exact kid11_part102_checked

  · exact kid11_part108_checked

  · exact kid11_part114_checked

  · exact kid11_part97_checked

  · exact kid11_part103_checked

  · exact kid11_part109_checked

  · exact kid11_part115_checked

  · exact kid11_part98_checked

  · exact kid11_part104_checked

  · exact kid11_part110_checked

  · exact kid11_part116_checked

def kid11_part117 : Audit := .cycle 1 11 true (1)
theorem kid11_part117_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part117) = true := by rfl

def kid11_part119 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 21 true (0),
.cycle 12 6 true (1),
.cycle 12 8 true (1),
.last 15 (5,true),
.last 21 (5,true),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (2),
.cycle 1 16 true (1)
])
theorem kid11_part119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part119) = true := by rfl

def kid11_part120 : Audit := .cycle 0 14 true (0)
theorem kid11_part120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part120) = true := by rfl

def kid11_part121 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (2),
.cycle 1 20 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 34, 34, 256, 8192, 16384, 8, 128, 34, 256, 33554432, 67108864, 2097152, 128, 1073741824, 1073741824, 33554432, 67108864, 2097152, 34, 1073741824, 1073741824, 33554432, 67108864, 134217728, 570425344, 1644167202, 1140850944, 1073741824],[128, 32, 1073741824, 1, 34, 2, 8192, 32, 1073741824, 1, 1073741824, 2, 33554432, 8388608, 1073741824, 262144, 1073741824, 524288, 33554432, 8388608, 1073741824, 262144, 34, 524288, 33554432, 536870912, 1073741824, 16777216, 1644167168, 33554432, 1073741824],2144284736⟩,
.last 27 (2,true),
.cycle 12 7 true (0),
.cycle 23 1 false (1),
.cycle 23 1 false (1),
.last 23 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 35 (2,true),
.cycle 1 20 true (0),
.cycle 9 9 true (0),
.cycle 30 1 false (2)
])
theorem kid11_part121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part121) = true := by rfl

def kid11_part122 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.far true 5 ⟨0,[0, 1, 2, 3, 3, 1, 4, 4, 4, 4],[0, 512, 2097152, 512, 1024, 16, 32768, 512, 2097152, 2097152, 4194304, 65536, 0, 512, 134217728, 512, 1024, 4194304, 1073741824, 1207959552, 2097152, 134217728, 268435456, 268435456, 1207959552, 1207960064, 1210056704, 134217728, 268435456, 268435456, 1073741824],[0, 1024, 2097152, 0, 8, 1073741824, 32768, 1073741824, 4194304, 0, 32768, 1073741824, 0, 1024, 2097152, 512, 2097152, 1073741824, 1073741824, 1342177280, 1075838976, 512, 134217728, 1073741824, 1207959552, 1342177280, 1478492160, 1207959552, 134217728, 1073741824, 1073741824],1191968768⟩,
.last 23 (5,true),
.cycle 3 13 true (0),
.last 22 (5,true),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 17 (5,true),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 7 13 true (0),
.cycle 0 19 true (0)
])
theorem kid11_part122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part122) = true := by rfl

def kid11_part123 : Audit := .cycle 13 1 false (-1)
theorem kid11_part123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part123) = true := by rfl

def kid11_part124 : Audit := .cycle 14 1 false (-2)
theorem kid11_part124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part124) = true := by rfl

def kid11_part125 : Audit := .cycle 1 11 true (1)
theorem kid11_part125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part125) = true := by rfl

def kid11_part126 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 1 19 true (0),
.cycle 21 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 32 1 false (6),
.cycle 21 1 false (3),
.cycle 41 1 false (3),
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 1 19 true (0),
.cycle 25 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 51 1 false (7),
.cycle 18 23 true (2)
])
theorem kid11_part126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part126) = true := by rfl

def kid11_part127 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 22 1 false (6),
.last 18 (5,true),
.cycle 7 6 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 23 (5,true)
])
theorem kid11_part127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part127) = true := by rfl

def kid11_part128 : Audit := .cycle 0 12 true (0)
theorem kid11_part128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part128) = true := by rfl

def kid11_part129 : Audit := .cycle 21 1 false (5)
theorem kid11_part129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part129) = true := by rfl

def kid11_part130 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 45 1 false (3)
])
theorem kid11_part130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part130) = true := by rfl

def kid11_part131 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 5 false (2),
.cycle 17 10 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 12 7 true (1),
.cycle 19 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 5 false (2),
.cycle 17 10 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (1),
.cycle 12 10 true (1)
])
theorem kid11_part131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part131) = true := by rfl

def kid11_part132 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.last 19 (5,true),
.last 22 (5,true),
.cycle 0 14 true (0),
.last 20 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.last 18 (5,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid11_part132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part132) = true := by rfl

def kid11_part133 : Audit := .cycle 1 13 true (1)
theorem kid11_part133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part133) = true := by rfl

def kid11_part134 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 25 1 false (1),
.cycle 1 18 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 4, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 25 (2,true),
.cycle 11 7 true (0),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 27 1 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 31 (2,true),
.cycle 1 18 true (0),
.cycle 9 7 true (0),
.cycle 25 1 false (1)
])
theorem kid11_part134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part134) = true := by rfl

def kid11_part135 : Audit := .cycle 13 1 false (-1)
theorem kid11_part135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part135) = true := by rfl

def kid11_part136 : Audit := .cycle 14 1 false (-2)
theorem kid11_part136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part136) = true := by rfl

def kid11_part137 : Audit := .cycle 1 11 true (1)
theorem kid11_part137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part137) = true := by rfl

def kid11_part138 : Audit := .cycle 7 4 true (2)
theorem kid11_part138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part138) = true := by rfl

def kid11_part139 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 2 15 true (1),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 2 12 true (1)
])
theorem kid11_part139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part139) = true := by rfl

def kid11_part140 : Audit := .cycle 0 12 true (0)
theorem kid11_part140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part140) = true := by rfl

def kid11_part141 : Audit := .cycle 9 3 true (2)
theorem kid11_part141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part141) = true := by rfl

def kid11_part142 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 1 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 2 true (2),
.cycle 13 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (2,true),
.cycle 3 9 true (1),
.cycle 16 2 true (4),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 13 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part142) = true := by rfl

def kid11_part118 : Audit := .split 10 (4,true) (byMove [(kid11_part119),(kid11_part120),(kid11_part121),(kid11_part122),(kid11_part123),(kid11_part124),(kid11_part125),(kid11_part126),(kid11_part127),(kid11_part128),(kid11_part129),(kid11_part130),(kid11_part131),(kid11_part132),(kid11_part133),(kid11_part134),(kid11_part135),(kid11_part136),(kid11_part137),(kid11_part138),(kid11_part139),(kid11_part140),(kid11_part141),(kid11_part142)])

theorem kid11_part118_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part118) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part119),(kid11_part120),(kid11_part121),(kid11_part122),(kid11_part123),(kid11_part124),(kid11_part125),(kid11_part126),(kid11_part127),(kid11_part128),(kid11_part129),(kid11_part130),(kid11_part131),(kid11_part132),(kid11_part133),(kid11_part134),(kid11_part135),(kid11_part136),(kid11_part137),(kid11_part138),(kid11_part139),(kid11_part140),(kid11_part141),(kid11_part142)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part119_checked

  · exact kid11_part125_checked

  · exact kid11_part131_checked

  · exact kid11_part137_checked

  · exact kid11_part120_checked

  · exact kid11_part126_checked

  · exact kid11_part132_checked

  · exact kid11_part138_checked

  · exact kid11_part121_checked

  · exact kid11_part127_checked

  · exact kid11_part133_checked

  · exact kid11_part139_checked

  · exact kid11_part122_checked

  · exact kid11_part128_checked

  · exact kid11_part134_checked

  · exact kid11_part140_checked

  · exact kid11_part123_checked

  · exact kid11_part129_checked

  · exact kid11_part135_checked

  · exact kid11_part141_checked

  · exact kid11_part124_checked

  · exact kid11_part130_checked

  · exact kid11_part136_checked

  · exact kid11_part142_checked

def kid11_part144 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 12 6 true (1),
.cycle 12 8 true (1),
.cycle 0 16 true (0),
.cycle 10 34 true (-1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 12 4 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (2),
.last 15 (4,true)
])
theorem kid11_part144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part144) = true := by rfl

def kid11_part145 : Audit := .cycle 0 14 true (0)
theorem kid11_part145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part145) = true := by rfl

def kid11_part146 : Audit := .cycle 28 1 false (2)
theorem kid11_part146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part146) = true := by rfl

def kid11_part147 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.far true 5 ⟨0,[0, 1, 0, 2, 3, 3, 4, 4, 4, 4],[0, 512, 2129920, 512, 2048, 16, 8, 512, 32768, 32768, 131072, 16, 0, 1073741824, 0, 2097152, 8388608, 4194304, 1073741824, 512, 134250496, 134217728, 536870912, 268435456, 1207959552, 1207960064, 1207959552, 134217728, 536870912, 268435456, 1073741824],[0, 2048, 32768, 512, 1073741824, 8, 8, 512, 16, 0, 1073741824, 8, 0, 512, 32768, 512, 1073741824, 2097152, 1073741824, 671088640, 1073774592, 0, 1073741824, 134217728, 1207959552, 671088640, 1476427776, 1207959552, 1073741824, 134217728, 1073741824],1191452672⟩,
.cycle 1 26 true (0),
.cycle 3 13 true (0),
.last 18 (4,true),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 1 20 true (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.last 16 (4,true),
.cycle 23 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 7 13 true (0),
.last 17 (4,true)
])
theorem kid11_part147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part147) = true := by rfl

def kid11_part148 : Audit := .cycle 13 2 false (-1)
theorem kid11_part148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part148) = true := by rfl

def kid11_part149 : Audit := .split 12 (4,true) (byMove [
.cycle 14 24 true (-1),
.cycle 23 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 31 2 false (1),
.last 17 (2,true),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
])
theorem kid11_part149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part149) = true := by rfl

def kid11_part150 : Audit := .cycle 1 11 true (1)
theorem kid11_part150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part150) = true := by rfl

def kid11_part151 : Audit := .cycle 18 2 false (2)
theorem kid11_part151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part151) = true := by rfl

def kid11_part152 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 18 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34734080, 1075183617, 1075839112, 2, 4, 32768, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 131072, 1073741824, 2097160, 128, 256, 2097152, 1048576, 1074135041, 1075839112, 2, 4, 32768, 128, 1048576, 1073741824, 1073741824],[128, 32, 4, 1, 1073741824, 4, 2, 131072, 16384, 4096, 1073741824, 16384, 33554432, 8388608, 1048576, 262144, 1073741824, 1048576, 128, 8388608, 1048576, 262144, 1073741824, 1048576, 2, 131072, 16384, 4096, 1073741824, 16384, 1073741824],1623263280⟩,
.cycle 10 9 true (0),
.last 16 (4,true),
.cycle 18 2 false (2),
.cycle 7 6 true (2),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34734084, 1075183621, 1075839112, 2, 4, 32768, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 131072, 1073741824, 2097160, 128, 256, 2097152, 1048580, 1074135041, 1075839112, 2, 4, 32768, 128, 1048580, 1073741824, 1073741824],[128, 32, 1048580, 1, 1073741824, 4, 2, 131072, 1048580, 4096, 1073741824, 16384, 33554432, 8388608, 1048580, 262144, 1073741824, 1048576, 128, 8388608, 1048580, 262144, 1073741824, 1048576, 2, 131072, 1048576, 4096, 1073741824, 16384, 1073741824],1623263280⟩,
.cycle 0 14 true (0),
.cycle 10 16 true (0),
.last 14 (4,true),
.cycle 16 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 13 (4,true)
])
theorem kid11_part152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part152) = true := by rfl

def kid11_part153 : Audit := .cycle 0 12 true (0)
theorem kid11_part153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part153) = true := by rfl

def kid11_part154 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 10 9 true (0),
.cycle 17 2 false (1),
.cycle 18 2 false (2),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 2 true (3)
])
theorem kid11_part154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part154) = true := by rfl

def kid11_part155 : Audit := .cycle 18 2 false (2)
theorem kid11_part155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part155) = true := by rfl

def kid11_part156 : Audit := .cycle 12 8 true (1)
theorem kid11_part156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part156) = true := by rfl

def kid11_part157 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 1 13 true (1),
.last 17 (4,true),
.cycle 10 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 10 true (1),
.cycle 10 14 true (1),
.cycle 10 4 true (1),
.cycle 22 10 true (0),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 1 13 true (1),
.cycle 10 8 true (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 19 (4,true)
])
theorem kid11_part157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part157) = true := by rfl

def kid11_part158 : Audit := .cycle 1 13 true (1)
theorem kid11_part158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part158) = true := by rfl

def kid11_part159 : Audit := .cycle 23 1 false (1)
theorem kid11_part159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part159) = true := by rfl

def kid11_part160 : Audit := .cycle 13 2 false (-1)
theorem kid11_part160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part160) = true := by rfl

def kid11_part161 : Audit := .split 12 (4,true) (byMove [
.cycle 1 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 23 2 false (1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 27 2 false (1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 25 2 false (-1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 27 2 false (1),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
])
theorem kid11_part161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part161) = true := by rfl

def kid11_part162 : Audit := .cycle 1 11 true (1)
theorem kid11_part162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part162) = true := by rfl

def kid11_part163 : Audit := .cycle 7 4 true (2)
theorem kid11_part163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part163) = true := by rfl

def kid11_part164 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 16 (4,true),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 13 (4,true)
])
theorem kid11_part164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part164) = true := by rfl

def kid11_part165 : Audit := .cycle 0 12 true (0)
theorem kid11_part165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part165) = true := by rfl

def kid11_part166 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 9 16 true (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 2 false (-1),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (2),
.cycle 3 9 true (1),
.cycle 23 2 false (1),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.cycle 9 5 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 17 2 false (-1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 2 true (3)
])
theorem kid11_part166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part166) = true := by rfl

def kid11_part167 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 28 true (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 21 2 false (-1),
.cycle 19 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 22 true (2),
.cycle 3 11 true (1),
.cycle 27 2 false (1),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 25 2 false (-1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part167) = true := by rfl

def kid11_part143 : Audit := .split 10 (5,true) (byMove [(kid11_part144),(kid11_part145),(kid11_part146),(kid11_part147),(kid11_part148),(kid11_part149),(kid11_part150),(kid11_part151),(kid11_part152),(kid11_part153),(kid11_part154),(kid11_part155),(kid11_part156),(kid11_part157),(kid11_part158),(kid11_part159),(kid11_part160),(kid11_part161),(kid11_part162),(kid11_part163),(kid11_part164),(kid11_part165),(kid11_part166),(kid11_part167)])

theorem kid11_part143_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part143) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part144),(kid11_part145),(kid11_part146),(kid11_part147),(kid11_part148),(kid11_part149),(kid11_part150),(kid11_part151),(kid11_part152),(kid11_part153),(kid11_part154),(kid11_part155),(kid11_part156),(kid11_part157),(kid11_part158),(kid11_part159),(kid11_part160),(kid11_part161),(kid11_part162),(kid11_part163),(kid11_part164),(kid11_part165),(kid11_part166),(kid11_part167)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part144_checked

  · exact kid11_part150_checked

  · exact kid11_part156_checked

  · exact kid11_part162_checked

  · exact kid11_part145_checked

  · exact kid11_part151_checked

  · exact kid11_part157_checked

  · exact kid11_part163_checked

  · exact kid11_part146_checked

  · exact kid11_part152_checked

  · exact kid11_part158_checked

  · exact kid11_part164_checked

  · exact kid11_part147_checked

  · exact kid11_part153_checked

  · exact kid11_part159_checked

  · exact kid11_part165_checked

  · exact kid11_part148_checked

  · exact kid11_part154_checked

  · exact kid11_part160_checked

  · exact kid11_part166_checked

  · exact kid11_part149_checked

  · exact kid11_part155_checked

  · exact kid11_part161_checked

  · exact kid11_part167_checked

def kid11_part168 : Audit := .cycle 0 10 true (0)
theorem kid11_part168_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part168) = true := by rfl

def kid11_part169 : Audit := .cycle 1 9 true (1)
theorem kid11_part169_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part169) = true := by rfl

def kid11_part170 : Audit := .cycle 2 8 true (1)
theorem kid11_part170_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part170) = true := by rfl

def kid11_part171 : Audit := .cycle 1 12 true (1)
theorem kid11_part171_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part171) = true := by rfl

def kid11_part172 : Audit := .cycle 9 1 true (3)
theorem kid11_part172_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part172) = true := by rfl

def kid11_part174 : Audit := .cycle 1 12 true (1)
theorem kid11_part174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part174) = true := by rfl

def kid11_part175 : Audit := .cycle 1 16 true (1)
theorem kid11_part175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part175) = true := by rfl

def kid11_part176 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.last 23 (5,true),
.cycle 33 1 false (1),
.cycle 21 7 false (2),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 29 1 false (1)
])
theorem kid11_part176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part176) = true := by rfl

def kid11_part177 : Audit := .cycle 0 13 true (0)
theorem kid11_part177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part177) = true := by rfl

def kid11_part178 : Audit := .cycle 16 3 false (0)
theorem kid11_part178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part178) = true := by rfl

def kid11_part179 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 4 false (0),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 12 7 true (0),
.cycle 21 4 false (2),
.cycle 17 4 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 4 false (-1),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 15 4 false (1)
])
theorem kid11_part179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part179) = true := by rfl

def kid11_part180 : Audit := .cycle 0 12 true (0)
theorem kid11_part180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part180) = true := by rfl

def kid11_part181 : Audit := .cycle 1 11 true (1)
theorem kid11_part181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part181) = true := by rfl

def kid11_part182 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 35 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (2,true),
.cycle 13 7 true (2),
.last 34 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 8, 64],[2, 32, 64, 1, 4, 32, 64],64⟩,
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 10 22 true (2)
])
theorem kid11_part182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part182) = true := by rfl

def kid11_part183 : Audit := .cycle 3 9 true (1)
theorem kid11_part183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part183) = true := by rfl

def kid11_part184 : Audit := .cycle 9 3 true (3)
theorem kid11_part184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part184) = true := by rfl

def kid11_part185 : Audit := .cycle 8 4 true (3)
theorem kid11_part185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part185) = true := by rfl

def kid11_part186 : Audit := .cycle 6 6 true (2)
theorem kid11_part186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part186) = true := by rfl

def kid11_part187 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.last 18 (2,true),
.last 25 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.last 18 (2,true),
.last 19 (2,true),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.last 18 (2,true),
.last 25 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (2),
.last 17 (2,true)
])
theorem kid11_part187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part187) = true := by rfl

def kid11_part188 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 13 12 true (-2),
.last 20 (5,true),
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
.last 14 (5,true),
.last 19 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 13 (5,true)
])
theorem kid11_part188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part188) = true := by rfl

def kid11_part189 : Audit := .cycle 1 13 true (1)
theorem kid11_part189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part189) = true := by rfl

def kid11_part190 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 20 7 false (0),
.last 15 (2,true),
.cycle 7 10 true (1),
.cycle 16 3 false (0),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 1 21 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 5 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.last 18 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 16 3 false (0),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 16 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid11_part190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part190) = true := by rfl

def kid11_part191 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.last 17 (2,true),
.cycle 17 4 false (0),
.cycle 13 4 false (1),
.cycle 1 13 true (1),
.cycle 24 4 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 4 false (1),
.cycle 24 4 false (2),
.cycle 14 10 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 27 1 false (1),
.cycle 19 4 false (-1),
.cycle 13 4 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part191) = true := by rfl

def kid11_part192 : Audit := .cycle 0 12 true (0)
theorem kid11_part192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part192) = true := by rfl

def kid11_part193 : Audit := .cycle 1 11 true (1)
theorem kid11_part193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part193) = true := by rfl

def kid11_part194 : Audit := .cycle 2 10 true (1)
theorem kid11_part194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part194) = true := by rfl

def kid11_part195 : Audit := .cycle 1 14 true (1)
theorem kid11_part195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part195) = true := by rfl

def kid11_part196 : Audit := .cycle 9 3 true (3)
theorem kid11_part196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part196) = true := by rfl

def kid11_part197 : Audit := .cycle 10 2 true (3)
theorem kid11_part197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part197) = true := by rfl

def kid11_part173 : Audit := .split 11 (4,true) (byMove [(kid11_part174),(kid11_part175),(kid11_part176),(kid11_part177),(kid11_part178),(kid11_part179),(kid11_part180),(kid11_part181),(kid11_part182),(kid11_part183),(kid11_part184),(kid11_part185),(kid11_part186),(kid11_part187),(kid11_part188),(kid11_part189),(kid11_part190),(kid11_part191),(kid11_part192),(kid11_part193),(kid11_part194),(kid11_part195),(kid11_part196),(kid11_part197)])

theorem kid11_part173_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part173) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some mv)) (byMove [(kid11_part174),(kid11_part175),(kid11_part176),(kid11_part177),(kid11_part178),(kid11_part179),(kid11_part180),(kid11_part181),(kid11_part182),(kid11_part183),(kid11_part184),(kid11_part185),(kid11_part186),(kid11_part187),(kid11_part188),(kid11_part189),(kid11_part190),(kid11_part191),(kid11_part192),(kid11_part193),(kid11_part194),(kid11_part195),(kid11_part196),(kid11_part197)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part174_checked

  · exact kid11_part180_checked

  · exact kid11_part186_checked

  · exact kid11_part192_checked

  · exact kid11_part175_checked

  · exact kid11_part181_checked

  · exact kid11_part187_checked

  · exact kid11_part193_checked

  · exact kid11_part176_checked

  · exact kid11_part182_checked

  · exact kid11_part188_checked

  · exact kid11_part194_checked

  · exact kid11_part177_checked

  · exact kid11_part183_checked

  · exact kid11_part189_checked

  · exact kid11_part195_checked

  · exact kid11_part178_checked

  · exact kid11_part184_checked

  · exact kid11_part190_checked

  · exact kid11_part196_checked

  · exact kid11_part179_checked

  · exact kid11_part185_checked

  · exact kid11_part191_checked

  · exact kid11_part197_checked

def kid11_part5 : Audit := .split 9 (4,false) (byMove [(kid11_part6),(kid11_part7),(kid11_part8),(kid11_part33),(kid11_part34),(kid11_part35),(kid11_part36),(kid11_part37),(kid11_part38),(kid11_part63),(kid11_part64),(kid11_part65),(kid11_part66),(kid11_part67),(kid11_part92),(kid11_part117),(kid11_part118),(kid11_part143),(kid11_part168),(kid11_part169),(kid11_part170),(kid11_part171),(kid11_part172),(kid11_part173)])

theorem kid11_part5_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (kid11_part5) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part6),(kid11_part7),(kid11_part8),(kid11_part33),(kid11_part34),(kid11_part35),(kid11_part36),(kid11_part37),(kid11_part38),(kid11_part63),(kid11_part64),(kid11_part65),(kid11_part66),(kid11_part67),(kid11_part92),(kid11_part117),(kid11_part118),(kid11_part143),(kid11_part168),(kid11_part169),(kid11_part170),(kid11_part171),(kid11_part172),(kid11_part173)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part6_checked

  · exact kid11_part36_checked

  · exact kid11_part66_checked

  · exact kid11_part168_checked

  · exact kid11_part7_checked

  · exact kid11_part37_checked

  · exact kid11_part67_checked

  · exact kid11_part169_checked

  · exact kid11_part8_checked

  · exact kid11_part38_checked

  · exact kid11_part92_checked

  · exact kid11_part170_checked

  · exact kid11_part33_checked

  · exact kid11_part63_checked

  · exact kid11_part117_checked

  · exact kid11_part171_checked

  · exact kid11_part34_checked

  · exact kid11_part64_checked

  · exact kid11_part118_checked

  · exact kid11_part172_checked

  · exact kid11_part35_checked

  · exact kid11_part65_checked

  · exact kid11_part143_checked

  · exact kid11_part173_checked

def kid11_part199 : Audit := .cycle 0 11 true (0)
theorem kid11_part199_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part199) = true := by rfl

def kid11_part200 : Audit := .cycle 1 10 true (1)
theorem kid11_part200_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part200) = true := by rfl

def kid11_part201 : Audit := .cycle 21 1 false (1)
theorem kid11_part201_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part201) = true := by rfl

def kid11_part202 : Audit := .cycle 1 13 true (0)
theorem kid11_part202_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part202) = true := by rfl

def kid11_part203 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 1 false (1),
.split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
]),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (4),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 23 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 1 false (0),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 15 1 false (-1)
]),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (0),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 16 1 false (0),
.cycle 13 6 false (2),
.split 16 (2,true) (byMove [
.cycle 1 17 false (4),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 0 17 true (-1),
.cycle 13 13 true (-1),
.cycle 10 14 true (-1),
.cycle 13 11 false (2),
.cycle 14 3 true (-1),
.cycle 13 6 false (1),
.cycle 13 8 false (1),
.cycle 12 5 false (1),
.cycle 1 20 true (-2),
.cycle 1 18 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 10 23 false (5),
.cycle 10 19 false (4),
.cycle 2 15 false (4),
.cycle 1 19 true (-1),
.cycle 10 9 false (2),
.last 19 (4,true)
]),
.split 12 (2,true) (byMove [
.cycle 14 16 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 14 1 false (2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 17 true (-1),
.cycle 10 5 false (2),
.cycle 0 28 true (-2),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 0 20 true (-2),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 1 13 true (0),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 14 1 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 17 1 false (-1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 3 true (0),
.cycle 17 1 false (-1)
]),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 23 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 23 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.cycle 15 1 false (1),
.cycle 18 3 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 22 3 false (2),
.cycle 1 17 true (0),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
])
])
theorem kid11_part203_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part203) = true := by rfl

def kid11_part204 : Audit := .cycle 13 1 false (-1)
theorem kid11_part204_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part204) = true := by rfl

def kid11_part205 : Audit := .cycle 0 11 true (0)
theorem kid11_part205_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part205) = true := by rfl

def kid11_part206 : Audit := .cycle 1 10 true (1)
theorem kid11_part206_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part206) = true := by rfl

def kid11_part207 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 10 18 true (0),
.cycle 30 1 false (4),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 32 1 false (4),
.cycle 1 24 true (0),
.last 23 (4,true),
.cycle 25 1 false (3),
.cycle 0 22 true (0),
.last 47 (4,true),
.cycle 11 11 true (0),
.cycle 10 18 true (0),
.cycle 21 1 true (3),
.cycle 27 1 false (3),
.cycle 10 24 true (0),
.last 24 (4,true),
.cycle 0 24 true (0),
.cycle 30 1 false (4),
.last 23 (4,true),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 0 45 true (0),
.cycle 1 24 true (0),
.cycle 21 1 true (3),
.cycle 9 13 true (0)
]),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 46, 64],[2, 32, 2, 1, 64, 4, 64],80⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 46, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 12 9 true (0),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.last 44 (4,true),
.cycle 11 11 true (0),
.cycle 10 18 true (0),
.last 25 (4,true),
.cycle 27 1 false (3),
.cycle 0 22 true (0),
.last 46 (4,true),
.last 34 (4,true),
.last 32 (4,true),
.cycle 21 1 true (5),
.cycle 29 1 false (3),
.last 38 (4,true),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 13 9 true (0),
.last 25 (4,true),
.cycle 27 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 44 (4,true),
.cycle 1 24 true (0),
.cycle 21 1 true (5),
.last 36 (4,true)
]),
.cycle 27 1 false (3),
.cycle 7 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 46, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.split 21 (4,false) (byMove [
.last 25 (4,true),
.cycle 0 25 true (0),
.cycle 10 18 true (0),
.last 27 (4,true),
.last 23 (4,true),
.cycle 25 1 false (3),
.cycle 1 22 true (0),
.cycle 29 1 false (3),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.last 22 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 44, 128, 256, 8, 128, 32, 8, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 10 14 true (0),
.last 24 (4,true),
.cycle 1 24 true (0),
.cycle 10 16 true (0),
.last 23 (4,true),
.cycle 1 26 true (0),
.cycle 1 22 true (0),
.cycle 7 15 true (0),
.last 23 (4,true),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 10 20 true (0)
]),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 42 true (0),
.cycle 1 23 true (0),
.split 21 (4,false) (byMove [
.cycle 1 22 true (0),
.cycle 29 1 false (3),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.last 22 (4,true),
.last 34 (4,true),
.cycle 0 22 true (0),
.last 43 (4,true),
.cycle 10 19 true (0),
.last 42 (4,true),
.cycle 21 1 true (5),
.last 36 (4,true),
.last 38 (4,true),
.last 36 (4,true),
.last 23 (4,true),
.cycle 1 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 24 true (0),
.cycle 21 1 true (5),
.cycle 10 21 true (0)
]),
.cycle 10 32 true (0)
])
theorem kid11_part207_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part207) = true := by rfl

def kid11_part208 : Audit := .cycle 10 7 true (0)
theorem kid11_part208_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part208) = true := by rfl

def kid11_part209 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (0),
.cycle 21 1 false (1),
.split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 25 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 25 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 20 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 1 false (2),
.cycle 1 17 true (0),
.cycle 13 2 true (0),
.cycle 17 1 false (1)
]),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 10 29 true (0),
.cycle 0 34 true (0),
.cycle 0 26 true (0),
.cycle 28 1 false (4),
.cycle 1 23 true (0),
.cycle 32 1 false (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 62, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 62, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 10 15 true (0),
.last 24 (2,true),
.cycle 1 25 true (0),
.cycle 10 25 true (0),
.last 24 (2,true),
.cycle 1 29 true (0),
.cycle 1 23 true (0),
.cycle 10 31 true (0),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 10 22 true (0),
.cycle 9 43 true (0)
]),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 10 18 true (0),
.cycle 30 1 false (4),
.cycle 10 18 true (0),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 62, 64],[2, 32, 64, 1, 2, 16, 64],64⟩,
.last 32 (2,true),
.cycle 12 9 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 62, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 27 1 false (3),
.cycle 7 15 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.cycle 0 23 true (0),
.cycle 25 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 42 (2,true),
.cycle 1 23 true (0),
.cycle 3 42 true (0),
.cycle 10 32 true (0)
]),
.cycle 11 1 true (3),
.cycle 18 1 false (2),
.cycle 7 6 true (2),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (2),
.cycle 3 11 true (1),
.cycle 11 3 true (2),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 10 5 true (2),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 10 6 true (2),
.cycle 9 5 true (2)
]),
.cycle 0 14 true (0),
.cycle 10 7 true (0),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 10 23 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 7 true (0),
.cycle 28 1 false (6),
.last 15 (2,true),
.cycle 21 1 false (3),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 10 11 true (-1),
.last 16 (2,true),
.cycle 10 9 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 7 true (0),
.cycle 1 17 true (0),
.last 15 (2,true),
.cycle 5 10 true (0),
.cycle 16 3 true (2),
.cycle 9 14 true (0)
]),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid11_part209_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part209) = true := by rfl

def kid11_part210 : Audit := .cycle 15 1 false (1)
theorem kid11_part210_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part210) = true := by rfl

def kid11_part211 : Audit := .cycle 17 5 false (2)
theorem kid11_part211_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part211) = true := by rfl

def kid11_part212 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 20 1 false (0),
.cycle 15 8 false (2),
.cycle 16 3 false (1),
.last 15 (4,false),
.cycle 1 15 true (0),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 17 5 false (1)
]),
.cycle 15 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (4,true),
.cycle 10 10 true (1),
.cycle 13 1 true (3),
.cycle 19 7 false (3),
.cycle 10 10 true (1),
.cycle 11 3 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 9 5 true (1)
]),
.cycle 17 5 false (2),
.cycle 19 7 false (2),
.cycle 10 4 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 23 1 false (-1),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 10 4 true (1),
.cycle 10 6 true (0),
.cycle 16 3 false (1),
.last 15 (4,false),
.cycle 23 1 false (-1),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 10 6 true (1)
]),
.cycle 15 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 10 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (1),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 10 8 true (1),
.cycle 10 10 true (1),
.cycle 10 5 true (1),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 10 7 true (1)
]),
.cycle 10 6 true (1)
])
theorem kid11_part212_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part212) = true := by rfl

def kid11_part213 : Audit := .cycle 0 13 true (0)
theorem kid11_part213_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part213) = true := by rfl

def kid11_part214 : Audit := .cycle 18 1 false (0)
theorem kid11_part214_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part214) = true := by rfl

def kid11_part216 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 13 14 true (1),
.cycle 10 12 true (0),
.cycle 3 12 true (0),
.cycle 0 16 true (0),
.last 18 (4,true),
.last 20 (4,true),
.cycle 10 6 true (0),
.cycle 13 13 false (3),
.cycle 1 16 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 1 16 true (0),
.last 17 (4,true)
])
theorem kid11_part216_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part216) = true := by rfl

def kid11_part217 : Audit := .cycle 13 1 false (1)
theorem kid11_part217_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part217) = true := by rfl

def kid11_part218 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 20 1 false (0),
.cycle 10 22 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
])
theorem kid11_part218_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part218) = true := by rfl

def kid11_part219 : Audit := .cycle 19 1 false (-1)
theorem kid11_part219_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part219) = true := by rfl

def kid11_part220 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.cycle 11 2 true (0),
.cycle 15 1 false (-1)
])
theorem kid11_part220_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part220) = true := by rfl

def kid11_part221 : Audit := .cycle 14 1 false (-2)
theorem kid11_part221_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part221) = true := by rfl

def kid11_part222 : Audit := .cycle 1 12 true (1)
theorem kid11_part222_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part222) = true := by rfl

def kid11_part223 : Audit := .cycle 19 1 false (1)
theorem kid11_part223_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part223) = true := by rfl

def kid11_part224 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 10 11 true (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 36, 4, 44, 8192, 16384, 8, 128, 4, 8, 33554432, 67108864, 2097152, 128, 1048576, 1073741824, 33554432, 67108864, 2097152, 36, 1048576, 1073741824, 33554432, 67108864, 134217728, 1711276032, 67108864, 1847590956, 1073741824],[128, 32, 4, 1, 1073741824, 4, 8192, 32, 4, 1, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1048576, 33554432, 536870912, 67108864, 16777216, 1073741824, 1140850688, 1073741824],2140024896⟩,
.cycle 10 9 true (0),
.last 26 (4,true),
.cycle 19 1 false (1),
.last 18 (4,true),
.cycle 10 6 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 11 true (1),
.cycle 9 4 true (1)
])
theorem kid11_part224_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part224) = true := by rfl

def kid11_part225 : Audit := .cycle 0 13 true (0)
theorem kid11_part225_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part225) = true := by rfl

def kid11_part226 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 13 1 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 10 9 true (0),
.cycle 13 1 true (3),
.cycle 19 1 false (1),
.cycle 10 11 false (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.cycle 9 4 true (1)
])
theorem kid11_part226_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part226) = true := by rfl

def kid11_part227 : Audit := .cycle 10 2 true (1)
theorem kid11_part227_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part227) = true := by rfl

def kid11_part228 : Audit := .cycle 10 4 true (0)
theorem kid11_part228_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part228) = true := by rfl

def kid11_part229 : Audit := .split 16 (2,true) (byMove [
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 1048576, 4398046642176, 524288, 1048576, 32768, 128, 274877906944, 8589934592, 33554432, 67108864, 8, 131072, 274877906944, 131072, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 524288, 1048576, 32768, 128, 274877906944, 8589934592, 33554432, 67108864, 8, 131072, 274877906944, 4398046511104, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 4398046511104],[128, 32, 1048576, 1, 4398046511104, 274877906944, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 274877906944, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 274877906944, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],6631437893664⟩,
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 10 10 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 6 11 false (4),
.last 27 (4,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 1048612, 1048580, 3145772, 8192, 16384, 8, 128, 1048580, 2097160, 33554432, 67108864, 2097152, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 1048612, 67108864, 1073741824, 33554432, 67108864, 134217728, 1712324612, 1141899268, 1848639532, 1073741824],[128, 32, 4, 1, 1073741824, 1048580, 8192, 32, 4, 1, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 68157444, 33554432, 536870912, 67108864, 16777216, 1073741824, 1141899268, 1073741824],2144219200⟩,
.cycle 1 18 true (-1),
.last 17 (4,true),
.cycle 10 7 false (2),
.cycle 10 9 false (2),
.cycle 12 5 false (1),
.cycle 10 12 true (-2),
.cycle 10 10 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.last 22 (4,true),
.cycle 10 11 false (2),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 1048576, 4398046642176, 524288, 1048576, 32768, 128, 274877906944, 8589934592, 33554432, 67108864, 8, 131072, 274877906944, 131072, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 524288, 1048576, 32768, 128, 274877906944, 8589934592, 33554432, 67108864, 8, 131072, 274877906944, 4398046511104, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 4398046511104],[128, 32, 256, 1, 4398046511104, 274877906944, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 67108864, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 67108864, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],6631437893664⟩,
.cycle 1 18 true (-1),
.last 17 (4,true),
.last 18 (4,true)
])
theorem kid11_part229_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part229) = true := by rfl

def kid11_part230 : Audit := .split 12 (2,true) (byMove [
.cycle 14 19 true (0),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 13 1 false (-1),
.cycle 1 21 true (-1),
.cycle 1 18 true (0),
.cycle 16 1 false (4),
.cycle 1 14 true (0),
.last 13 (4,true),
.cycle 1 25 true (-1),
.cycle 10 5 false (2),
.cycle 10 12 true (-2),
.cycle 1 23 true (-1),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 10 4 true (0),
.cycle 2 13 true (0),
.cycle 1 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid11_part230_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part230) = true := by rfl

def kid11_part231 : Audit := .cycle 19 1 false (-1)
theorem kid11_part231_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part231) = true := by rfl

def kid11_part232 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.cycle 15 1 false (1),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 13 3 true (1),
.cycle 12 2 true (0)
])
theorem kid11_part232_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part232) = true := by rfl

def kid11_part233 : Audit := .cycle 14 1 false (-2)
theorem kid11_part233_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part233) = true := by rfl

def kid11_part234 : Audit := .cycle 1 12 true (1)
theorem kid11_part234_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part234) = true := by rfl

def kid11_part235 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 19 (2,true),
.cycle 17 1 false (-1),
.cycle 1 17 true (0),
.cycle 18 1 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 1 18 true (0),
.cycle 17 5 false (2),
.cycle 10 9 false (3),
.last 18 (2,true),
.cycle 1 19 true (-1),
.cycle 17 1 false (-1),
.cycle 10 9 false (3),
.cycle 17 1 false (-1),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 1 18 true (0),
.cycle 15 2 true (0)
])
theorem kid11_part235_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part235) = true := by rfl

def kid11_part236 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.last 16 (4,true),
.last 18 (4,true),
.cycle 10 4 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 15 (4,true)
])
theorem kid11_part236_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part236) = true := by rfl

def kid11_part237 : Audit := .cycle 0 13 true (0)
theorem kid11_part237_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part237) = true := by rfl

def kid11_part238 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 15 1 true (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 13 1 true (3),
.cycle 17 5 false (2),
.cycle 10 11 false (3),
.cycle 10 4 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.cycle 14 2 true (1)
])
theorem kid11_part238_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part238) = true := by rfl

def kid11_part239 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 9 7 true (1),
.cycle 10 4 true (1),
.cycle 10 6 true (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 17 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 5 true (1),
.cycle 12 2 true (1)
])
theorem kid11_part239_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part239) = true := by rfl

def kid11_part215 : Audit := .split 11 (4,false) (byMove [(kid11_part216),(kid11_part217),(kid11_part218),(kid11_part219),(kid11_part220),(kid11_part221),(kid11_part222),(kid11_part223),(kid11_part224),(kid11_part225),(kid11_part226),(kid11_part227),(kid11_part228),(kid11_part229),(kid11_part230),(kid11_part231),(kid11_part232),(kid11_part233),(kid11_part234),(kid11_part235),(kid11_part236),(kid11_part237),(kid11_part238),(kid11_part239)])

theorem kid11_part215_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part215) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part216),(kid11_part217),(kid11_part218),(kid11_part219),(kid11_part220),(kid11_part221),(kid11_part222),(kid11_part223),(kid11_part224),(kid11_part225),(kid11_part226),(kid11_part227),(kid11_part228),(kid11_part229),(kid11_part230),(kid11_part231),(kid11_part232),(kid11_part233),(kid11_part234),(kid11_part235),(kid11_part236),(kid11_part237),(kid11_part238),(kid11_part239)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part216_checked

  · exact kid11_part222_checked

  · exact kid11_part228_checked

  · exact kid11_part234_checked

  · exact kid11_part217_checked

  · exact kid11_part223_checked

  · exact kid11_part229_checked

  · exact kid11_part235_checked

  · exact kid11_part218_checked

  · exact kid11_part224_checked

  · exact kid11_part230_checked

  · exact kid11_part236_checked

  · exact kid11_part219_checked

  · exact kid11_part225_checked

  · exact kid11_part231_checked

  · exact kid11_part237_checked

  · exact kid11_part220_checked

  · exact kid11_part226_checked

  · exact kid11_part232_checked

  · exact kid11_part238_checked

  · exact kid11_part221_checked

  · exact kid11_part227_checked

  · exact kid11_part233_checked

  · exact kid11_part239_checked

def kid11_part240 : Audit := .cycle 13 1 false (-1)
theorem kid11_part240_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part240) = true := by rfl

def kid11_part241 : Audit := .cycle 0 11 true (0)
theorem kid11_part241_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part241) = true := by rfl

def kid11_part242 : Audit := .cycle 1 10 true (1)
theorem kid11_part242_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part242) = true := by rfl

def kid11_part243 : Audit := .cycle 2 9 true (1)
theorem kid11_part243_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part243) = true := by rfl

def kid11_part244 : Audit := .cycle 1 13 true (1)
theorem kid11_part244_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part244) = true := by rfl

def kid11_part245 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 19 1 false (1),
.split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 10 9 true (0),
.cycle 10 11 true (0),
.cycle 19 1 false (1),
.cycle 21 7 false (2),
.cycle 10 6 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
]),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 20 true (0),
.cycle 10 9 true (0),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
]),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.cycle 10 3 true (2),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 10 9 true (0),
.cycle 0 19 true (0),
.cycle 13 10 true (-2),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 24 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 10 5 true (1),
.last 17 (4,true),
.cycle 1 15 true (1),
.cycle 10 7 true (0),
.last 21 (4,true),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2)
]),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 9 true (0),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 1 false (5),
.cycle 10 3 true (2),
.cycle 10 5 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 7 true (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 3 true (2),
.cycle 10 3 true (2)
]),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 1 false (-2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (2),
.cycle 3 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 10 5 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 1 false (-2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (2),
.cycle 9 5 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid11_part245_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part245) = true := by rfl

def kid11_part246 : Audit := .cycle 9 2 true (2)
theorem kid11_part246_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part246) = true := by rfl

def kid11_part198 : Audit := .split 10 (5,true) (byMove [(kid11_part199),(kid11_part200),(kid11_part201),(kid11_part202),(kid11_part203),(kid11_part204),(kid11_part205),(kid11_part206),(kid11_part207),(kid11_part208),(kid11_part209),(kid11_part210),(kid11_part211),(kid11_part212),(kid11_part213),(kid11_part214),(kid11_part215),(kid11_part240),(kid11_part241),(kid11_part242),(kid11_part243),(kid11_part244),(kid11_part245),(kid11_part246)])

theorem kid11_part198_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (kid11_part198) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part199),(kid11_part200),(kid11_part201),(kid11_part202),(kid11_part203),(kid11_part204),(kid11_part205),(kid11_part206),(kid11_part207),(kid11_part208),(kid11_part209),(kid11_part210),(kid11_part211),(kid11_part212),(kid11_part213),(kid11_part214),(kid11_part215),(kid11_part240),(kid11_part241),(kid11_part242),(kid11_part243),(kid11_part244),(kid11_part245),(kid11_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part199_checked

  · exact kid11_part205_checked

  · exact kid11_part211_checked

  · exact kid11_part241_checked

  · exact kid11_part200_checked

  · exact kid11_part206_checked

  · exact kid11_part212_checked

  · exact kid11_part242_checked

  · exact kid11_part201_checked

  · exact kid11_part207_checked

  · exact kid11_part213_checked

  · exact kid11_part243_checked

  · exact kid11_part202_checked

  · exact kid11_part208_checked

  · exact kid11_part214_checked

  · exact kid11_part244_checked

  · exact kid11_part203_checked

  · exact kid11_part209_checked

  · exact kid11_part215_checked

  · exact kid11_part245_checked

  · exact kid11_part204_checked

  · exact kid11_part210_checked

  · exact kid11_part240_checked

  · exact kid11_part246_checked

def kid11_part247 : Audit := .cycle 0 9 true (0)
theorem kid11_part247_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,0⟩)) (kid11_part247) = true := by rfl

def kid11_part248 : Audit := .cycle 1 8 true (1)
theorem kid11_part248_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,1⟩)) (kid11_part248) = true := by rfl

def kid11_part250 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 0 32 true (0),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.last 24 (4,false),
.cycle 1 23 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 0 30 true (0),
.cycle 3 19 true (1),
.last 22 (4,false),
.cycle 8 14 true (2),
.cycle 6 16 true (2),
.cycle 0 24 true (0),
.cycle 7 20 true (2),
.cycle 1 23 true (1),
.last 24 (4,false),
.cycle 39 5 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 22 (4,false),
.cycle 0 31 true (0)
]),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 29 true (0),
.cycle 3 18 true (1),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 23 (4,true),
.cycle 0 31 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 9 13 true (2),
.cycle 0 29 true (0),
.cycle 21 1 true (7),
.last 36 (4,true),
.cycle 7 16 true (2),
.cycle 19 3 true (5),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (4,true),
.cycle 20 3 true (6),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 21 1 true (7),
.cycle 0 31 true (0)
]),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 0 23 true (0),
.cycle 0 29 true (0),
.cycle 1 22 true (1),
.split 21 (4,true) (byMove [
.cycle 19 4 true (4),
.last 25 (4,false),
.cycle 39 1 false (1),
.cycle 7 17 true (2),
.last 24 (4,false),
.cycle 0 27 true (0),
.cycle 1 22 true (1),
.cycle 0 40 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 0 25 true (0),
.cycle 16 6 true (4),
.cycle 0 29 true (0),
.cycle 5 17 true (1),
.last 24 (4,false),
.cycle 39 5 false (2),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 20 2 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 1 23 true (1)
]),
.cycle 19 4 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.split 21 (4,false) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 20 2 true (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 1 23 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 0 30 true (0),
.cycle 3 19 true (1),
.cycle 21 1 true (7),
.cycle 8 14 true (2),
.cycle 6 16 true (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 19 5 true (5),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 21 1 true (7),
.cycle 0 31 true (0)
]),
.cycle 0 30 true (0)
])
theorem kid11_part250_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part250) = true := by rfl

def kid11_part251 : Audit := .cycle 0 21 true (0)
theorem kid11_part251_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part251) = true := by rfl

def kid11_part252 : Audit := .cycle 2 23 true (1)
theorem kid11_part252_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part252) = true := by rfl

def kid11_part253 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.split 23 (4,true) (byMove [
.cycle 1 24 true (1),
.cycle 69 1 false (11),
.last 25 (4,false),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 1 34 true (0),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 1 34 true (1),
.cycle 3 21 true (1),
.last 24 (4,false),
.cycle 8 16 true (2),
.cycle 6 18 true (2),
.cycle 42 1 false (2),
.last 25 (4,false),
.cycle 1 25 true (1),
.last 25 (4,false),
.cycle 0 38 true (0),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.last 24 (4,false),
.cycle 1 35 true (1)
]),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 1 33 true (1),
.cycle 3 20 true (1),
.split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.last 25 (4,true),
.cycle 1 35 true (1),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 9 15 true (2),
.cycle 1 33 true (1),
.cycle 23 1 true (7),
.last 40 (4,true),
.cycle 7 18 true (2),
.cycle 21 3 true (5),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.last 25 (4,true),
.cycle 22 3 true (6),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 23 1 true (7),
.cycle 1 35 true (1)
]),
.cycle 8 15 true (2),
.cycle 6 17 true (2),
.cycle 1 27 true (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.split 23 (4,true) (byMove [
.cycle 20 4 true (4),
.last 27 (4,false),
.last 25 (4,false),
.cycle 7 19 true (2),
.last 25 (4,false),
.cycle 1 45 true (0),
.cycle 1 24 true (1),
.cycle 3 41 true (1),
.last 25 (4,false),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 1 27 true (1),
.cycle 1 29 true (1),
.cycle 42 1 false (2),
.last 25 (4,false),
.cycle 5 19 true (1),
.last 25 (4,false),
.cycle 1 38 true (0),
.cycle 1 24 true (1),
.cycle 7 17 true (2),
.cycle 22 2 true (5),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 0 26 true (0)
]),
.cycle 7 19 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.split 23 (4,false) (byMove [
.cycle 1 24 true (1),
.cycle 7 17 true (2),
.cycle 22 2 true (6),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 1 34 true (1),
.cycle 3 21 true (1),
.cycle 23 1 true (7),
.cycle 8 16 true (2),
.cycle 6 18 true (2),
.cycle 1 28 true (1),
.last 25 (4,true),
.cycle 1 25 true (1),
.last 24 (4,true),
.cycle 7 20 true (2),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 23 1 true (7),
.cycle 1 35 true (1)
]),
.cycle 1 34 true (1)
])
theorem kid11_part253_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part253) = true := by rfl

def kid11_part255 : Audit := .cycle 0 23 true (0)
theorem kid11_part255_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part255) = true := by rfl

def kid11_part256 : Audit := .cycle 0 23 true (0)
theorem kid11_part256_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part256) = true := by rfl

def kid11_part257 : Audit := .split 19 (2,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 28 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 41 1 false (1),
.cycle 34 1 false (2),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 34 1 false (2),
.cycle 0 23 true (0),
.cycle 0 25 true (0),
.cycle 49 1 false (1),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 32 1 false (0),
.cycle 19 2 true (2),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 1 27 true (1),
.cycle 18 2 true (3),
.cycle 0 23 true (0)
])
theorem kid11_part257_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part257) = true := by rfl

def kid11_part258 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 0 33 true (0),
.cycle 3 20 true (1),
.cycle 1 26 true (1),
.cycle 8 15 true (2),
.cycle 6 17 true (2),
.cycle 0 27 true (0),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 0 25 true (0),
.cycle 0 34 true (0)
])
theorem kid11_part258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part258) = true := by rfl

def kid11_part259 : Audit := .split 19 (4,true) (byMove [
.cycle 0 31 true (0),
.last 28 (2,true),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 23 1 false (-1),
.cycle 34 1 false (2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 25 1 false (1),
.cycle 0 23 true (0),
.cycle 0 25 true (0),
.last 21 (2,true),
.last 24 (2,true),
.cycle 28 1 false (0),
.cycle 23 1 false (-1),
.last 21 (2,true),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.last 24 (2,true),
.cycle 18 2 true (3),
.cycle 0 23 true (0)
])
theorem kid11_part259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part259) = true := by rfl

def kid11_part260 : Audit := .cycle 35 1 false (1)
theorem kid11_part260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part260) = true := by rfl

def kid11_part261 : Audit := .cycle 7 13 true (2)
theorem kid11_part261_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part261) = true := by rfl

def kid11_part262 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 1 38 true (1),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 1 29 true (1),
.cycle 3 18 true (1),
.cycle 1 21 true (1),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.cycle 1 24 true (1),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 17 4 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 21 true (1),
.cycle 1 30 true (1)
])
theorem kid11_part262_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part262) = true := by rfl

def kid11_part263 : Audit := .cycle 0 21 true (0)
theorem kid11_part263_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part263) = true := by rfl

def kid11_part264 : Audit := .cycle 3 23 true (1)
theorem kid11_part264_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part264) = true := by rfl

def kid11_part265 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 29 1 true (5),
.cycle 3 18 true (1),
.cycle 21 1 true (5),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 34 (2,true),
.cycle 10 11 true (2),
.cycle 21 1 true (7),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 48, 16, 4, 128, 256, 8, 128, 16, 4, 4096],[128, 32, 4096, 1, 32, 16, 128, 32, 4096, 1, 32, 4, 4096],4096⟩,
.cycle 7 15 true (2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 27 1 true (5),
.cycle 19 2 true (5),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 21 1 true (7),
.cycle 30 1 true (8)
])
theorem kid11_part265_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part265) = true := by rfl

def kid11_part266 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 8 22 true (2),
.cycle 3 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4096, 4096],4096⟩,
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 10 11 true (2),
.last 38 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 32, 1, 4096, 4096, 4096],4096⟩,
.cycle 7 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 23 true (0),
.cycle 8 20 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4096, 4096],4096⟩,
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 8 14 true (2),
.cycle 8 23 true (2)
])
theorem kid11_part266_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part266) = true := by rfl

def kid11_part267 : Audit := .split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 6 26 true (2),
.cycle 3 20 true (1),
.cycle 7 18 true (2),
.cycle 8 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 10 13 true (2),
.cycle 7 18 true (2),
.cycle 20 23 true (3),
.cycle 7 17 true (2),
.cycle 7 22 true (2),
.cycle 0 25 true (0),
.cycle 6 24 true (2),
.cycle 6 22 true (2),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 6 18 true (2),
.cycle 6 27 true (2)
])
theorem kid11_part267_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part267) = true := by rfl

def kid11_part268 : Audit := .split 23 (2,true) (byMove [
.cycle 1 39 true (1),
.cycle 45 1 false (3),
.cycle 49 1 false (1),
.cycle 0 29 true (0),
.last 24 (4,true),
.cycle 27 4 false (1),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.cycle 11 14 true (2),
.cycle 10 21 true (2),
.last 30 (4,true),
.cycle 0 27 true (0),
.cycle 0 29 true (0),
.cycle 32 5 false (1),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.last 24 (4,true),
.cycle 27 4 false (1),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.cycle 2 35 true (1),
.cycle 1 31 true (1),
.cycle 36 9 false (2),
.cycle 0 27 true (0)
])
theorem kid11_part268_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part268) = true := by rfl

def kid11_part269 : Audit := .split 19 (2,true) (byMove [
.cycle 0 27 true (0),
.cycle 7 17 true (2),
.cycle 31 1 false (1),
.cycle 0 35 true (0),
.cycle 0 30 true (0),
.cycle 7 17 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.last 20 (4,true),
.cycle 8 19 true (2),
.cycle 31 5 false (2),
.cycle 0 38 true (0),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 1 30 true (1),
.cycle 19 2 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part269_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part269) = true := by rfl

def kid11_part270 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 1 33 true (1),
.cycle 3 20 true (1),
.cycle 4 20 true (1),
.cycle 8 15 true (2),
.cycle 6 17 true (2),
.cycle 1 27 true (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 1 25 true (1),
.cycle 1 34 true (1)
])
theorem kid11_part270_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part270) = true := by rfl

def kid11_part271 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 7 17 true (2),
.cycle 31 1 false (1),
.last 26 (2,true),
.cycle 23 1 false (-1),
.cycle 7 17 true (2),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 33 1 false (7),
.cycle 26 1 false (0),
.cycle 31 5 false (2),
.last 21 (2,true),
.last 24 (2,true),
.cycle 28 1 false (0),
.cycle 23 1 false (-1),
.last 21 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 23 3 true (5),
.cycle 0 25 true (0)
])
theorem kid11_part271_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part271) = true := by rfl

def kid11_part272 : Audit := .split 22 (2,true) (byMove [
.cycle 7 21 true (1),
.cycle 32 13 false (2),
.cycle 45 1 false (1),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17069, 17069, 4, 8192, 16384, 8, 160, 17069, 4, 524288, 1048576, 512, 128, 16777216, 256, 524288, 1048576, 2097152, 29125293, 29125293, 1048576, 16777216],[128, 32, 17069, 1, 16777216, 17069, 8192, 32, 16512, 1, 16777216, 16777216, 524288, 2048, 128, 64, 16777216, 16777216, 524288, 8388608, 29125293, 262144, 16777216, 29125293, 16777216],33370176⟩,
.cycle 25 3 false (-1),
.cycle 39 1 false (1),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 7 19 true (1),
.cycle 35 1 false (1),
.last 26 (4,true),
.cycle 69 1 false (11),
.cycle 7 25 true (1),
.cycle 28 7 false (0),
.cycle 0 31 true (0),
.cycle 40 1 false (0),
.cycle 25 3 false (-1),
.cycle 21 2 true (1),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 7 19 true (1),
.cycle 1 31 true (1),
.cycle 25 5 false (1),
.cycle 23 16 true (3)
])
theorem kid11_part272_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part272) = true := by rfl

def kid11_part273 : Audit := .cycle 7 13 true (2)
theorem kid11_part273_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part273) = true := by rfl

def kid11_part274 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 1 32 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 1 29 true (1),
.cycle 3 18 true (1),
.cycle 1 21 true (1),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.cycle 1 29 true (1),
.cycle 1 22 true (1),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 21 true (1),
.cycle 1 30 true (1)
])
theorem kid11_part274_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part274) = true := by rfl

def kid11_part275 : Audit := .cycle 0 21 true (0)
theorem kid11_part275_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part275) = true := by rfl

def kid11_part276 : Audit := .cycle 4 15 true (1)
theorem kid11_part276_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part276) = true := by rfl

def kid11_part277 : Audit := .split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 24 1 true (2),
.cycle 24 1 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 29 1 true (7),
.cycle 3 18 true (1),
.cycle 21 1 true (7),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 23 1 true (5),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 29 3 false (1),
.last 30 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 21 1 true (7),
.cycle 30 1 true (8)
])
theorem kid11_part277_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part277) = true := by rfl

def kid11_part278 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 21 10 true (5),
.cycle 21 10 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (2),
.cycle 21 10 true (4),
.cycle 21 10 true (7),
.cycle 35 10 true (8),
.cycle 7 15 true (2),
.cycle 23 10 true (5),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 23 (4,true),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 21 10 true (7),
.cycle 21 10 true (6)
])
theorem kid11_part278_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part278) = true := by rfl

def kid11_part254 : Audit := .split 18 (4,false) (byMove [(kid11_part255),(kid11_part256),(kid11_part257),(kid11_part258),(kid11_part259),(kid11_part260),(kid11_part261),(kid11_part262),(kid11_part263),(kid11_part264),(kid11_part265),(kid11_part266),(kid11_part267),(kid11_part268),(kid11_part269),(kid11_part270),(kid11_part271),(kid11_part272),(kid11_part273),(kid11_part274),(kid11_part275),(kid11_part276),(kid11_part277),(kid11_part278)])

theorem kid11_part254_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part254) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) 18 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part255),(kid11_part256),(kid11_part257),(kid11_part258),(kid11_part259),(kid11_part260),(kid11_part261),(kid11_part262),(kid11_part263),(kid11_part264),(kid11_part265),(kid11_part266),(kid11_part267),(kid11_part268),(kid11_part269),(kid11_part270),(kid11_part271),(kid11_part272),(kid11_part273),(kid11_part274),(kid11_part275),(kid11_part276),(kid11_part277),(kid11_part278)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part255_checked

  · exact kid11_part261_checked

  · exact kid11_part267_checked

  · exact kid11_part273_checked

  · exact kid11_part256_checked

  · exact kid11_part262_checked

  · exact kid11_part268_checked

  · exact kid11_part274_checked

  · exact kid11_part257_checked

  · exact kid11_part263_checked

  · exact kid11_part269_checked

  · exact kid11_part275_checked

  · exact kid11_part258_checked

  · exact kid11_part264_checked

  · exact kid11_part270_checked

  · exact kid11_part276_checked

  · exact kid11_part259_checked

  · exact kid11_part265_checked

  · exact kid11_part271_checked

  · exact kid11_part277_checked

  · exact kid11_part260_checked

  · exact kid11_part266_checked

  · exact kid11_part272_checked

  · exact kid11_part278_checked

def kid11_part279 : Audit := .cycle 0 21 true (0)
theorem kid11_part279_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part279) = true := by rfl

def kid11_part280 : Audit := .cycle 1 18 true (1)
theorem kid11_part280_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part280) = true := by rfl

def kid11_part281 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 4, 64],[2, 32, 64, 1, 64, 2, 64],80⟩
theorem kid11_part281_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part281) = true := by rfl

def kid11_part282 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 18 true (2),
.cycle 3 16 true (1),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 9 20 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 9 18 true (2),
.cycle 19 1 true (5),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 7 14 true (2),
.last 22 (4,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (4,true),
.cycle 33 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (5),
.cycle 9 20 true (2)
]),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 10 9 true (2),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 9 18 true (2),
.last 23 (4,true),
.last 32 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (4,true),
.last 30 (4,true),
.cycle 19 1 true (7),
.last 34 (4,true),
.cycle 7 14 true (2),
.cycle 18 3 true (6),
.cycle 0 22 true (0),
.cycle 11 9 true (2),
.last 23 (4,true),
.cycle 18 3 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 9 20 true (2)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 32, 1, 64, 4, 64],80⟩,
.cycle 7 13 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 21 true (0),
.cycle 9 16 true (2),
.split 19 (4,false) (byMove [
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 9 18 true (2),
.last 25 (4,true),
.last 21 (4,true),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2, 4, 128, 256, 8, 128, 2, 4, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 18 2 true (5),
.cycle 0 21 true (0),
.last 20 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 9 14 true (2),
.last 22 (4,true),
.cycle 1 22 true (1),
.cycle 9 16 true (2),
.last 21 (4,true),
.cycle 33 3 false (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 21 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 9 20 true (2)
]),
.cycle 18 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.last 34 (4,true),
.cycle 18 2 true (6),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 32 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 19 true (2),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.last 34 (4,true),
.last 21 (4,true),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 17 3 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 9 20 true (2)
]),
.cycle 9 19 true (2)
])
theorem kid11_part282_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part282) = true := by rfl

def kid11_part283 : Audit := .cycle 0 19 true (0)
theorem kid11_part283_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part283) = true := by rfl

def kid11_part285 : Audit := .cycle 0 19 true (0)
theorem kid11_part285_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part285) = true := by rfl

def kid11_part286 : Audit := .cycle 1 18 true (1)
theorem kid11_part286_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part286) = true := by rfl

def kid11_part287 : Audit := .split 27 (4,false) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 19 9 true (3),
.cycle 3 25 true (1),
.cycle 54 1 false (2),
.cycle 8 20 true (2),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 11 29 true (2),
.cycle 10 18 true (2),
.cycle 27 1 true (7),
.cycle 11 40 true (2),
.cycle 7 22 true (2),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 21 7 true (3),
.cycle 81 1 false (5),
.last 29 (2,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 27 1 true (7),
.cycle 19 10 true (3)
])
theorem kid11_part287_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part287) = true := by rfl

def kid11_part288 : Audit := .cycle 3 16 true (1)
theorem kid11_part288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part288) = true := by rfl

def kid11_part289 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 25 1 false (-1),
.cycle 8 22 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 10 18 true (2),
.cycle 19 1 true (5),
.last 34 (2,true),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 25 1 false (-1),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (5),
.cycle 19 10 true (5)
])
theorem kid11_part289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part289) = true := by rfl

def kid11_part290 : Audit := .cycle 8 11 true (2)
theorem kid11_part290_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part290) = true := by rfl

def kid11_part291 : Audit := .cycle 0 19 true (0)
theorem kid11_part291_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part291) = true := by rfl

def kid11_part292 : Audit := .cycle 1 18 true (1)
theorem kid11_part292_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part292) = true := by rfl

def kid11_part293 : Audit := .split 30 (2,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.cycle 9 22 true (2),
.last 38 (4,false),
.last 31 (4,false),
.cycle 19 13 true (3),
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 16777216, 4, 128, 256, 32768, 128, 16777216, 16384, 128, 256, 2097152, 131072, 16777216, 1048576, 128, 256, 8, 4194304, 16777216, 4, 16777216],[128, 32, 4, 1, 4, 16, 128, 131072, 16384, 4096, 16384, 65536, 128, 8388608, 1048576, 262144, 1048576, 4194304, 128, 32, 4, 1, 4, 16, 16777216],23153680⟩,
.cycle 20 11 true (3),
.last 31 (4,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 33554816, 1073741824, 16384, 33554432, 67108864, 2097152, 131072, 1073741824, 1048576, 128, 256, 512, 4194304, 1073741824, 256, 128, 256, 32768, 128, 1073741824, 16384, 1073741824],[128, 32, 32, 1, 4, 16, 128, 131072, 131072, 4096, 16384, 65536, 33554432, 8388608, 8388608, 262144, 1048576, 4194304, 128, 2048, 2048, 64, 256, 1024, 128, 131072, 131072, 4096, 16384, 65536, 1073741824],1885424656⟩,
.cycle 7 25 true (2),
.last 35 (4,false),
.cycle 0 33 true (0),
.cycle 11 20 true (2),
.last 31 (4,false),
.cycle 30 2 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.cycle 2 29 true (1),
.cycle 1 33 true (1),
.last 31 (4,false),
.last 40 (4,false)
])
theorem kid11_part293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part293) = true := by rfl

def kid11_part294 : Audit := .cycle 10 9 true (2)
theorem kid11_part294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part294) = true := by rfl

def kid11_part295 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 3 25 true (1),
.cycle 29 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 19 1 true (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 11 9 true (2),
.cycle 45 1 false (9),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 19 10 true (7)
])
theorem kid11_part295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part295) = true := by rfl

def kid11_part296 : Audit := .far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 128, 1073741824, 16384, 128, 256, 2097152, 131072, 1073741824, 1048576, 128, 256, 134217728, 4194304, 1073741824, 67108864, 128, 256, 2097152, 536870912, 1073741824, 1048576, 1073741824],[128, 32, 1073741824, 1, 32, 16, 128, 131072, 1073741824, 4096, 131072, 65536, 128, 8388608, 1073741824, 262144, 8388608, 4194304, 128, 536870912, 1073741824, 16777216, 536870912, 268435456, 128, 8388608, 1073741824, 262144, 8388608, 4194304, 1073741824],1424051216⟩
theorem kid11_part296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part296) = true := by rfl

def kid11_part297 : Audit := .cycle 7 13 true (2)
theorem kid11_part297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part297) = true := by rfl

def kid11_part298 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 1 38 true (1),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.last 27 (4,false),
.last 22 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 29 (4,false),
.cycle 3 18 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.last 23 (4,false),
.cycle 1 24 true (1),
.cycle 1 22 true (1),
.cycle 42 3 false (2),
.cycle 17 4 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 30 (4,false)
])
theorem kid11_part298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part298) = true := by rfl

def kid11_part299 : Audit := .cycle 0 21 true (0)
theorem kid11_part299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part299) = true := by rfl

def kid11_part300 : Audit := .split 25 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 19 9 true (3),
.cycle 3 23 true (1),
.cycle 47 1 false (1),
.cycle 8 18 true (2),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 12 25 true (2),
.cycle 10 16 true (2),
.cycle 25 1 true (7),
.cycle 12 34 true (2),
.cycle 7 20 true (2),
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 19 7 true (3),
.cycle 68 1 false (4),
.last 27 (2,true),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 25 1 true (7),
.cycle 19 10 true (3)
])
theorem kid11_part300_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part300) = true := by rfl

def kid11_part301 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 9 true (3),
.last 24 (2,true),
.cycle 25 1 false (-1),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 2, 4, 64],[2, 32, 64, 1, 48, 16, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 7 18 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 20 7 true (3),
.cycle 25 1 false (-1),
.last 21 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 31 3 false (1),
.cycle 20 10 true (6)
])
theorem kid11_part301_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part301) = true := by rfl

def kid11_part302 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 29 (4,false),
.cycle 3 18 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 16777216, 4, 128, 256, 32768, 128, 16777216, 16384, 128, 256, 2097152, 131072, 16777216, 1048576, 128, 256, 8, 4194304, 16777216, 4, 16777216],[128, 32, 4, 1, 4, 16, 128, 131072, 16384, 4096, 1048580, 65536, 128, 8388608, 1048576, 262144, 1048576, 4194304, 128, 32, 4, 1, 4, 16, 16777216],23153680⟩,
.cycle 10 11 true (2),
.last 21 (4,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 128, 1073741824, 16384, 128, 256, 2097152, 131072, 1073741824, 1048576, 128, 256, 134217728, 4194304, 1073741824, 67108864, 128, 256, 2097152, 536870912, 1073741824, 1048576, 1073741824],[128, 32, 32, 1, 32, 16, 128, 131072, 131072, 4096, 545259552, 65536, 128, 8388608, 8388608, 262144, 8388608, 4194304, 128, 536870912, 536870912, 16777216, 536870912, 268435456, 128, 8388608, 8388608, 262144, 8388608, 4194304, 1073741824],1424051216⟩,
.cycle 7 15 true (2),
.last 25 (4,false),
.cycle 0 23 true (0),
.last 27 (4,false),
.last 21 (4,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 30 (4,false)
])
theorem kid11_part302_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part302) = true := by rfl

def kid11_part303 : Audit := .cycle 0 19 true (0)
theorem kid11_part303_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part303) = true := by rfl

def kid11_part304 : Audit := .cycle 1 18 true (1)
theorem kid11_part304_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part304) = true := by rfl

def kid11_part305 : Audit := .cycle 2 17 true (1)
theorem kid11_part305_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part305) = true := by rfl

def kid11_part306 : Audit := .cycle 1 21 true (1)
theorem kid11_part306_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part306) = true := by rfl

def kid11_part307 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 30 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (6),
.cycle 8 40 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 18 22 true (6),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.last 24 (2,true),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 18 3 true (6),
.cycle 17 3 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 19 10 true (7)
])
theorem kid11_part307_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part307) = true := by rfl

def kid11_part308 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 20 9 true (6),
.cycle 3 26 true (1),
.cycle 18 13 true (6),
.cycle 8 21 true (2),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 9 33 true (2),
.cycle 10 19 true (2),
.cycle 28 1 true (10),
.cycle 17 25 true (5),
.cycle 7 23 true (2),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 22 7 true (6),
.cycle 17 21 true (5),
.last 30 (2,true),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 28 1 true (10),
.cycle 19 10 true (6)
])
theorem kid11_part308_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part308) = true := by rfl

def kid11_part284 : Audit := .split 18 (4,true) (byMove [(kid11_part285),(kid11_part286),(kid11_part287),(kid11_part288),(kid11_part289),(kid11_part290),(kid11_part291),(kid11_part292),(kid11_part293),(kid11_part294),(kid11_part295),(kid11_part296),(kid11_part297),(kid11_part298),(kid11_part299),(kid11_part300),(kid11_part301),(kid11_part302),(kid11_part303),(kid11_part304),(kid11_part305),(kid11_part306),(kid11_part307),(kid11_part308)])

theorem kid11_part284_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part284) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part285),(kid11_part286),(kid11_part287),(kid11_part288),(kid11_part289),(kid11_part290),(kid11_part291),(kid11_part292),(kid11_part293),(kid11_part294),(kid11_part295),(kid11_part296),(kid11_part297),(kid11_part298),(kid11_part299),(kid11_part300),(kid11_part301),(kid11_part302),(kid11_part303),(kid11_part304),(kid11_part305),(kid11_part306),(kid11_part307),(kid11_part308)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part285_checked

  · exact kid11_part291_checked

  · exact kid11_part297_checked

  · exact kid11_part303_checked

  · exact kid11_part286_checked

  · exact kid11_part292_checked

  · exact kid11_part298_checked

  · exact kid11_part304_checked

  · exact kid11_part287_checked

  · exact kid11_part293_checked

  · exact kid11_part299_checked

  · exact kid11_part305_checked

  · exact kid11_part288_checked

  · exact kid11_part294_checked

  · exact kid11_part300_checked

  · exact kid11_part306_checked

  · exact kid11_part289_checked

  · exact kid11_part295_checked

  · exact kid11_part301_checked

  · exact kid11_part307_checked

  · exact kid11_part290_checked

  · exact kid11_part296_checked

  · exact kid11_part302_checked

  · exact kid11_part308_checked

def kid11_part309 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 4, 64],[2, 32, 64, 1, 64, 32, 64],80⟩
theorem kid11_part309_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part309) = true := by rfl

def kid11_part310 : Audit := .cycle 7 15 true (2)
theorem kid11_part310_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part310) = true := by rfl

def kid11_part311 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.cycle 35 1 false (1),
.cycle 7 15 true (2),
.split 20 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 22 (4,false),
.cycle 0 27 true (0),
.last 22 (4,false),
.cycle 43 1 false (1),
.cycle 7 15 true (2),
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.last 21 (4,false),
.last 23 (4,false),
.last 25 (4,false),
.cycle 34 3 false (1),
.last 22 (4,false),
.cycle 1 27 true (1),
.last 22 (4,false),
.last 27 (4,false),
.cycle 7 15 true (2),
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 21 (4,false),
.last 23 (4,false)
]),
.cycle 33 3 false (1),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 32 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (2),
.last 30 (4,false),
.last 21 (4,false),
.last 38 (4,false),
.cycle 7 15 true (2),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 21 (4,false),
.last 23 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 32 (4,false)
]),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.cycle 5 27 true (1),
.cycle 5 15 true (1),
.split 20 (4,true) (byMove [
.cycle 18 4 true (3),
.last 24 (4,false),
.last 22 (4,false),
.cycle 7 23 true (2),
.last 22 (4,false),
.cycle 7 35 true (1),
.cycle 6 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 32, 4096, 1, 2, 32, 128, 32, 32, 1, 2, 32, 4096],5136⟩,
.last 22 (4,false),
.cycle 1 22 true (1),
.last 23 (4,false),
.cycle 17 4 true (4),
.cycle 15 6 true (3),
.cycle 34 3 false (1),
.last 22 (4,false),
.cycle 5 23 true (1),
.last 22 (4,false),
.last 27 (4,false),
.cycle 6 15 true (2),
.cycle 7 19 true (2),
.cycle 19 2 true (4),
.cycle 1 22 true (1),
.last 23 (4,false),
.cycle 16 6 true (4)
]),
.cycle 33 3 false (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.last 26 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (4,false),
.cycle 3 18 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.last 25 (4,false),
.cycle 19 2 true (5),
.cycle 1 22 true (1),
.last 24 (4,false),
.cycle 16 6 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 32 (4,false)
]),
.cycle 21 11 true (5)
])
theorem kid11_part311_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part311) = true := by rfl

def kid11_part312 : Audit := .cycle 1 20 true (1)
theorem kid11_part312_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part312) = true := by rfl

def kid11_part313 : Audit := .cycle 4 19 true (1)
theorem kid11_part313_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part313) = true := by rfl

def kid11_part315 : Audit := .split 21 (2,true) (byMove [
.cycle 1 25 true (1),
.cycle 1 24 true (1),
.cycle 39 1 false (1),
.cycle 7 17 true (2),
.last 22 (4,true),
.last 23 (4,true),
.cycle 1 22 true (1),
.cycle 1 43 true (1),
.cycle 9 14 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 8 19 true (2),
.cycle 6 23 true (2),
.cycle 16 6 true (3),
.cycle 5 31 true (1),
.cycle 5 17 true (1),
.last 22 (4,true),
.last 23 (4,true),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 2 21 true (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part315_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part315) = true := by rfl

def kid11_part316 : Audit := .split 21 (2,true) (byMove [
.cycle 1 25 true (1),
.cycle 0 25 true (0),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 1 35 true (1),
.cycle 0 25 true (0),
.cycle 1 22 true (1),
.cycle 14 33 true (0),
.cycle 46 1 false (10),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 0 27 true (0),
.cycle 7 23 true (2),
.cycle 1 30 true (1),
.cycle 1 24 true (1),
.cycle 34 1 false (2),
.cycle 1 26 true (1),
.cycle 20 2 true (4),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 2 21 true (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part316_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part316) = true := by rfl

def kid11_part317 : Audit := .split 19 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 1 28 true (0),
.cycle 1 30 true (0),
.cycle 34 1 false (2),
.cycle 7 19 true (2),
.cycle 1 51 true (1),
.cycle 1 22 true (1),
.cycle 30 1 false (2),
.cycle 34 1 false (2),
.cycle 41 1 false (3),
.cycle 7 27 true (2),
.cycle 40 1 false (0),
.cycle 7 23 true (2),
.cycle 28 1 false (0),
.cycle 32 1 false (0),
.cycle 19 2 true (2),
.cycle 7 19 true (2),
.cycle 7 15 true (2),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (3),
.last 23 (4,true)
])
theorem kid11_part317_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part317) = true := by rfl

def kid11_part318 : Audit := .cycle 7 19 true (2)
theorem kid11_part318_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part318) = true := by rfl

def kid11_part319 : Audit := .split 19 (4,true) (byMove [
.cycle 1 24 true (1),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 1 28 true (0),
.cycle 23 1 false (-1),
.cycle 34 1 false (2),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 30 1 false (2),
.cycle 25 1 false (1),
.last 21 (2,true),
.last 23 (2,true),
.last 21 (2,true),
.cycle 7 23 true (2),
.cycle 28 1 false (0),
.cycle 23 1 false (-1),
.last 21 (2,true),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (3),
.last 21 (2,true)
])
theorem kid11_part319_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part319) = true := by rfl

def kid11_part320 : Audit := .cycle 7 27 true (1)
theorem kid11_part320_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part320) = true := by rfl

def kid11_part321 : Audit := .cycle 6 13 true (2)
theorem kid11_part321_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part321) = true := by rfl

def kid11_part322 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 2, 4, 128, 256, 8, 128, 2, 4, 4096],[128, 32, 4096, 1, 4096, 32, 128, 32, 4096, 1, 4096, 4096, 4096],4096⟩
theorem kid11_part322_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part322) = true := by rfl

def kid11_part323 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 26 true (0),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 2, 1, 4096, 2, 128, 32, 2, 1, 4096, 4096, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.last 20 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 32, 1, 4096, 32, 128, 32, 32, 1, 4096, 4096, 4096],4096⟩,
.cycle 7 19 true (2),
.cycle 16 6 true (4),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (4),
.cycle 19 2 true (4),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part323_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part323) = true := by rfl

def kid11_part324 : Audit := .cycle 1 20 true (1)
theorem kid11_part324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part324) = true := by rfl

def kid11_part325 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.last 24 (2,true),
.cycle 23 1 true (5),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 16, 4, 64],[2, 32, 64, 1, 2, 34, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 16, 4, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (4),
.last 21 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (7),
.cycle 19 2 true (5)
])
theorem kid11_part325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part325) = true := by rfl

def kid11_part326 : Audit := .cycle 17 2 true (4)
theorem kid11_part326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part326) = true := by rfl

def kid11_part327 : Audit := .cycle 15 4 true (3)
theorem kid11_part327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part327) = true := by rfl

def kid11_part328 : Audit := .split 23 (2,true) (byMove [
.cycle 1 33 true (1),
.cycle 1 30 true (1),
.cycle 49 1 false (1),
.cycle 16 10 true (2),
.last 24 (4,true),
.cycle 27 4 false (1),
.cycle 6 27 true (2),
.cycle 19 33 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 5 19 true (1),
.last 24 (4,true),
.cycle 34 7 false (2),
.cycle 37 9 false (2),
.cycle 32 5 false (1),
.cycle 14 12 true (1),
.cycle 14 10 true (2),
.last 24 (4,true),
.cycle 27 4 false (1),
.cycle 43 15 false (4),
.cycle 38 11 false (3),
.cycle 2 25 true (1),
.cycle 5 19 true (1),
.last 24 (4,true),
.last 25 (4,true)
])
theorem kid11_part328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part328) = true := by rfl

def kid11_part329 : Audit := .split 19 (2,true) (byMove [
.cycle 1 29 true (1),
.cycle 5 17 true (1),
.cycle 31 1 false (1),
.cycle 58 1 false (4),
.cycle 16 8 true (1),
.cycle 5 17 true (1),
.cycle 6 19 true (2),
.cycle 5 19 true (1),
.cycle 46 1 false (10),
.cycle 5 15 true (1),
.last 20 (4,true),
.cycle 5 27 true (1),
.cycle 31 5 false (2),
.cycle 14 12 true (1),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 14 8 true (1),
.cycle 19 2 true (2),
.cycle 6 19 true (2),
.cycle 16 4 true (3),
.cycle 2 21 true (1),
.cycle 5 15 true (1),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part329) = true := by rfl

def kid11_part330 : Audit := .cycle 5 19 true (1)
theorem kid11_part330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part330) = true := by rfl

def kid11_part331 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 5 17 true (1),
.cycle 31 1 false (1),
.last 26 (2,true),
.cycle 23 1 false (-1),
.cycle 5 17 true (1),
.cycle 6 19 true (2),
.cycle 29 1 false (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 38 1 false (8),
.cycle 26 1 false (0),
.cycle 31 5 false (2),
.last 21 (2,true),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 23 1 false (-1),
.last 21 (2,true),
.cycle 6 19 true (2),
.cycle 16 4 true (3),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 21 3 true (5),
.cycle 19 2 true (3)
])
theorem kid11_part331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part331) = true := by rfl

def kid11_part332 : Audit := .split 22 (2,true) (byMove [
.cycle 1 35 true (1),
.cycle 5 31 true (1),
.cycle 36 1 false (0),
.cycle 39 1 false (-1),
.cycle 25 3 false (-1),
.cycle 5 31 true (1),
.cycle 15 8 true (1),
.cycle 102 1 false (12),
.cycle 54 1 false (10),
.cycle 5 27 true (1),
.last 23 (4,true),
.cycle 19 4 true (1),
.last 28 (4,true),
.cycle 28 7 false (0),
.cycle 14 10 true (1),
.cycle 33 1 false (-1),
.cycle 25 3 false (-1),
.cycle 21 2 true (1),
.last 28 (4,true),
.cycle 26 7 false (2),
.cycle 2 25 true (1),
.cycle 28 11 false (4),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part332) = true := by rfl

def kid11_part333 : Audit := .cycle 6 13 true (2)
theorem kid11_part333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part333) = true := by rfl

def kid11_part334 : Audit := .cycle 7 15 true (2)
theorem kid11_part334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part334) = true := by rfl

def kid11_part335 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.cycle 35 1 false (1),
.cycle 7 15 true (2),
.last 20 (4,true),
.last 21 (4,true),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.cycle 5 27 true (1),
.cycle 5 15 true (1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part335) = true := by rfl

def kid11_part336 : Audit := .cycle 1 20 true (1)
theorem kid11_part336_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part336) = true := by rfl

def kid11_part337 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 31 1 true (1),
.cycle 7 19 true (2),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (7),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 27 3 false (1),
.last 23 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (7),
.cycle 19 2 true (5)
])
theorem kid11_part337_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part337) = true := by rfl

def kid11_part338 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.last 23 (2,true),
.last 21 (2,true),
.cycle 7 23 true (2),
.cycle 1 26 true (1),
.cycle 7 35 true (1),
.cycle 6 15 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 21 14 true (5),
.cycle 17 4 true (4),
.cycle 15 6 true (3),
.last 27 (2,true),
.last 21 (2,true),
.cycle 5 23 true (1),
.cycle 28 3 false (0),
.last 26 (2,true),
.cycle 6 15 true (2),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 21 14 true (5),
.cycle 19 2 true (4)
])
theorem kid11_part338_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part338) = true := by rfl

def kid11_part314 : Audit := .split 18 (4,false) (byMove [(kid11_part315),(kid11_part316),(kid11_part317),(kid11_part318),(kid11_part319),(kid11_part320),(kid11_part321),(kid11_part322),(kid11_part323),(kid11_part324),(kid11_part325),(kid11_part326),(kid11_part327),(kid11_part328),(kid11_part329),(kid11_part330),(kid11_part331),(kid11_part332),(kid11_part333),(kid11_part334),(kid11_part335),(kid11_part336),(kid11_part337),(kid11_part338)])

theorem kid11_part314_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part314) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) 18 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part315),(kid11_part316),(kid11_part317),(kid11_part318),(kid11_part319),(kid11_part320),(kid11_part321),(kid11_part322),(kid11_part323),(kid11_part324),(kid11_part325),(kid11_part326),(kid11_part327),(kid11_part328),(kid11_part329),(kid11_part330),(kid11_part331),(kid11_part332),(kid11_part333),(kid11_part334),(kid11_part335),(kid11_part336),(kid11_part337),(kid11_part338)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part315_checked

  · exact kid11_part321_checked

  · exact kid11_part327_checked

  · exact kid11_part333_checked

  · exact kid11_part316_checked

  · exact kid11_part322_checked

  · exact kid11_part328_checked

  · exact kid11_part334_checked

  · exact kid11_part317_checked

  · exact kid11_part323_checked

  · exact kid11_part329_checked

  · exact kid11_part335_checked

  · exact kid11_part318_checked

  · exact kid11_part324_checked

  · exact kid11_part330_checked

  · exact kid11_part336_checked

  · exact kid11_part319_checked

  · exact kid11_part325_checked

  · exact kid11_part331_checked

  · exact kid11_part337_checked

  · exact kid11_part320_checked

  · exact kid11_part326_checked

  · exact kid11_part332_checked

  · exact kid11_part338_checked

def kid11_part339 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 26 true (0),
.split 20 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 45 1 false (1),
.last 25 (4,true),
.last 21 (4,true),
.cycle 43 1 false (1),
.cycle 7 15 true (2),
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.last 22 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 7 20 true (2),
.last 28 (4,true),
.cycle 0 32 true (0),
.last 25 (4,true),
.last 21 (4,true),
.cycle 29 3 false (0),
.cycle 7 15 true (2),
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 22 (4,true),
.cycle 21 12 true (5)
]),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 4, 64],[2, 32, 2, 1, 64, 34, 64],80⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (4,false),
.cycle 3 18 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 35 (4,false),
.cycle 10 11 true (2),
.last 21 (4,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 128, 1073741824, 16384, 128, 256, 2097152, 131072, 1073741824, 1048576, 128, 256, 134217728, 4194304, 1073741824, 67108864, 128, 256, 2097152, 536870912, 1073741824, 1048576, 1073741824],[128, 32, 16, 1, 32, 16, 128, 131072, 65536, 4096, 131072, 817889328, 128, 8388608, 4194304, 262144, 8388608, 4194304, 128, 536870912, 268435456, 16777216, 536870912, 268435456, 128, 8388608, 4194304, 262144, 8388608, 4194304, 1073741824],1424051216⟩,
.cycle 7 15 true (2),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 29 (4,false),
.last 21 (4,false),
.last 23 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 32 (4,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 4, 64],[2, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 7 19 true (2),
.cycle 16 6 true (4),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.split 20 (4,false) (byMove [
.last 24 (4,true),
.cycle 1 28 true (1),
.cycle 36 1 false (0),
.cycle 7 23 true (2),
.last 21 (4,true),
.cycle 7 35 true (1),
.cycle 6 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 2, 4, 128, 256, 8, 128, 2, 4, 4096],[128, 32, 32, 1, 4096, 32, 128, 32, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 19 2 true (4),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 17 4 true (4),
.cycle 15 6 true (3),
.last 28 (4,true),
.cycle 14 10 true (1),
.cycle 5 23 true (1),
.last 21 (4,true),
.cycle 29 3 false (0),
.cycle 6 15 true (2),
.cycle 7 19 true (2),
.last 22 (4,true),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 33 5 false (1)
]),
.cycle 18 2 true (4),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.last 39 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 24 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (4,false),
.cycle 3 18 true (1),
.last 21 (4,false),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.last 25 (4,false),
.cycle 19 2 true (5),
.cycle 1 22 true (1),
.last 22 (4,false),
.cycle 17 4 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.last 32 (4,false)
]),
.cycle 17 4 true (4)
])
theorem kid11_part339_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part339) = true := by rfl

def kid11_part340 : Audit := .cycle 1 18 true (1)
theorem kid11_part340_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part340) = true := by rfl

def kid11_part341 : Audit := .cycle 7 11 true (2)
theorem kid11_part341_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part341) = true := by rfl

def kid11_part342 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 34 true (1),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 2 27 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 2 25 true (1),
.last 20 (4,false),
.last 35 (4,false),
.cycle 7 14 true (2),
.cycle 2 23 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 20 (4,false),
.last 22 (4,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 2 27 true (1)
]),
.cycle 2 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 25 true (1),
.cycle 3 16 true (1),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 2 27 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 2 25 true (1),
.cycle 19 1 true (7),
.last 32 (4,true),
.cycle 7 14 true (2),
.cycle 18 3 true (6),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (4,true),
.cycle 18 3 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 2 27 true (1)
]),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 2 19 true (1),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.split 19 (4,true) (byMove [
.cycle 21 4 true (4),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 7 21 true (2),
.last 20 (4,false),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 288, 4096, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 32, 4096, 1, 2, 256, 128, 32, 32, 1, 2, 256, 4096],5136⟩,
.last 21 (4,false),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 2 19 true (1),
.cycle 2 21 true (1),
.cycle 38 3 false (2),
.cycle 1 22 true (1),
.cycle 2 23 true (1),
.last 20 (4,false),
.last 22 (4,false),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 18 2 true (5),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 2 19 true (1)
]),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 18 2 true (6),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 2 19 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 26 true (1),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.cycle 2 20 true (1),
.last 21 (4,true),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 17 3 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 2 27 true (1)
]),
.cycle 2 26 true (1)
])
theorem kid11_part342_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part342) = true := by rfl

def kid11_part343 : Audit := .cycle 0 19 true (0)
theorem kid11_part343_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part343) = true := by rfl

def kid11_part345 : Audit := .cycle 1 19 true (1)
theorem kid11_part345_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part345) = true := by rfl

def kid11_part346 : Audit := .split 34 (2,true) (byMove [
.cycle 0 35 true (0),
.cycle 1 34 true (1),
.cycle 9 26 true (2),
.last 42 (4,false),
.last 35 (4,false),
.cycle 20 15 true (3),
.cycle 0 35 true (0),
.cycle 1 34 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048580, 16777216, 4, 128, 256, 32768, 128, 16777216, 16384, 128, 256, 2097152, 131072, 16777216, 1048576, 128, 256, 8, 1024, 16777216, 4, 16777216],[128, 32, 4, 1, 32768, 1024, 128, 131072, 16384, 4096, 1048580, 1024, 128, 8388608, 1048576, 262144, 32768, 1024, 128, 32, 4, 1, 32768, 1024, 16777216],23153680⟩,
.cycle 22 13 true (3),
.last 35 (4,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 33554816, 1073741824, 16384, 33554432, 67108864, 2097152, 131072, 1073741824, 1048576, 128, 256, 512, 268435456, 1073741824, 256, 128, 256, 32768, 128, 1073741824, 16384, 1073741824],[128, 32, 32, 1, 32768, 1024, 128, 131072, 131072, 4096, 1097732, 1024, 33554432, 8388608, 8388608, 262144, 32768, 268435456, 128, 2048, 2048, 64, 32768, 1024, 128, 131072, 131072, 4096, 256, 1024, 1073741824],1885424656⟩,
.cycle 7 29 true (2),
.last 39 (4,false),
.cycle 0 37 true (0),
.cycle 11 24 true (2),
.last 35 (4,false),
.cycle 33 2 true (7),
.cycle 0 35 true (0),
.cycle 1 34 true (1),
.cycle 2 33 true (1),
.cycle 1 37 true (1),
.last 35 (4,false),
.last 44 (4,false)
])
theorem kid11_part346_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part346) = true := by rfl

def kid11_part347 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.last 29 (4,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.last 27 (4,false),
.last 20 (4,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 33554816, 1073741824, 16384, 33554432, 67108864, 2097152, 131072, 1073741824, 1048576, 128, 256, 512, 268435456, 1073741824, 256, 128, 256, 32768, 128, 1073741824, 16384, 1073741824],[128, 32, 32, 1, 0, 1024, 128, 131072, 131072, 4096, 34619780, 1024, 33554432, 8388608, 8388608, 262144, 131072, 268435456, 128, 2048, 2048, 64, 268435456, 1024, 128, 131072, 131072, 4096, 256, 1024, 1073741824],1885424656⟩,
.cycle 7 14 true (2),
.last 24 (4,false),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 20 (4,false),
.cycle 19 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.last 29 (4,false)
])
theorem kid11_part347_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part347) = true := by rfl

def kid11_part348 : Audit := .cycle 0 20 true (0)
theorem kid11_part348_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part348) = true := by rfl

def kid11_part349 : Audit := .split 20 (4,false) (byMove [
.cycle 1 21 true (1),
.cycle 40 1 false (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 25 1 false (-1),
.cycle 20 2 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 20 9 true (3),
.cycle 3 18 true (1),
.cycle 20 1 true (4),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 20 3 true (3),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 25 1 false (-1),
.last 26 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (4),
.cycle 20 10 true (4)
])
theorem kid11_part349_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part349) = true := by rfl

def kid11_part350 : Audit := .split 20 (4,false) (byMove [
.cycle 1 21 true (1),
.last 38 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 19 11 true (3),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 19 9 true (5),
.cycle 3 18 true (1),
.cycle 20 1 true (6),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 19 3 true (5),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 0 25 true (0),
.cycle 17 4 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (6),
.cycle 19 10 true (5)
])
theorem kid11_part350_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part350) = true := by rfl

def kid11_part351 : Audit := .cycle 0 19 true (0)
theorem kid11_part351_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part351) = true := by rfl

def kid11_part352 : Audit := .cycle 1 18 true (1)
theorem kid11_part352_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part352) = true := by rfl

def kid11_part353 : Audit := .split 27 (4,false) (byMove [
.cycle 1 28 true (1),
.last 41 (2,true),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 9 20 true (2),
.cycle 26 2 true (8),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 19 9 true (5),
.cycle 3 25 true (1),
.cycle 27 1 true (9),
.cycle 8 20 true (2),
.cycle 6 22 true (2),
.cycle 25 3 true (7),
.last 28 (2,true),
.cycle 1 29 true (1),
.last 29 (2,true),
.cycle 17 11 true (5),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 27 1 true (9),
.cycle 19 10 true (5)
])
theorem kid11_part353_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part353) = true := by rfl

def kid11_part354 : Audit := .cycle 3 16 true (1)
theorem kid11_part354_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part354) = true := by rfl

def kid11_part355 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.cycle 28 2 true (8),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 3 25 true (1),
.cycle 19 1 true (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 54 1 false (10),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 19 10 true (7)
])
theorem kid11_part355_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part355) = true := by rfl

def kid11_part356 : Audit := .cycle 8 11 true (2)
theorem kid11_part356_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part356) = true := by rfl

def kid11_part357 : Audit := .cycle 6 13 true (2)
theorem kid11_part357_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part357) = true := by rfl

def kid11_part358 : Audit := .split 21 (4,false) (byMove [
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1056, 8, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 4096, 1, 4096, 1024, 128, 32, 4096, 1, 1024, 1024, 4096],4096⟩,
.last 22 (2,true),
.cycle 0 23 true (0),
.last 24 (2,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 19 9 true (5),
.cycle 3 19 true (1),
.cycle 21 1 true (7),
.cycle 8 14 true (2),
.cycle 6 16 true (2),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 1 23 true (1),
.last 24 (2,true),
.cycle 17 5 true (5),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 21 1 true (7),
.cycle 19 10 true (5)
])
theorem kid11_part358_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part358) = true := by rfl

def kid11_part359 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.last 27 (4,false),
.cycle 0 26 true (0),
.last 20 (4,false),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 1, 3, 3],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 524416, 1073741824, 16384, 524288, 1048576, 2097152, 537001984, 1073741824, 1048576, 128, 256, 134217728, 4718720, 1073741824, 67108864, 524288, 1048576, 2097152, 553779200, 1073741824, 1048576, 1073741824],[128, 32, 2, 1, 1, 1024, 128, 131072, 8192, 4096, 8388640, 1024, 524288, 8388608, 524288, 262144, 262144, 4194304, 128, 536870912, 33554432, 16777216, 553648128, 1024, 524288, 8388608, 524288, 262144, 262144, 4194304, 1073741824],1424051216⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048580, 16777216, 4, 128, 256, 32768, 128, 16777216, 16384, 128, 256, 2097152, 131072, 16777216, 1048576, 128, 256, 8, 1024, 16777216, 4, 16777216],[128, 32, 4, 1, 1, 1024, 128, 131072, 16384, 4096, 1048580, 1024, 128, 8388608, 1048576, 262144, 262144, 1024, 128, 32, 4, 1, 1, 1024, 16777216],23153680⟩,
.cycle 0 21 true (0),
.cycle 0 23 true (0),
.last 21 (4,false),
.last 23 (4,false),
.cycle 16 6 true (4),
.cycle 1 22 true (1),
.last 25 (4,false),
.last 20 (4,false),
.cycle 19 2 true (4),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 18 2 true (5),
.last 21 (4,false)
])
theorem kid11_part359_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part359) = true := by rfl

def kid11_part360 : Audit := .cycle 1 20 true (1)
theorem kid11_part360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part360) = true := by rfl

def kid11_part361 : Audit := .split 20 (4,false) (byMove [
.last 23 (2,true),
.last 23 (2,true),
.last 21 (2,true),
.cycle 0 27 true (0),
.cycle 25 1 false (-1),
.cycle 20 2 true (3),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 19 2 true (4),
.cycle 17 4 true (4),
.cycle 15 6 true (3),
.last 27 (2,true),
.last 21 (2,true),
.cycle 1 27 true (1),
.cycle 25 1 false (-1),
.last 26 (2,true),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 29 3 false (1),
.cycle 34 5 false (2)
])
theorem kid11_part361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part361) = true := by rfl

def kid11_part362 : Audit := .cycle 17 2 true (5)
theorem kid11_part362_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part362) = true := by rfl

def kid11_part363 : Audit := .cycle 0 19 true (0)
theorem kid11_part363_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part363) = true := by rfl

def kid11_part364 : Audit := .cycle 1 18 true (1)
theorem kid11_part364_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part364) = true := by rfl

def kid11_part365 : Audit := .cycle 2 17 true (1)
theorem kid11_part365_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part365) = true := by rfl

def kid11_part366 : Audit := .cycle 1 21 true (1)
theorem kid11_part366_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part366) = true := by rfl

def kid11_part367 : Audit := .split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (6),
.cycle 19 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 19 9 true (6),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.cycle 19 3 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 18 3 true (6),
.cycle 17 3 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 19 10 true (7)
])
theorem kid11_part367_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part367) = true := by rfl

def kid11_part368 : Audit := .split 28 (4,false) (byMove [
.cycle 1 29 true (1),
.cycle 7 37 true (2),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 18 11 true (6),
.cycle 27 2 true (9),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 20 9 true (6),
.cycle 3 26 true (1),
.cycle 28 1 true (10),
.cycle 8 21 true (2),
.cycle 6 23 true (2),
.cycle 26 3 true (8),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 27 3 true (9),
.cycle 17 12 true (5),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 28 1 true (10),
.cycle 19 10 true (6)
])
theorem kid11_part368_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part368) = true := by rfl

def kid11_part344 : Audit := .split 18 (4,true) (byMove [(kid11_part345),(kid11_part346),(kid11_part347),(kid11_part348),(kid11_part349),(kid11_part350),(kid11_part351),(kid11_part352),(kid11_part353),(kid11_part354),(kid11_part355),(kid11_part356),(kid11_part357),(kid11_part358),(kid11_part359),(kid11_part360),(kid11_part361),(kid11_part362),(kid11_part363),(kid11_part364),(kid11_part365),(kid11_part366),(kid11_part367),(kid11_part368)])

theorem kid11_part344_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part344) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part345),(kid11_part346),(kid11_part347),(kid11_part348),(kid11_part349),(kid11_part350),(kid11_part351),(kid11_part352),(kid11_part353),(kid11_part354),(kid11_part355),(kid11_part356),(kid11_part357),(kid11_part358),(kid11_part359),(kid11_part360),(kid11_part361),(kid11_part362),(kid11_part363),(kid11_part364),(kid11_part365),(kid11_part366),(kid11_part367),(kid11_part368)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part345_checked

  · exact kid11_part351_checked

  · exact kid11_part357_checked

  · exact kid11_part363_checked

  · exact kid11_part346_checked

  · exact kid11_part352_checked

  · exact kid11_part358_checked

  · exact kid11_part364_checked

  · exact kid11_part347_checked

  · exact kid11_part353_checked

  · exact kid11_part359_checked

  · exact kid11_part365_checked

  · exact kid11_part348_checked

  · exact kid11_part354_checked

  · exact kid11_part360_checked

  · exact kid11_part366_checked

  · exact kid11_part349_checked

  · exact kid11_part355_checked

  · exact kid11_part361_checked

  · exact kid11_part367_checked

  · exact kid11_part350_checked

  · exact kid11_part356_checked

  · exact kid11_part362_checked

  · exact kid11_part368_checked

def kid11_part369 : Audit := .cycle 18 9 true (6)
theorem kid11_part369_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part369) = true := by rfl

def kid11_part249 : Audit := .split 17 (5,true) (byMove [(kid11_part250),(kid11_part251),(kid11_part252),(kid11_part253),(kid11_part254),(kid11_part279),(kid11_part280),(kid11_part281),(kid11_part282),(kid11_part283),(kid11_part284),(kid11_part309),(kid11_part310),(kid11_part311),(kid11_part312),(kid11_part313),(kid11_part314),(kid11_part339),(kid11_part340),(kid11_part341),(kid11_part342),(kid11_part343),(kid11_part344),(kid11_part369)])

theorem kid11_part249_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (kid11_part249) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid11_part250),(kid11_part251),(kid11_part252),(kid11_part253),(kid11_part254),(kid11_part279),(kid11_part280),(kid11_part281),(kid11_part282),(kid11_part283),(kid11_part284),(kid11_part309),(kid11_part310),(kid11_part311),(kid11_part312),(kid11_part313),(kid11_part314),(kid11_part339),(kid11_part340),(kid11_part341),(kid11_part342),(kid11_part343),(kid11_part344),(kid11_part369)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part250_checked

  · exact kid11_part280_checked

  · exact kid11_part310_checked

  · exact kid11_part340_checked

  · exact kid11_part251_checked

  · exact kid11_part281_checked

  · exact kid11_part311_checked

  · exact kid11_part341_checked

  · exact kid11_part252_checked

  · exact kid11_part282_checked

  · exact kid11_part312_checked

  · exact kid11_part342_checked

  · exact kid11_part253_checked

  · exact kid11_part283_checked

  · exact kid11_part313_checked

  · exact kid11_part343_checked

  · exact kid11_part254_checked

  · exact kid11_part284_checked

  · exact kid11_part314_checked

  · exact kid11_part344_checked

  · exact kid11_part279_checked

  · exact kid11_part309_checked

  · exact kid11_part339_checked

  · exact kid11_part369_checked

def kid11_part371 : Audit := .cycle 0 16 true (0)
theorem kid11_part371_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part371) = true := by rfl

def kid11_part372 : Audit := .cycle 1 15 true (1)
theorem kid11_part372_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part372) = true := by rfl

def kid11_part373 : Audit := .cycle 2 14 true (1)
theorem kid11_part373_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part373) = true := by rfl

def kid11_part374 : Audit := .cycle 1 18 true (1)
theorem kid11_part374_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part374) = true := by rfl

def kid11_part375 : Audit := .split 16 (4,false) (byMove [
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 37 1 false (1),
.cycle 29 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 32 1 false (2),
.cycle 31 1 false (3),
.cycle 7 12 true (2),
.cycle 45 1 false (1),
.cycle 0 20 true (0),
.cycle 26 1 false (0),
.cycle 30 1 false (0),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 16 2 true (3),
.cycle 3 16 true (1)
]),
.cycle 0 18 true (0),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 21 1 false (-1),
.cycle 29 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 23 1 false (1),
.cycle 31 1 false (3),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 26 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 16 2 true (3),
.cycle 3 16 true (1)
]),
.cycle 37 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 9 true (2),
.cycle 3 14 true (1),
.cycle 16 1 true (4),
.cycle 8 9 true (2),
.cycle 6 11 true (2),
.split 21 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 40 1 false (2),
.cycle 45 1 false (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 25 4 false (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 9 14 true (2),
.cycle 3 19 true (1),
.cycle 19 3 true (2),
.cycle 8 14 true (2),
.cycle 6 16 true (2),
.cycle 30 5 false (1),
.cycle 1 25 true (1),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 25 4 false (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 34 9 false (2),
.cycle 3 20 true (1)
]),
.split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 25 true (0),
.cycle 7 15 true (1),
.cycle 29 1 false (1),
.cycle 1 18 true (1),
.cycle 49 1 false (9),
.cycle 49 1 false (9),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 0 22 true (0),
.cycle 29 5 false (2),
.cycle 7 19 true (1),
.cycle 1 20 true (1),
.cycle 26 1 false (0),
.cycle 5 15 true (1),
.cycle 1 20 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 19 (4,true)
]),
.cycle 1 18 true (1),
.split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 25 true (0),
.cycle 21 1 false (-1),
.cycle 29 1 false (1),
.cycle 1 18 true (1),
.cycle 49 1 false (9),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 30 1 false (6),
.cycle 24 1 false (0),
.cycle 29 5 false (2),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 26 1 false (0),
.cycle 21 1 false (-1),
.cycle 1 20 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 3 true (3),
.cycle 3 18 true (1)
]),
.cycle 7 15 true (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 16 1 true (4),
.cycle 3 15 true (1)
])
theorem kid11_part375_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part375) = true := by rfl

def kid11_part376 : Audit := .cycle 3 14 true (1)
theorem kid11_part376_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part376) = true := by rfl

def kid11_part377 : Audit := .cycle 0 16 true (0)
theorem kid11_part377_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part377) = true := by rfl

def kid11_part378 : Audit := .cycle 1 15 true (1)
theorem kid11_part378_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part378) = true := by rfl

def kid11_part379 : Audit := .split 25 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 9 18 true (2),
.cycle 3 23 true (1),
.split 26 (4,false) (byMove [
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.last 28 (4,true),
.cycle 3 25 true (1),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 16 11 true (3),
.cycle 9 18 true (2),
.cycle 26 1 true (6),
.cycle 17 11 true (3),
.cycle 7 21 true (2),
.last 29 (4,true),
.cycle 0 29 true (0),
.cycle 4 23 true (1),
.last 28 (4,true),
.cycle 0 29 true (0),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 26 1 true (6),
.cycle 3 25 true (1)
]),
.cycle 8 18 true (2),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 17 9 true (3),
.split 26 (4,false) (byMove [
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 16 11 true (3),
.cycle 9 18 true (2),
.last 30 (4,true),
.cycle 17 11 true (3),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.last 39 (4,true),
.last 37 (4,true),
.cycle 26 1 true (8),
.last 39 (4,true),
.cycle 7 21 true (2),
.cycle 25 3 true (7),
.cycle 0 29 true (0),
.cycle 18 9 true (3),
.last 30 (4,true),
.cycle 0 29 true (0),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 26 1 true (8),
.cycle 3 25 true (1)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 32, 32, 1, 64, 4, 64],80⟩,
.cycle 7 20 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.split 26 (4,false) (byMove [
.last 30 (4,true),
.cycle 0 30 true (0),
.cycle 10 18 true (2),
.last 32 (4,true),
.last 28 (4,true),
.cycle 10 18 true (2),
.cycle 1 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2, 8, 128, 256, 8, 128, 2, 8, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 25 2 true (6),
.cycle 0 28 true (0),
.last 27 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 8, 128, 256, 8, 128, 32, 8, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 14 14 true (3),
.last 29 (4,true),
.cycle 1 29 true (1),
.cycle 11 16 true (2),
.last 28 (4,true),
.cycle 1 29 true (1),
.cycle 1 27 true (1),
.cycle 7 20 true (2),
.last 28 (4,true),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 9 20 true (2)
]),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.split 26 (4,false) (byMove [
.cycle 1 27 true (1),
.last 39 (4,true),
.cycle 25 2 true (7),
.cycle 0 28 true (0),
.last 27 (4,true),
.last 39 (4,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 9 19 true (2),
.cycle 3 24 true (1),
.cycle 26 1 true (8),
.cycle 8 19 true (2),
.cycle 6 21 true (2),
.last 41 (4,true),
.last 28 (4,true),
.cycle 1 28 true (1),
.last 27 (4,true),
.cycle 24 3 true (6),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 26 1 true (8),
.cycle 3 25 true (1)
]),
.cycle 3 24 true (1)
])
theorem kid11_part379_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part379) = true := by rfl

def kid11_part380 : Audit := .cycle 9 7 true (2)
theorem kid11_part380_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part380) = true := by rfl

def kid11_part381 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 9 true (2),
.cycle 3 14 true (1),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (1),
.cycle 37 1 false (1),
.cycle 23 1 false (-1),
.cycle 33 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 31 (2,true),
.cycle 19 9 true (0),
.cycle 25 1 false (1),
.cycle 39 1 false (3),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 30 1 false (0),
.cycle 23 1 false (-1),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (3),
.cycle 3 18 true (1)
]),
.cycle 8 9 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.split 27 (4,true) (byMove [
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 9 29 true (2),
.cycle 0 35 true (0),
.cycle 0 31 true (0),
.cycle 8 29 true (2),
.cycle 1 28 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 32, 64, 1, 2, 16, 64],64⟩,
.last 28 (2,true),
.cycle 0 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 14 15 true (3),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 10 25 true (2),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 1 28 true (1),
.cycle 7 21 true (2),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 9 22 true (2),
.cycle 3 38 true (1)
]),
.split 25 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 9 18 true (2),
.cycle 3 23 true (1),
.cycle 9 18 true (2),
.cycle 8 18 true (2),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.last 37 (2,true),
.cycle 17 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 8, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 7 20 true (2),
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 3 24 true (1),
.cycle 3 24 true (1)
]),
.cycle 16 1 true (6),
.split 27 (4,true) (byMove [
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 9 29 true (2),
.cycle 0 35 true (0),
.cycle 0 31 true (0),
.cycle 8 29 true (2),
.cycle 1 28 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 32, 64, 1, 2, 16, 64],64⟩,
.last 28 (2,true),
.cycle 0 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 14 15 true (3),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 10 25 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 30 true (1),
.cycle 1 28 true (1),
.cycle 7 21 true (2),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 8 22 true (2),
.cycle 3 38 true (1)
]),
.cycle 7 11 true (2),
.split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.last 29 (4,true),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 15 4 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 16 3 true (5),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 14 5 true (4),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 19 (4,true),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 14 6 true (4),
.cycle 3 17 true (1)
]),
.cycle 0 19 true (0),
.cycle 10 7 true (2),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 5 17 true (1),
.cycle 60 1 false (4),
.cycle 1 71 true (0),
.cycle 23 1 false (-1),
.cycle 60 1 false (4),
.cycle 13 7 true (3),
.cycle 1 22 true (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 38 1 false (8),
.cycle 38 1 false (8),
.cycle 14 11 true (2),
.last 21 (2,true),
.cycle 12 9 true (2),
.cycle 51 1 false (3),
.cycle 23 1 false (-1),
.cycle 12 9 true (2),
.cycle 13 7 true (3),
.cycle 1 22 true (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 21 3 true (5),
.cycle 3 26 true (1)
]),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 16 1 true (6),
.cycle 3 15 true (1)
])
theorem kid11_part381_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part381) = true := by rfl

def kid11_part382 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 8, 64],[2, 32, 64, 1, 64, 32, 64],80⟩
theorem kid11_part382_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part382) = true := by rfl

def kid11_part383 : Audit := .cycle 7 10 true (2)
theorem kid11_part383_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part383) = true := by rfl

def kid11_part384 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 33 1 false (1),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 35 1 false (3),
.last 20 (4,false),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 45 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.last 19 (4,false),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 32 3 false (1),
.last 20 (4,false),
.cycle 1 20 true (1),
.last 20 (4,false),
.cycle 7 19 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 19 (4,false),
.cycle 3 17 true (1)
]),
.cycle 31 3 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 3 17 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 30 (4,true),
.cycle 9 10 true (2),
.cycle 18 1 true (6),
.last 30 (4,true),
.cycle 7 13 true (2),
.cycle 16 3 true (4),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (4,true),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 3 17 true (1)
]),
.cycle 8 10 true (2),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.split 18 (4,true) (byMove [
.cycle 16 4 true (3),
.cycle 0 22 true (0),
.last 20 (4,false),
.cycle 7 14 true (2),
.last 20 (4,false),
.cycle 38 1 false (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 8, 128, 256, 8, 128, 4096, 8, 4096],[128, 32, 4096, 1, 2, 32, 128, 32, 32, 1, 2, 32, 4096],5136⟩,
.last 20 (4,false),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 15 4 true (4),
.cycle 13 6 true (3),
.cycle 32 3 false (1),
.last 20 (4,false),
.cycle 5 14 true (1),
.last 20 (4,false),
.cycle 12 12 true (1),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 17 2 true (4),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 14 6 true (4)
]),
.cycle 31 3 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.split 18 (4,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 17 2 true (5),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 14 6 true (4),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 18 1 true (6),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 14 5 true (4),
.last 20 (4,true),
.cycle 1 20 true (1),
.last 19 (4,true),
.last 24 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 18 1 true (6),
.cycle 3 17 true (1)
]),
.cycle 3 16 true (1)
])
theorem kid11_part384_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part384) = true := by rfl

def kid11_part385 : Audit := .cycle 0 18 true (0)
theorem kid11_part385_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part385) = true := by rfl

def kid11_part386 : Audit := .cycle 4 12 true (1)
theorem kid11_part386_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part386) = true := by rfl

def kid11_part388 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 37 1 false (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 12 true (2),
.cycle 3 17 true (1),
.cycle 0 21 true (0),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.cycle 14 6 true (3),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 1 21 true (1),
.cycle 3 18 true (1)
])
theorem kid11_part388_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part388) = true := by rfl

def kid11_part389 : Audit := .cycle 0 20 true (0)
theorem kid11_part389_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part389) = true := by rfl

def kid11_part390 : Audit := .split 17 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 10 10 true (2),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 37 1 false (1),
.cycle 29 1 false (1),
.cycle 7 12 true (2),
.cycle 1 19 true (1),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.cycle 32 1 false (2),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.cycle 38 1 false (0),
.cycle 7 14 true (2),
.cycle 26 1 false (0),
.cycle 30 1 false (0),
.cycle 7 14 true (2),
.cycle 7 12 true (2),
.cycle 1 19 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 16 2 true (3),
.cycle 0 20 true (0)
])
theorem kid11_part390_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part390) = true := by rfl

def kid11_part391 : Audit := .cycle 7 12 true (2)
theorem kid11_part391_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part391) = true := by rfl

def kid11_part392 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 10 10 true (2),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 21 1 false (-1),
.cycle 29 1 false (1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 7 14 true (2),
.cycle 26 1 false (0),
.cycle 21 1 false (-1),
.cycle 7 14 true (2),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 16 2 true (3),
.cycle 0 20 true (0)
])
theorem kid11_part392_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part392) = true := by rfl

def kid11_part393 : Audit := .cycle 30 1 false (0)
theorem kid11_part393_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part393) = true := by rfl

def kid11_part394 : Audit := .cycle 1 17 true (1)
theorem kid11_part394_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part394) = true := by rfl

def kid11_part395 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 2, 8, 128, 256, 8, 128, 2, 8, 4096],[128, 32, 4096, 1, 4096, 32, 128, 32, 4096, 1, 4096, 4096, 4096],4096⟩
theorem kid11_part395_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part395) = true := by rfl

def kid11_part396 : Audit := .split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 8, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 9 9 true (2),
.last 31 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 8, 128, 256, 8, 128, 4, 8, 4096],[128, 32, 32, 1, 4096, 32, 128, 32, 32, 1, 4096, 4096, 4096],4096⟩,
.cycle 7 12 true (2),
.cycle 14 6 true (4),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1)
])
theorem kid11_part396_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part396) = true := by rfl

def kid11_part397 : Audit := .cycle 0 18 true (0)
theorem kid11_part397_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part397) = true := by rfl

def kid11_part398 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 18 1 true (4),
.cycle 3 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 29 (2,true),
.cycle 9 9 true (2),
.cycle 18 1 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 16, 8, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 18 1 true (6),
.cycle 3 16 true (1)
])
theorem kid11_part398_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part398) = true := by rfl

def kid11_part399 : Audit := .cycle 15 2 true (4)
theorem kid11_part399_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part399) = true := by rfl

def kid11_part400 : Audit := .cycle 13 4 true (3)
theorem kid11_part400_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part400) = true := by rfl

def kid11_part401 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (1),
.cycle 1 25 true (1),
.cycle 1 31 true (0),
.cycle 14 10 true (2),
.last 22 (4,true),
.cycle 25 4 false (1),
.cycle 6 16 true (2),
.cycle 17 26 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 8, 128, 256, 8, 128, 4, 8, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 32 7 false (2),
.cycle 35 9 false (2),
.cycle 30 5 false (1),
.cycle 12 12 true (1),
.cycle 12 10 true (2),
.last 22 (4,true),
.cycle 25 4 false (1),
.cycle 6 16 true (2),
.cycle 36 11 false (3),
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part401_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part401) = true := by rfl

def kid11_part402 : Audit := .split 17 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 1 21 true (1),
.cycle 29 1 false (1),
.cycle 1 25 true (0),
.cycle 14 8 true (1),
.cycle 29 1 false (1),
.cycle 6 12 true (2),
.cycle 1 23 true (1),
.cycle 41 1 false (9),
.cycle 1 19 true (1),
.last 18 (4,true),
.cycle 5 16 true (1),
.cycle 29 5 false (2),
.cycle 12 12 true (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 12 8 true (1),
.cycle 5 14 true (1),
.cycle 6 12 true (2),
.cycle 14 4 true (3),
.cycle 2 18 true (1),
.cycle 1 19 true (1),
.last 18 (4,true),
.last 19 (4,true)
])
theorem kid11_part402_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part402) = true := by rfl

def kid11_part403 : Audit := .cycle 5 12 true (1)
theorem kid11_part403_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part403) = true := by rfl

def kid11_part404 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 29 1 false (1),
.cycle 1 25 true (0),
.cycle 21 1 false (-1),
.cycle 29 1 false (1),
.cycle 6 12 true (2),
.cycle 27 1 false (1),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 33 1 false (7),
.cycle 24 1 false (0),
.cycle 29 5 false (2),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 21 1 false (-1),
.cycle 5 14 true (1),
.cycle 6 12 true (2),
.cycle 14 4 true (3),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 18 3 true (4),
.cycle 17 2 true (3)
])
theorem kid11_part404_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part404) = true := by rfl

def kid11_part405 : Audit := .cycle 12 8 true (1)
theorem kid11_part405_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part405) = true := by rfl

def kid11_part406 : Audit := .cycle 1 17 true (1)
theorem kid11_part406_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part406) = true := by rfl

def kid11_part407 : Audit := .cycle 7 10 true (2)
theorem kid11_part407_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part407) = true := by rfl

def kid11_part408 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 33 1 false (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.cycle 2 17 true (1),
.cycle 8 10 true (2),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 2 17 true (1),
.cycle 3 16 true (1)
])
theorem kid11_part408_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part408) = true := by rfl

def kid11_part409 : Audit := .cycle 0 18 true (0)
theorem kid11_part409_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part409) = true := by rfl

def kid11_part410 : Audit := .split 17 (4,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 20 1 true (2),
.cycle 33 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.cycle 18 1 true (6),
.cycle 8 10 true (2),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 25 3 false (1),
.cycle 5 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 18 1 true (6),
.cycle 3 16 true (1)
])
theorem kid11_part410_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part410) = true := by rfl

def kid11_part411 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 7 14 true (2),
.cycle 10 12 true (2),
.cycle 38 1 false (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 8, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 3 19 true (1),
.cycle 15 4 true (4),
.cycle 13 6 true (3),
.last 25 (2,true),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 26 3 false (0),
.cycle 12 12 true (1),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 3 19 true (1),
.cycle 17 2 true (4)
])
theorem kid11_part411_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part411) = true := by rfl

def kid11_part387 : Audit := .split 16 (4,false) (byMove [(kid11_part388),(kid11_part389),(kid11_part390),(kid11_part391),(kid11_part392),(kid11_part393),(kid11_part394),(kid11_part395),(kid11_part396),(kid11_part397),(kid11_part398),(kid11_part399),(kid11_part400),(kid11_part401),(kid11_part402),(kid11_part403),(kid11_part404),(kid11_part405),(kid11_part406),(kid11_part407),(kid11_part408),(kid11_part409),(kid11_part410),(kid11_part411)])

theorem kid11_part387_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part387) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) 16 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part388),(kid11_part389),(kid11_part390),(kid11_part391),(kid11_part392),(kid11_part393),(kid11_part394),(kid11_part395),(kid11_part396),(kid11_part397),(kid11_part398),(kid11_part399),(kid11_part400),(kid11_part401),(kid11_part402),(kid11_part403),(kid11_part404),(kid11_part405),(kid11_part406),(kid11_part407),(kid11_part408),(kid11_part409),(kid11_part410),(kid11_part411)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part388_checked

  · exact kid11_part394_checked

  · exact kid11_part400_checked

  · exact kid11_part406_checked

  · exact kid11_part389_checked

  · exact kid11_part395_checked

  · exact kid11_part401_checked

  · exact kid11_part407_checked

  · exact kid11_part390_checked

  · exact kid11_part396_checked

  · exact kid11_part402_checked

  · exact kid11_part408_checked

  · exact kid11_part391_checked

  · exact kid11_part397_checked

  · exact kid11_part403_checked

  · exact kid11_part409_checked

  · exact kid11_part392_checked

  · exact kid11_part398_checked

  · exact kid11_part404_checked

  · exact kid11_part410_checked

  · exact kid11_part393_checked

  · exact kid11_part399_checked

  · exact kid11_part405_checked

  · exact kid11_part411_checked

def kid11_part412 : Audit := .cycle 0 18 true (0)
theorem kid11_part412_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part412) = true := by rfl

def kid11_part413 : Audit := .cycle 0 16 true (0)
theorem kid11_part413_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part413) = true := by rfl

def kid11_part414 : Audit := .cycle 1 15 true (1)
theorem kid11_part414_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part414) = true := by rfl

def kid11_part415 : Audit := .cycle 2 14 true (1)
theorem kid11_part415_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part415) = true := by rfl

def kid11_part416 : Audit := .cycle 1 18 true (1)
theorem kid11_part416_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part416) = true := by rfl

def kid11_part417 : Audit := .split 16 (4,false) (byMove [
.cycle 1 17 true (1),
.split 27 (4,true) (byMove [
.cycle 1 28 true (1),
.cycle 17 11 true (3),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 47 1 false (3),
.cycle 15 13 true (3),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 9 20 true (2),
.cycle 3 25 true (1),
.cycle 1 28 true (1),
.cycle 8 20 true (2),
.cycle 6 22 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1056, 8, 8, 128, 256, 8, 128, 8, 8, 4096],[128, 32, 4096, 1, 4096, 1024, 128, 32, 4096, 1, 1024, 1024, 4096],4096⟩,
.last 28 (2,true),
.cycle 1 29 true (1),
.cycle 1 33 true (1),
.cycle 26 2 true (6),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 7 22 true (2),
.cycle 3 26 true (1)
]),
.split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 41 1 false (1),
.cycle 3 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (4,true),
.cycle 9 9 true (2),
.cycle 9 11 true (2),
.last 27 (4,true),
.cycle 7 12 true (2),
.cycle 14 6 true (4),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 34 1 false (0),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 16 2 true (5),
.cycle 3 16 true (1)
]),
.cycle 0 18 true (0),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 23 1 false (-1),
.cycle 3 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 20 true (2),
.cycle 9 9 true (2),
.cycle 27 1 false (1),
.cycle 8 20 true (2),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 23 1 false (-1),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 16 2 true (5),
.cycle 3 16 true (1)
]),
.cycle 15 2 true (5),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 9 true (2),
.cycle 3 14 true (1),
.cycle 16 1 true (6),
.cycle 8 9 true (2),
.cycle 6 11 true (2),
.cycle 14 3 true (4),
.split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 10 9 true (2),
.cycle 0 24 true (0),
.cycle 0 27 true (0),
.cycle 10 9 true (2),
.cycle 1 18 true (1),
.last 29 (4,true),
.last 29 (4,true),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 15 3 true (5),
.cycle 14 5 true (4),
.last 22 (4,true),
.cycle 1 20 true (1),
.cycle 11 7 true (2),
.last 26 (4,true),
.cycle 1 20 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 15 3 true (5)
]),
.cycle 1 18 true (1),
.split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 9 true (2),
.last 22 (2,true),
.cycle 23 1 false (-1),
.cycle 10 9 true (2),
.cycle 1 18 true (1),
.cycle 1 40 true (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 45 1 false (9),
.cycle 15 3 true (5),
.cycle 14 5 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 11 7 true (2),
.cycle 23 1 false (-1),
.cycle 1 20 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 3 true (5),
.cycle 15 3 true (5)
]),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 17 11 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 27 true (0),
.cycle 15 4 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 0 22 true (0),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 14 5 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 17 12 true (1),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 16 3 true (5),
.cycle 3 17 true (1)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 16 1 true (6),
.cycle 3 15 true (1)
])
theorem kid11_part417_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part417) = true := by rfl

def kid11_part418 : Audit := .cycle 3 14 true (1)
theorem kid11_part418_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part418) = true := by rfl

def kid11_part370 : Audit := .split 15 (5,true) (byMove [(kid11_part371),(kid11_part372),(kid11_part373),(kid11_part374),(kid11_part375),(kid11_part376),(kid11_part377),(kid11_part378),(kid11_part379),(kid11_part380),(kid11_part381),(kid11_part382),(kid11_part383),(kid11_part384),(kid11_part385),(kid11_part386),(kid11_part387),(kid11_part412),(kid11_part413),(kid11_part414),(kid11_part415),(kid11_part416),(kid11_part417),(kid11_part418)])

theorem kid11_part370_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (kid11_part370) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some mv)) (byMove [(kid11_part371),(kid11_part372),(kid11_part373),(kid11_part374),(kid11_part375),(kid11_part376),(kid11_part377),(kid11_part378),(kid11_part379),(kid11_part380),(kid11_part381),(kid11_part382),(kid11_part383),(kid11_part384),(kid11_part385),(kid11_part386),(kid11_part387),(kid11_part412),(kid11_part413),(kid11_part414),(kid11_part415),(kid11_part416),(kid11_part417),(kid11_part418)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part371_checked

  · exact kid11_part377_checked

  · exact kid11_part383_checked

  · exact kid11_part413_checked

  · exact kid11_part372_checked

  · exact kid11_part378_checked

  · exact kid11_part384_checked

  · exact kid11_part414_checked

  · exact kid11_part373_checked

  · exact kid11_part379_checked

  · exact kid11_part385_checked

  · exact kid11_part415_checked

  · exact kid11_part374_checked

  · exact kid11_part380_checked

  · exact kid11_part386_checked

  · exact kid11_part416_checked

  · exact kid11_part375_checked

  · exact kid11_part381_checked

  · exact kid11_part387_checked

  · exact kid11_part417_checked

  · exact kid11_part376_checked

  · exact kid11_part382_checked

  · exact kid11_part412_checked

  · exact kid11_part418_checked

def kid11_part420 : Audit := .cycle 0 10 true (0)
theorem kid11_part420_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part420) = true := by rfl

def kid11_part421 : Audit := .cycle 1 9 true (1)
theorem kid11_part421_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part421) = true := by rfl

def kid11_part422 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 41 1 false (1),
.cycle 35 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 34 1 false (2),
.cycle 37 1 false (3),
.cycle 7 14 true (2),
.cycle 49 1 false (1),
.cycle 0 22 true (0),
.cycle 28 1 false (0),
.cycle 32 1 false (0),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (3),
.cycle 2 20 true (1)
]),
.cycle 2 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 27 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 10 18 true (2),
.cycle 3 25 true (1),
.cycle 2 27 true (1),
.cycle 8 20 true (2),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 46, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 19 9 true (3),
.cycle 18 11 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 54, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 22 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 46, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 30 true (0),
.cycle 12 16 true (2),
.cycle 12 18 true (2),
.last 29 (4,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 27 2 true (7),
.cycle 2 28 true (1)
]),
.cycle 11 7 true (2),
.cycle 9 9 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 32, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 32, 4096, 1, 4096, 32, 128, 32, 4096, 1, 4096, 32, 4096],5120⟩,
.cycle 7 12 true (2),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 35 1 false (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 33 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.cycle 2 19 true (1),
.cycle 8 12 true (2),
.cycle 6 14 true (2),
.cycle 16 4 true (4),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 33 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 2 true (5),
.cycle 2 20 true (1)
]),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 41 1 false (1),
.cycle 35 1 false (1),
.cycle 7 14 true (2),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.cycle 34 1 false (2),
.last 21 (4,true),
.last 23 (4,true),
.cycle 40 1 false (0),
.cycle 7 16 true (2),
.cycle 28 1 false (0),
.cycle 32 1 false (0),
.last 21 (4,true),
.cycle 7 14 true (2),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (3),
.last 21 (4,true)
]),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (2,true),
.cycle 2 20 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 31 (2,true),
.cycle 11 9 true (2),
.cycle 9 11 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 32, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 32, 4096, 1, 32, 32, 128, 32, 4096, 1, 32, 32, 4096],5120⟩,
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (2,true),
.cycle 2 20 true (1)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 45 1 false (1),
.cycle 2 20 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (4,true),
.cycle 11 9 true (2),
.cycle 9 11 true (2),
.last 31 (4,true),
.cycle 7 14 true (2),
.cycle 16 6 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 36 1 false (0),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (5),
.cycle 2 20 true (1)
]),
.cycle 2 18 true (1)
])
theorem kid11_part422_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part422) = true := by rfl

def kid11_part423 : Audit := .cycle 3 7 true (1)
theorem kid11_part423_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part423) = true := by rfl

def kid11_part424 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.last 26 (2,true),
.cycle 25 1 false (3),
.cycle 27 1 false (3),
.cycle 1 22 true (0),
.cycle 31 1 false (3),
.last 22 (2,true),
.cycle 0 23 true (0),
.last 34 (2,true),
.cycle 31 1 false (3),
.cycle 23 15 true (2),
.last 23 (2,true),
.cycle 1 24 true (0),
.cycle 37 1 false (5),
.cycle 1 26 true (0),
.last 24 (2,true),
.cycle 1 22 true (0),
.cycle 7 15 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 11 20 true (0),
.cycle 10 26 true (0)
]),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (3),
.cycle 1 22 true (0),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 62, 16, 64],[2, 32, 64, 1, 8, 2, 64],64⟩,
.last 29 (2,true),
.cycle 13 7 true (0),
.cycle 24 1 false (2),
.cycle 26 1 false (2),
.cycle 37 1 false (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.cycle 22 1 false (2),
.cycle 12 9 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.last 39 (2,true),
.cycle 1 22 true (0),
.cycle 11 9 true (0),
.cycle 10 11 true (0)
]),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 21 7 false (3),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (5,true),
.cycle 3 12 true (1),
.last 19 (5,true),
.last 21 (5,true),
.last 23 (5,true),
.last 16 (5,true),
.cycle 1 31 true (-1),
.cycle 1 16 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 18 (5,true),
.last 20 (5,true)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part424_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part424) = true := by rfl

def kid11_part425 : Audit := .cycle 8 2 true (4)
theorem kid11_part425_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part425) = true := by rfl

def kid11_part426 : Audit := .cycle 0 10 true (0)
theorem kid11_part426_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part426) = true := by rfl

def kid11_part427 : Audit := .cycle 1 9 true (1)
theorem kid11_part427_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part427) = true := by rfl

def kid11_part429 : Audit := .split 22 (2,true) (byMove [
.cycle 1 26 true (1),
.last 25 (4,true),
.last 43 (4,true),
.cycle 7 18 true (2),
.last 23 (4,true),
.cycle 0 28 true (0),
.cycle 1 23 true (1),
.cycle 0 42 true (0),
.cycle 0 44 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 0 42 true (0),
.cycle 5 18 true (1),
.last 23 (4,true),
.cycle 21 4 true (4),
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 1 24 true (1)
])
theorem kid11_part429_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part429) = true := by rfl

def kid11_part430 : Audit := .cycle 1 23 true (1)
theorem kid11_part430_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part430) = true := by rfl

def kid11_part431 : Audit := .cycle 2 32 true (1)
theorem kid11_part431_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part431) = true := by rfl

def kid11_part432 : Audit := .split 24 (2,true) (byMove [
.cycle 1 28 true (1),
.last 27 (4,true),
.cycle 44 1 false (2),
.cycle 7 20 true (2),
.last 25 (4,true),
.cycle 0 32 true (0),
.cycle 1 25 true (1),
.cycle 3 43 true (1),
.cycle 1 50 true (1),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 1 28 true (1),
.cycle 1 30 true (1),
.cycle 1 36 true (1),
.cycle 1 34 true (1),
.cycle 5 20 true (1),
.last 25 (4,true),
.cycle 1 32 true (1),
.cycle 1 25 true (1),
.cycle 7 18 true (2),
.cycle 2 24 true (1),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 0 27 true (0)
])
theorem kid11_part432_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part432) = true := by rfl

def kid11_part433 : Audit := .cycle 1 23 true (1)
theorem kid11_part433_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part433) = true := by rfl

def kid11_part434 : Audit := .split 22 (2,true) (byMove [
.cycle 1 26 true (1),
.cycle 0 26 true (0),
.cycle 24 22 true (3),
.last 29 (4,true),
.cycle 0 26 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 60, 1, 4096, 60, 4096],4096⟩,
.cycle 1 23 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 38, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 2, 1, 4096, 4, 128, 32, 2, 1, 4096, 318, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 60, 4096],4096⟩,
.cycle 0 24 true (0),
.last 23 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 32, 1, 4096, 60, 4096],4096⟩,
.cycle 7 34 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 60, 4096],4096⟩,
.cycle 1 25 true (1),
.cycle 23 20 true (3),
.cycle 21 2 true (5),
.last 24 (4,true),
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 8 17 true (2)
])
theorem kid11_part434_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part434) = true := by rfl

def kid11_part435 : Audit := .cycle 6 14 true (2)
theorem kid11_part435_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part435) = true := by rfl

def kid11_part436 : Audit := .cycle 1 21 true (1)
theorem kid11_part436_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part436) = true := by rfl

def kid11_part437 : Audit := .split 20 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 0 24 true (0),
.cycle 22 18 true (3),
.last 27 (4,true),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 47, 4, 16, 64],[2, 32, 12, 1, 64, 4, 64],64⟩,
.cycle 1 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 2, 1, 64, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 22 true (0),
.last 21 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 28 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 1 23 true (1),
.cycle 21 16 true (3),
.cycle 20 2 true (5),
.last 22 (4,true),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 30 12 true (7)
])
theorem kid11_part437_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part437) = true := by rfl

def kid11_part438 : Audit := .cycle 1 21 true (1)
theorem kid11_part438_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part438) = true := by rfl

def kid11_part439 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 9 29 true (2),
.cycle 3 25 true (1),
.cycle 0 24 true (0),
.last 23 (2,true),
.cycle 1 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 2, 16, 64],64⟩,
.last 21 (2,true),
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 9 15 true (2),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 9 25 true (2),
.last 22 (2,true),
.cycle 20 2 true (5),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 9 22 true (2),
.cycle 22 12 true (6)
])
theorem kid11_part439_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part439) = true := by rfl

def kid11_part440 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 4, 16, 64],[2, 32, 64, 1, 64, 32, 64],64⟩
theorem kid11_part440_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part440) = true := by rfl

def kid11_part441 : Audit := .cycle 7 20 true (2)
theorem kid11_part441_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part441) = true := by rfl

def kid11_part442 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (1),
.last 24 (4,true),
.cycle 37 1 false (1),
.cycle 0 29 true (0),
.last 22 (4,true),
.cycle 35 3 false (1),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.cycle 10 14 true (2),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 8 20 true (2),
.cycle 6 26 true (2),
.cycle 18 4 true (4),
.cycle 5 38 true (1),
.cycle 1 29 true (1),
.last 22 (4,true),
.cycle 35 3 false (1),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 23 18 true (5)
])
theorem kid11_part442_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part442) = true := by rfl

def kid11_part443 : Audit := .cycle 5 16 true (1)
theorem kid11_part443_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part443) = true := by rfl

def kid11_part444 : Audit := .cycle 4 26 true (1)
theorem kid11_part444_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part444) = true := by rfl

def kid11_part445 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (1),
.cycle 1 25 true (1),
.cycle 2 38 true (1),
.cycle 7 22 true (2),
.cycle 1 25 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4104, 1, 4096, 4096, 4096],4096⟩,
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 23 true (1),
.last 22 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 32, 1, 4096, 32, 128, 32, 32, 1, 4096, 4096, 4096],4096⟩,
.cycle 7 26 true (2),
.cycle 18 6 true (4),
.cycle 5 18 true (1),
.cycle 4 32 true (1),
.cycle 20 2 true (4),
.last 23 (4,true),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part445_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part445) = true := by rfl

def kid11_part446 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 2 38 true (1),
.last 26 (2,true),
.cycle 1 25 true (1),
.last 24 (2,true),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 4, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 26 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 4 32 true (1),
.last 23 (2,true),
.cycle 20 2 true (4),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 23 11 true (7),
.cycle 19 4 true (4)
])
theorem kid11_part446_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part446) = true := by rfl

def kid11_part447 : Audit := .cycle 6 14 true (2)
theorem kid11_part447_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part447) = true := by rfl

def kid11_part448 : Audit := .cycle 1 21 true (1)
theorem kid11_part448_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part448) = true := by rfl

def kid11_part449 : Audit := .split 20 (2,true) (byMove [
.cycle 1 24 true (1),
.last 23 (4,true),
.last 29 (4,true),
.cycle 7 16 true (2),
.last 21 (4,true),
.cycle 0 24 true (0),
.cycle 1 21 true (1),
.cycle 2 36 true (1),
.cycle 2 38 true (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 2 20 true (1),
.cycle 2 22 true (1),
.cycle 2 24 true (1),
.cycle 5 18 true (1),
.cycle 5 16 true (1),
.last 21 (4,true),
.cycle 19 2 true (5),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 2 20 true (1)
])
theorem kid11_part449_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part449) = true := by rfl

def kid11_part450 : Audit := .cycle 1 21 true (1)
theorem kid11_part450_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part450) = true := by rfl

def kid11_part451 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 1 23 true (1),
.last 21 (2,true),
.cycle 7 16 true (2),
.cycle 33 9 true (4),
.last 23 (2,true),
.cycle 1 21 true (1),
.cycle 36 9 true (10),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 9 13 true (2),
.cycle 21 9 true (7),
.cycle 21 9 true (5),
.cycle 24 9 true (6),
.last 21 (2,true),
.cycle 5 16 true (1),
.last 23 (2,true),
.cycle 19 2 true (5),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 9 true (7),
.cycle 21 9 true (7)
])
theorem kid11_part451_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part451) = true := by rfl

def kid11_part452 : Audit := .cycle 20 12 true (6)
theorem kid11_part452_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part452) = true := by rfl

def kid11_part428 : Audit := .split 19 (5,true) (byMove [(kid11_part429),(kid11_part430),(kid11_part431),(kid11_part432),(kid11_part433),(kid11_part434),(kid11_part435),(kid11_part436),(kid11_part437),(kid11_part438),(kid11_part439),(kid11_part440),(kid11_part441),(kid11_part442),(kid11_part443),(kid11_part444),(kid11_part445),(kid11_part446),(kid11_part447),(kid11_part448),(kid11_part449),(kid11_part450),(kid11_part451),(kid11_part452)])

theorem kid11_part428_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part428) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid11_part429),(kid11_part430),(kid11_part431),(kid11_part432),(kid11_part433),(kid11_part434),(kid11_part435),(kid11_part436),(kid11_part437),(kid11_part438),(kid11_part439),(kid11_part440),(kid11_part441),(kid11_part442),(kid11_part443),(kid11_part444),(kid11_part445),(kid11_part446),(kid11_part447),(kid11_part448),(kid11_part449),(kid11_part450),(kid11_part451),(kid11_part452)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part429_checked

  · exact kid11_part435_checked

  · exact kid11_part441_checked

  · exact kid11_part447_checked

  · exact kid11_part430_checked

  · exact kid11_part436_checked

  · exact kid11_part442_checked

  · exact kid11_part448_checked

  · exact kid11_part431_checked

  · exact kid11_part437_checked

  · exact kid11_part443_checked

  · exact kid11_part449_checked

  · exact kid11_part432_checked

  · exact kid11_part438_checked

  · exact kid11_part444_checked

  · exact kid11_part450_checked

  · exact kid11_part433_checked

  · exact kid11_part439_checked

  · exact kid11_part445_checked

  · exact kid11_part451_checked

  · exact kid11_part434_checked

  · exact kid11_part440_checked

  · exact kid11_part446_checked

  · exact kid11_part452_checked

def kid11_part454 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 0 32 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 29 true (0),
.cycle 3 18 true (1),
.cycle 0 29 true (0),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 0 23 true (0),
.cycle 0 29 true (0),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 19 4 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 3 19 true (1),
.cycle 0 30 true (0)
])
theorem kid11_part454_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part454) = true := by rfl

def kid11_part455 : Audit := .cycle 0 21 true (0)
theorem kid11_part455_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part455) = true := by rfl

def kid11_part456 : Audit := .cycle 2 23 true (1)
theorem kid11_part456_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part456) = true := by rfl

def kid11_part457 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 1 33 true (1),
.cycle 3 20 true (1),
.cycle 1 33 true (1),
.cycle 8 15 true (2),
.cycle 6 17 true (2),
.cycle 1 27 true (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.last 23 (4,true),
.cycle 7 19 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 3 21 true (1),
.cycle 1 34 true (1)
])
theorem kid11_part457_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part457) = true := by rfl

def kid11_part458 : Audit := .cycle 3 23 true (1)
theorem kid11_part458_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part458) = true := by rfl

def kid11_part459 : Audit := .cycle 0 21 true (0)
theorem kid11_part459_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part459) = true := by rfl

def kid11_part460 : Audit := .cycle 1 18 true (1)
theorem kid11_part460_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part460) = true := by rfl

def kid11_part461 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 8, 16, 64],[2, 32, 64, 1, 64, 2, 64],64⟩
theorem kid11_part461_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part461) = true := by rfl

def kid11_part462 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 18 true (2),
.cycle 3 16 true (1),
.cycle 10 18 true (2),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 10 9 true (2),
.last 30 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 13 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 21 true (0),
.cycle 10 16 true (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 10 19 true (2)
])
theorem kid11_part462_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part462) = true := by rfl

def kid11_part463 : Audit := .cycle 0 19 true (0)
theorem kid11_part463_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part463) = true := by rfl

def kid11_part464 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 18 true (2),
.cycle 3 16 true (1),
.cycle 9 18 true (2),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 30 (2,true),
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 16 true (2),
.cycle 0 21 true (0),
.cycle 18 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 9 19 true (2)
])
theorem kid11_part464_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part464) = true := by rfl

def kid11_part465 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 8, 16, 64],[2, 32, 64, 1, 64, 32, 64],64⟩
theorem kid11_part465_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part465) = true := by rfl

def kid11_part466 : Audit := .cycle 7 15 true (2)
theorem kid11_part466_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part466) = true := by rfl

def kid11_part467 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 35 1 false (1),
.cycle 7 15 true (2),
.last 20 (4,true),
.cycle 33 3 false (1),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.cycle 10 12 true (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.cycle 5 27 true (1),
.cycle 5 15 true (1),
.last 20 (4,true),
.cycle 33 3 false (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 21 11 true (5)
])
theorem kid11_part467_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part467) = true := by rfl

def kid11_part468 : Audit := .cycle 1 20 true (1)
theorem kid11_part468_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part468) = true := by rfl

def kid11_part469 : Audit := .cycle 4 19 true (1)
theorem kid11_part469_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part469) = true := by rfl

def kid11_part470 : Audit := .cycle 1 20 true (1)
theorem kid11_part470_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part470) = true := by rfl

def kid11_part471 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.last 24 (2,true),
.cycle 3 27 true (1),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 8, 16, 64],[2, 32, 64, 1, 2, 34, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 8, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (4),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 3 19 true (1),
.cycle 17 4 true (4)
])
theorem kid11_part471_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part471) = true := by rfl

def kid11_part472 : Audit := .cycle 1 18 true (1)
theorem kid11_part472_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part472) = true := by rfl

def kid11_part473 : Audit := .cycle 7 11 true (2)
theorem kid11_part473_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part473) = true := by rfl

def kid11_part474 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.last 34 (4,true),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 2 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 25 true (1),
.cycle 3 16 true (1),
.cycle 2 25 true (1),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 2 19 true (1),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 19 (4,true),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 2 26 true (1)
])
theorem kid11_part474_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part474) = true := by rfl

def kid11_part475 : Audit := .cycle 0 19 true (0)
theorem kid11_part475_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part475) = true := by rfl

def kid11_part476 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 34 true (1),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 3 18 true (1),
.cycle 3 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 3 25 true (1),
.cycle 3 16 true (1),
.cycle 3 25 true (1),
.cycle 8 11 true (2),
.cycle 6 13 true (2),
.cycle 3 19 true (1),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 3 26 true (1)
])
theorem kid11_part476_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part476) = true := by rfl

def kid11_part477 : Audit := .cycle 18 9 true (6)
theorem kid11_part477_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part477) = true := by rfl

def kid11_part453 : Audit := .split 17 (5,true) (byMove [(kid11_part454),(kid11_part455),(kid11_part456),(kid11_part457),(kid11_part458),(kid11_part459),(kid11_part460),(kid11_part461),(kid11_part462),(kid11_part463),(kid11_part464),(kid11_part465),(kid11_part466),(kid11_part467),(kid11_part468),(kid11_part469),(kid11_part470),(kid11_part471),(kid11_part472),(kid11_part473),(kid11_part474),(kid11_part475),(kid11_part476),(kid11_part477)])

theorem kid11_part453_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part453) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some mv)) (byMove [(kid11_part454),(kid11_part455),(kid11_part456),(kid11_part457),(kid11_part458),(kid11_part459),(kid11_part460),(kid11_part461),(kid11_part462),(kid11_part463),(kid11_part464),(kid11_part465),(kid11_part466),(kid11_part467),(kid11_part468),(kid11_part469),(kid11_part470),(kid11_part471),(kid11_part472),(kid11_part473),(kid11_part474),(kid11_part475),(kid11_part476),(kid11_part477)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part454_checked

  · exact kid11_part460_checked

  · exact kid11_part466_checked

  · exact kid11_part472_checked

  · exact kid11_part455_checked

  · exact kid11_part461_checked

  · exact kid11_part467_checked

  · exact kid11_part473_checked

  · exact kid11_part456_checked

  · exact kid11_part462_checked

  · exact kid11_part468_checked

  · exact kid11_part474_checked

  · exact kid11_part457_checked

  · exact kid11_part463_checked

  · exact kid11_part469_checked

  · exact kid11_part475_checked

  · exact kid11_part458_checked

  · exact kid11_part464_checked

  · exact kid11_part470_checked

  · exact kid11_part476_checked

  · exact kid11_part459_checked

  · exact kid11_part465_checked

  · exact kid11_part471_checked

  · exact kid11_part477_checked

def kid11_part478 : Audit := .cycle 9 1 true (5)
theorem kid11_part478_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part478) = true := by rfl

def kid11_part479 : Audit := .cycle 8 2 true (4)
theorem kid11_part479_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part479) = true := by rfl

def kid11_part480 : Audit := .cycle 7 4 true (3)
theorem kid11_part480_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part480) = true := by rfl

def kid11_part482 : Audit := .cycle 1 12 true (1)
theorem kid11_part482_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part482) = true := by rfl

def kid11_part483 : Audit := .cycle 7 5 true (3)
theorem kid11_part483_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part483) = true := by rfl

def kid11_part484 : Audit := .cycle 2 11 true (1)
theorem kid11_part484_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part484) = true := by rfl

def kid11_part485 : Audit := .cycle 0 13 true (0)
theorem kid11_part485_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part485) = true := by rfl

def kid11_part486 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 9 4 true (4),
.cycle 8 5 true (4),
.cycle 7 7 true (3),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.cycle 12 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 8 5 true (4)
])
theorem kid11_part486_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part486) = true := by rfl

def kid11_part487 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 20 (4,true),
.cycle 24 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 12 7 true (2),
.cycle 9 4 true (4),
.cycle 8 5 true (4),
.cycle 7 7 true (3),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.cycle 8 5 true (4)
])
theorem kid11_part487_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part487) = true := by rfl

def kid11_part488 : Audit := .cycle 0 12 true (0)
theorem kid11_part488_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part488) = true := by rfl

def kid11_part489 : Audit := .cycle 1 11 true (1)
theorem kid11_part489_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part489) = true := by rfl

def kid11_part490 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 14 true (4),
.cycle 8 12 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 13 7 true (4),
.cycle 9 11 true (4),
.cycle 8 12 true (4),
.cycle 7 14 true (3),
.cycle 10 10 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (6),
.cycle 8 12 true (4)
])
theorem kid11_part490_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part490) = true := by rfl

def kid11_part491 : Audit := .cycle 3 9 true (1)
theorem kid11_part491_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part491) = true := by rfl

def kid11_part492 : Audit := .cycle 9 3 true (4)
theorem kid11_part492_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part492) = true := by rfl

def kid11_part493 : Audit := .cycle 8 4 true (4)
theorem kid11_part493_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part493) = true := by rfl

def kid11_part494 : Audit := .cycle 6 6 true (2)
theorem kid11_part494_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part494) = true := by rfl

def kid11_part495 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 20 true (1),
.cycle 3 11 true (1),
.cycle 28 5 false (1),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 23 true (0),
.cycle 9 5 true (4),
.cycle 8 6 true (4),
.cycle 7 8 true (3),
.cycle 10 4 true (4),
.cycle 0 16 true (0),
.cycle 4 16 true (1),
.cycle 28 5 false (1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 3 true (4),
.cycle 8 6 true (4)
])
theorem kid11_part495_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part495) = true := by rfl

def kid11_part496 : Audit := .cycle 1 15 true (1)
theorem kid11_part496_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part496) = true := by rfl

def kid11_part497 : Audit := .cycle 1 13 true (1)
theorem kid11_part497_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part497) = true := by rfl

def kid11_part498 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (3),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 7 14 true (2),
.last 15 (5,true),
.last 18 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 21 (5,true),
.cycle 0 14 true (0),
.cycle 9 5 true (4),
.last 13 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 12 2 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part498_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part498) = true := by rfl

def kid11_part499 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (3),
.cycle 0 16 true (0),
.cycle 2 18 true (1),
.cycle 7 14 true (2),
.last 20 (4,true),
.cycle 24 5 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (4),
.cycle 7 10 true (3),
.cycle 25 3 false (1),
.cycle 1 15 true (1),
.cycle 4 14 true (1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (4)
])
theorem kid11_part499_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part499) = true := by rfl

def kid11_part500 : Audit := .cycle 0 12 true (0)
theorem kid11_part500_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part500) = true := by rfl

def kid11_part501 : Audit := .cycle 1 11 true (1)
theorem kid11_part501_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part501) = true := by rfl

def kid11_part502 : Audit := .cycle 2 10 true (1)
theorem kid11_part502_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part502) = true := by rfl

def kid11_part503 : Audit := .cycle 1 14 true (1)
theorem kid11_part503_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part503) = true := by rfl

def kid11_part504 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 36 9 false (2),
.cycle 8 7 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 40 (4,true),
.cycle 13 7 true (4),
.cycle 9 6 true (4),
.cycle 8 7 true (4),
.cycle 7 9 true (3),
.cycle 10 5 true (4),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 21 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (5),
.cycle 8 7 true (4)
])
theorem kid11_part504_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part504) = true := by rfl

def kid11_part505 : Audit := .cycle 8 4 true (4)
theorem kid11_part505_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part505) = true := by rfl

def kid11_part481 : Audit := .split 11 (2,true) (byMove [(kid11_part482),(kid11_part483),(kid11_part484),(kid11_part485),(kid11_part486),(kid11_part487),(kid11_part488),(kid11_part489),(kid11_part490),(kid11_part491),(kid11_part492),(kid11_part493),(kid11_part494),(kid11_part495),(kid11_part496),(kid11_part497),(kid11_part498),(kid11_part499),(kid11_part500),(kid11_part501),(kid11_part502),(kid11_part503),(kid11_part504),(kid11_part505)])

theorem kid11_part481_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part481) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part482),(kid11_part483),(kid11_part484),(kid11_part485),(kid11_part486),(kid11_part487),(kid11_part488),(kid11_part489),(kid11_part490),(kid11_part491),(kid11_part492),(kid11_part493),(kid11_part494),(kid11_part495),(kid11_part496),(kid11_part497),(kid11_part498),(kid11_part499),(kid11_part500),(kid11_part501),(kid11_part502),(kid11_part503),(kid11_part504),(kid11_part505)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part482_checked

  · exact kid11_part488_checked

  · exact kid11_part494_checked

  · exact kid11_part500_checked

  · exact kid11_part483_checked

  · exact kid11_part489_checked

  · exact kid11_part495_checked

  · exact kid11_part501_checked

  · exact kid11_part484_checked

  · exact kid11_part490_checked

  · exact kid11_part496_checked

  · exact kid11_part502_checked

  · exact kid11_part485_checked

  · exact kid11_part491_checked

  · exact kid11_part497_checked

  · exact kid11_part503_checked

  · exact kid11_part486_checked

  · exact kid11_part492_checked

  · exact kid11_part498_checked

  · exact kid11_part504_checked

  · exact kid11_part487_checked

  · exact kid11_part493_checked

  · exact kid11_part499_checked

  · exact kid11_part505_checked

def kid11_part506 : Audit := .cycle 0 12 true (0)
theorem kid11_part506_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part506) = true := by rfl

def kid11_part507 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 4 14 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.split 25 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 10 18 true (2),
.cycle 3 23 true (1),
.cycle 4 23 true (1),
.cycle 8 18 true (2),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 38, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 17 9 true (3),
.cycle 18 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 38, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 20 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 38, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.cycle 11 16 true (2),
.last 27 (4,true),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 1 28 true (1),
.cycle 4 24 true (1)
]),
.cycle 10 7 true (2),
.cycle 9 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 64, 32, 64],64⟩,
.cycle 7 10 true (2),
.split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 33 1 false (1),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 31 3 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 10 true (2),
.cycle 3 15 true (1),
.cycle 4 15 true (1),
.cycle 8 10 true (2),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.last 18 (4,true),
.cycle 31 3 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 20 true (1),
.cycle 4 16 true (1)
]),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 5 12 true (1),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 20 true (1),
.cycle 4 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 29 (2,true),
.cycle 10 9 true (2),
.cycle 9 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 5 14 true (1),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 20 true (1),
.cycle 4 16 true (1)
]),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 4 14 true (1)
])
theorem kid11_part507_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part507) = true := by rfl

def kid11_part509 : Audit := .split 15 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (1),
.cycle 20 1 false (0),
.last 19 (5,true),
.cycle 1 21 true (1),
.last 16 (5,true),
.cycle 6 10 true (1),
.last 17 (5,true),
.last 27 (5,true),
.cycle 1 17 true (1),
.cycle 0 27 true (0),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 23 (5,true),
.last 19 (5,true),
.cycle 14 4 true (1),
.last 16 (5,true),
.cycle 14 10 true (2),
.last 17 (5,true),
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.cycle 16 5 true (3),
.last 16 (5,true)
])
theorem kid11_part509_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part509) = true := by rfl

def kid11_part510 : Audit := .cycle 5 10 true (1)
theorem kid11_part510_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part510) = true := by rfl

def kid11_part511 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 1 23 true (0),
.cycle 46 1 false (4),
.last 24 (2,true),
.cycle 23 1 false (1),
.cycle 25 1 false (1),
.cycle 0 38 true (0),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 34, 34, 16, 8192, 16384, 8, 128, 34, 16, 33554432, 67108864, 2097152, 128, 1073741824, 4194304, 33554432, 67108864, 2097152, 34, 1073741824, 4194304, 33554432, 67108864, 134217728, 570425344, 1644167202, 268435456, 1073741824],[128, 32, 1073741824, 1, 34, 2, 8192, 32, 1073741824, 1, 1073741824, 2, 33554432, 8388608, 1073741824, 262144, 1073741824, 524288, 33554432, 8388608, 1073741824, 262144, 34, 524288, 33554432, 536870912, 1073741824, 16777216, 1644167168, 33554432, 1073741824],2144284736⟩,
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 43 1 false (3),
.cycle 31 1 false (1),
.last 33 (2,true),
.last 21 (2,true),
.cycle 0 44 true (0),
.cycle 40 1 false (4),
.cycle 23 1 false (1),
.cycle 52 1 false (4),
.last 27 (2,true),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 1 21 true (0),
.last 21 (2,true),
.last 26 (2,true)
])
theorem kid11_part511_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part511) = true := by rfl

def kid11_part512 : Audit := .split 17 (2,true) (byMove [
.cycle 1 24 true (0),
.cycle 38 1 false (2),
.cycle 21 1 false (1),
.last 21 (5,true),
.cycle 0 30 true (0),
.last 18 (5,true),
.cycle 6 12 true (0),
.last 19 (5,true),
.last 29 (5,true),
.cycle 1 19 true (0),
.last 30 (5,true),
.last 18 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 24 (5,true),
.last 21 (5,true),
.last 22 (5,true),
.last 18 (5,true),
.last 28 (5,true),
.last 19 (5,true),
.cycle 2 18 true (0),
.cycle 1 19 true (0),
.cycle 7 14 true (0),
.last 18 (5,true)
])
theorem kid11_part512_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part512) = true := by rfl

def kid11_part513 : Audit := .cycle 15 1 false (-1)
theorem kid11_part513_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part513) = true := by rfl

def kid11_part514 : Audit := .cycle 18 1 false (0)
theorem kid11_part514_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part514) = true := by rfl

def kid11_part515 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 25 (2,true),
.cycle 13 7 true (3),
.cycle 9 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 1, 32, 64],64⟩,
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2)
])
theorem kid11_part515_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part515) = true := by rfl

def kid11_part516 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 52 1 false (6),
.cycle 0 28 true (0),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 1 15 true (1),
.cycle 33 1 false (9),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 33 1 false (9),
.cycle 7 12 true (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 43 1 false (5),
.cycle 21 1 false (1),
.cycle 41 1 false (9),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 15 6 true (5)
])
theorem kid11_part516_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part516) = true := by rfl

def kid11_part517 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.last 21 (5,true),
.last 28 (5,true),
.cycle 18 1 false (0),
.cycle 21 1 false (1),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 27 (5,true),
.cycle 1 15 true (1),
.cycle 30 1 false (8),
.last 14 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 5 10 true (1),
.last 19 (5,true),
.cycle 18 1 false (0),
.last 33 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.last 14 (5,true)
])
theorem kid11_part517_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part517) = true := by rfl

def kid11_part518 : Audit := .cycle 5 8 true (1)
theorem kid11_part518_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part518) = true := by rfl

def kid11_part519 : Audit := .cycle 29 1 false (7)
theorem kid11_part519_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part519) = true := by rfl

def kid11_part520 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 49 1 false (5),
.cycle 1 31 true (0),
.cycle 18 1 false (0),
.cycle 21 1 false (1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 30 1 false (8),
.cycle 33 1 false (9),
.cycle 7 14 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 40 1 false (4),
.cycle 18 1 false (0),
.cycle 53 1 false (9),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.cycle 14 6 true (4)
])
theorem kid11_part520_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part520) = true := by rfl

def kid11_part521 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 2 28 true (1),
.last 20 (2,true),
.cycle 19 5 false (2),
.cycle 21 7 false (2),
.cycle 6 10 true (1),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 9 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 14 16 true (2),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 4 22 true (1),
.cycle 19 5 false (2),
.cycle 14 22 true (2),
.cycle 14 10 true (2),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 18 5 true (4),
.cycle 16 8 true (4)
])
theorem kid11_part521_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part521) = true := by rfl

def kid11_part522 : Audit := .split 14 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 73 1 false (7),
.cycle 18 1 false (0),
.last 18 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 28 (5,true),
.cycle 5 10 true (1),
.last 28 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 21 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.cycle 2 16 true (1),
.cycle 5 10 true (1),
.last 17 (5,true),
.last 15 (5,true)
])
theorem kid11_part522_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part522) = true := by rfl

def kid11_part523 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.cycle 5 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 14 7 true (2),
.cycle 9 9 true (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 32, 32, 16, 8192, 16384, 8, 128, 128, 16, 33554432, 67108864, 2097152, 128, 1073741824, 4194304, 33554432, 67108864, 2097152, 32, 1073741824, 4194304, 33554432, 67108864, 134217728, 570425344, 1644167168, 268435456, 1073741824],[128, 32, 1073741824, 1, 1, 32, 8192, 32, 1073741824, 1, 1073741824, 32, 33554432, 8388608, 1073741824, 262144, 1073741824, 8388608, 33554432, 8388608, 1073741824, 262144, 262144, 8388608, 33554432, 536870912, 1073741824, 16777216, 1090519040, 536870912, 1073741824],2144284736⟩,
.last 25 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 5 16 true (1),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.cycle 5 18 true (1)
])
theorem kid11_part523_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part523) = true := by rfl

def kid11_part524 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 43 1 false (3),
.last 22 (2,true),
.cycle 20 1 false (0),
.cycle 22 1 false (0),
.cycle 0 34 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 34, 2, 64],64⟩,
.last 18 (2,true),
.cycle 1 19 true (0),
.cycle 36 1 false (2),
.cycle 28 1 false (0),
.cycle 19 14 true (3),
.last 19 (2,true),
.cycle 0 40 true (0),
.cycle 37 1 false (3),
.cycle 20 1 false (0),
.cycle 43 1 false (3),
.cycle 1 29 true (0),
.cycle 1 19 true (0),
.last 18 (2,true),
.cycle 1 19 true (0),
.cycle 34 7 true (4),
.cycle 18 18 true (4)
])
theorem kid11_part524_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part524) = true := by rfl

def kid11_part525 : Audit := .cycle 15 1 false (-1)
theorem kid11_part525_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part525) = true := by rfl

def kid11_part526 : Audit := .cycle 12 2 true (1)
theorem kid11_part526_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part526) = true := by rfl

def kid11_part527 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 25 (2,true),
.cycle 13 7 true (3),
.cycle 9 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 1, 32, 64],64⟩,
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2)
])
theorem kid11_part527_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part527) = true := by rfl

def kid11_part528 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.last 19 (2,true),
.cycle 1 19 true (1),
.cycle 10 6 true (2),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 2, 2, 64],64⟩,
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.cycle 7 12 true (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 4 16 true (1),
.cycle 11 4 true (2),
.cycle 7 10 true (2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 15 6 true (5)
])
theorem kid11_part528_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part528) = true := by rfl

def kid11_part529 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 57 1 false (11),
.last 32 (5,true),
.last 17 (5,true),
.cycle 1 17 true (1),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 25 (5,true),
.cycle 1 15 true (1),
.cycle 2 19 true (1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 17 (5,true),
.cycle 12 2 true (2),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.last 14 (5,true)
])
theorem kid11_part529_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part529) = true := by rfl

def kid11_part530 : Audit := .cycle 5 8 true (1)
theorem kid11_part530_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part530) = true := by rfl

def kid11_part531 : Audit := .cycle 14 3 true (4)
theorem kid11_part531_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part531) = true := by rfl

def kid11_part532 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 34 8 true (4),
.last 14 (2,true),
.cycle 1 20 true (1),
.cycle 18 8 true (4),
.cycle 22 1 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 16 6 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 14 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 4 14 true (1),
.cycle 12 2 true (2),
.cycle 12 4 true (1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.cycle 14 6 true (4)
])
theorem kid11_part532_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part532) = true := by rfl

def kid11_part508 : Audit := .split 12 (4,true) (byMove [(kid11_part509),(kid11_part510),(kid11_part511),(kid11_part512),(kid11_part513),(kid11_part514),(kid11_part515),(kid11_part516),(kid11_part517),(kid11_part518),(kid11_part519),(kid11_part520),(kid11_part521),(kid11_part522),(kid11_part523),(kid11_part524),(kid11_part525),(kid11_part526),(kid11_part527),(kid11_part528),(kid11_part529),(kid11_part530),(kid11_part531),(kid11_part532)])

theorem kid11_part508_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part508) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part509),(kid11_part510),(kid11_part511),(kid11_part512),(kid11_part513),(kid11_part514),(kid11_part515),(kid11_part516),(kid11_part517),(kid11_part518),(kid11_part519),(kid11_part520),(kid11_part521),(kid11_part522),(kid11_part523),(kid11_part524),(kid11_part525),(kid11_part526),(kid11_part527),(kid11_part528),(kid11_part529),(kid11_part530),(kid11_part531),(kid11_part532)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part509_checked

  · exact kid11_part515_checked

  · exact kid11_part521_checked

  · exact kid11_part527_checked

  · exact kid11_part510_checked

  · exact kid11_part516_checked

  · exact kid11_part522_checked

  · exact kid11_part528_checked

  · exact kid11_part511_checked

  · exact kid11_part517_checked

  · exact kid11_part523_checked

  · exact kid11_part529_checked

  · exact kid11_part512_checked

  · exact kid11_part518_checked

  · exact kid11_part524_checked

  · exact kid11_part530_checked

  · exact kid11_part513_checked

  · exact kid11_part519_checked

  · exact kid11_part525_checked

  · exact kid11_part531_checked

  · exact kid11_part514_checked

  · exact kid11_part520_checked

  · exact kid11_part526_checked

  · exact kid11_part532_checked

def kid11_part534 : Audit := .cycle 0 12 true (0)
theorem kid11_part534_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part534) = true := by rfl

def kid11_part535 : Audit := .cycle 1 11 true (1)
theorem kid11_part535_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part535) = true := by rfl

def kid11_part536 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 47 1 false (1),
.cycle 2 22 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (2,true),
.cycle 13 7 true (2),
.cycle 9 11 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 32, 16, 128, 256, 8, 128, 32, 16, 4096],[128, 32, 4096, 1, 32, 32, 128, 32, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 38 1 false (0),
.cycle 2 20 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 23 (2,true),
.cycle 2 22 true (1)
])
theorem kid11_part536_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part536) = true := by rfl

def kid11_part537 : Audit := .cycle 3 9 true (1)
theorem kid11_part537_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part537) = true := by rfl

def kid11_part538 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 40 1 false (2),
.last 21 (2,true),
.cycle 19 3 false (-1),
.cycle 24 3 false (0),
.cycle 1 17 true (1),
.cycle 35 3 false (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 23 3 false (1),
.cycle 35 3 false (3),
.cycle 18 14 true (1),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 35 1 false (1),
.cycle 19 3 false (-1),
.cycle 21 3 false (0),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 22 3 false (0),
.cycle 12 7 true (2)
])
theorem kid11_part538_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part538) = true := by rfl

def kid11_part539 : Audit := .cycle 8 4 true (4)
theorem kid11_part539_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part539) = true := by rfl

def kid11_part540 : Audit := .cycle 0 12 true (0)
theorem kid11_part540_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part540) = true := by rfl

def kid11_part541 : Audit := .cycle 1 11 true (1)
theorem kid11_part541_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part541) = true := by rfl

def kid11_part542 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 2 34 true (1),
.last 26 (2,true),
.cycle 0 39 true (0),
.last 26 (2,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.last 23 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 36, 16, 64],[2, 32, 64, 1, 4, 32, 64],64⟩,
.cycle 7 22 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.last 27 (2,true),
.last 24 (2,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.last 23 (2,true),
.cycle 22 14 true (6)
])
theorem kid11_part542_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part542) = true := by rfl

def kid11_part543 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.last 24 (2,true),
.cycle 37 1 false (1),
.cycle 0 25 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 40, 16, 64],[2, 32, 64, 1, 8, 2, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 40, 16, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 7 17 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.cycle 5 29 true (1),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 3 18 true (1),
.cycle 20 11 true (6)
])
theorem kid11_part543_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part543) = true := by rfl

def kid11_part544 : Audit := .cycle 9 3 true (4)
theorem kid11_part544_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part544) = true := by rfl

def kid11_part545 : Audit := .cycle 8 4 true (4)
theorem kid11_part545_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part545) = true := by rfl

def kid11_part546 : Audit := .cycle 7 6 true (3)
theorem kid11_part546_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part546) = true := by rfl

def kid11_part547 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 19 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 19 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 8 6 true (4)
])
theorem kid11_part547_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part547) = true := by rfl

def kid11_part548 : Audit := .cycle 0 14 true (0)
theorem kid11_part548_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part548) = true := by rfl

def kid11_part549 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 40 1 false (0),
.cycle 4 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 12 7 true (2),
.cycle 9 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 34, 32, 64],64⟩,
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 33 1 false (-1),
.cycle 4 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.cycle 4 18 true (1)
])
theorem kid11_part549_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part549) = true := by rfl

def kid11_part550 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 54 1 false (4),
.last 21 (2,true),
.cycle 19 3 false (-1),
.cycle 24 3 false (0),
.cycle 0 20 true (0),
.cycle 49 3 false (9),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 23 3 false (1),
.cycle 49 3 false (9),
.cycle 18 20 true (2),
.last 18 (2,true),
.cycle 0 24 true (0),
.cycle 45 1 false (3),
.cycle 19 3 false (-1),
.cycle 21 3 false (0),
.cycle 0 20 true (0),
.cycle 7 12 true (2),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 22 3 false (0),
.cycle 17 8 true (3)
])
theorem kid11_part550_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part550) = true := by rfl

def kid11_part551 : Audit := .cycle 10 2 true (4)
theorem kid11_part551_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part551) = true := by rfl

def kid11_part552 : Audit := .cycle 0 12 true (0)
theorem kid11_part552_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part552) = true := by rfl

def kid11_part553 : Audit := .cycle 1 11 true (1)
theorem kid11_part553_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part553) = true := by rfl

def kid11_part554 : Audit := .cycle 2 10 true (1)
theorem kid11_part554_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part554) = true := by rfl

def kid11_part555 : Audit := .cycle 1 14 true (1)
theorem kid11_part555_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part555) = true := by rfl

def kid11_part556 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 27 true (1),
.cycle 10 9 true (2),
.cycle 21 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (5),
.cycle 8 7 true (4),
.cycle 7 11 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 4 21 true (1),
.cycle 16 5 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (5),
.cycle 8 7 true (4)
])
theorem kid11_part556_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part556) = true := by rfl

def kid11_part557 : Audit := .cycle 8 4 true (4)
theorem kid11_part557_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part557) = true := by rfl

def kid11_part533 : Audit := .split 11 (4,true) (byMove [(kid11_part534),(kid11_part535),(kid11_part536),(kid11_part537),(kid11_part538),(kid11_part539),(kid11_part540),(kid11_part541),(kid11_part542),(kid11_part543),(kid11_part544),(kid11_part545),(kid11_part546),(kid11_part547),(kid11_part548),(kid11_part549),(kid11_part550),(kid11_part551),(kid11_part552),(kid11_part553),(kid11_part554),(kid11_part555),(kid11_part556),(kid11_part557)])

theorem kid11_part533_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part533) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some mv)) (byMove [(kid11_part534),(kid11_part535),(kid11_part536),(kid11_part537),(kid11_part538),(kid11_part539),(kid11_part540),(kid11_part541),(kid11_part542),(kid11_part543),(kid11_part544),(kid11_part545),(kid11_part546),(kid11_part547),(kid11_part548),(kid11_part549),(kid11_part550),(kid11_part551),(kid11_part552),(kid11_part553),(kid11_part554),(kid11_part555),(kid11_part556),(kid11_part557)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part534_checked

  · exact kid11_part540_checked

  · exact kid11_part546_checked

  · exact kid11_part552_checked

  · exact kid11_part535_checked

  · exact kid11_part541_checked

  · exact kid11_part547_checked

  · exact kid11_part553_checked

  · exact kid11_part536_checked

  · exact kid11_part542_checked

  · exact kid11_part548_checked

  · exact kid11_part554_checked

  · exact kid11_part537_checked

  · exact kid11_part543_checked

  · exact kid11_part549_checked

  · exact kid11_part555_checked

  · exact kid11_part538_checked

  · exact kid11_part544_checked

  · exact kid11_part550_checked

  · exact kid11_part556_checked

  · exact kid11_part539_checked

  · exact kid11_part545_checked

  · exact kid11_part551_checked

  · exact kid11_part557_checked

def kid11_part558 : Audit := .cycle 0 10 true (0)
theorem kid11_part558_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part558) = true := by rfl

def kid11_part559 : Audit := .cycle 1 9 true (1)
theorem kid11_part559_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part559) = true := by rfl

def kid11_part560 : Audit := .cycle 2 8 true (1)
theorem kid11_part560_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part560) = true := by rfl

def kid11_part561 : Audit := .cycle 1 12 true (1)
theorem kid11_part561_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part561) = true := by rfl

def kid11_part562 : Audit := .cycle 9 1 true (5)
theorem kid11_part562_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part562) = true := by rfl

def kid11_part563 : Audit := .cycle 8 2 true (4)
theorem kid11_part563_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part563) = true := by rfl

def kid11_part419 : Audit := .split 9 (4,false) (byMove [(kid11_part420),(kid11_part421),(kid11_part422),(kid11_part423),(kid11_part424),(kid11_part425),(kid11_part426),(kid11_part427),(kid11_part428),(kid11_part453),(kid11_part478),(kid11_part479),(kid11_part480),(kid11_part481),(kid11_part506),(kid11_part507),(kid11_part508),(kid11_part533),(kid11_part558),(kid11_part559),(kid11_part560),(kid11_part561),(kid11_part562),(kid11_part563)])

theorem kid11_part419_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (kid11_part419) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part420),(kid11_part421),(kid11_part422),(kid11_part423),(kid11_part424),(kid11_part425),(kid11_part426),(kid11_part427),(kid11_part428),(kid11_part453),(kid11_part478),(kid11_part479),(kid11_part480),(kid11_part481),(kid11_part506),(kid11_part507),(kid11_part508),(kid11_part533),(kid11_part558),(kid11_part559),(kid11_part560),(kid11_part561),(kid11_part562),(kid11_part563)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part420_checked

  · exact kid11_part426_checked

  · exact kid11_part480_checked

  · exact kid11_part558_checked

  · exact kid11_part421_checked

  · exact kid11_part427_checked

  · exact kid11_part481_checked

  · exact kid11_part559_checked

  · exact kid11_part422_checked

  · exact kid11_part428_checked

  · exact kid11_part506_checked

  · exact kid11_part560_checked

  · exact kid11_part423_checked

  · exact kid11_part453_checked

  · exact kid11_part507_checked

  · exact kid11_part561_checked

  · exact kid11_part424_checked

  · exact kid11_part478_checked

  · exact kid11_part508_checked

  · exact kid11_part562_checked

  · exact kid11_part425_checked

  · exact kid11_part479_checked

  · exact kid11_part533_checked

  · exact kid11_part563_checked

def kid11_part564 : Audit := .cycle 8 1 true (4)
theorem kid11_part564_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨false,true,5⟩)) (kid11_part564) = true := by rfl

def kid11_part565 : Audit := .cycle 7 3 true (3)
theorem kid11_part565_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (kid11_part565) = true := by rfl

def kid11_part567 : Audit := .cycle 1 11 true (1)
theorem kid11_part567_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part567) = true := by rfl

def kid11_part568 : Audit := .cycle 7 4 true (3)
theorem kid11_part568_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part568) = true := by rfl

def kid11_part569 : Audit := .cycle 25 1 false (1)
theorem kid11_part569_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part569) = true := by rfl

def kid11_part570 : Audit := .cycle 0 12 true (0)
theorem kid11_part570_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part570) = true := by rfl

def kid11_part572 : Audit := .cycle 1 12 true (1)
theorem kid11_part572_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part572) = true := by rfl

def kid11_part573 : Audit := .cycle 1 16 true (1)
theorem kid11_part573_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part573) = true := by rfl

def kid11_part574 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 25 1 false (-1),
.cycle 15 8 false (2),
.last 15 (5,true),
.cycle 0 28 true (-2),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.last 16 (5,true)
])
theorem kid11_part574_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part574) = true := by rfl

def kid11_part575 : Audit := .cycle 0 13 true (0)
theorem kid11_part575_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part575) = true := by rfl

def kid11_part576 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 18 13 false (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 18 5 false (0),
.cycle 15 8 false (2),
.last 15 (5,true),
.cycle 0 28 true (-2),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.last 16 (5,true)
])
theorem kid11_part576_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part576) = true := by rfl

def kid11_part577 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,false),
.cycle 12 7 true (0),
.last 13 (4,false),
.cycle 20 4 false (2),
.cycle 21 7 false (2),
.cycle 17 4 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 3 true (2)
])
theorem kid11_part577_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part577) = true := by rfl

def kid11_part578 : Audit := .cycle 0 12 true (0)
theorem kid11_part578_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part578) = true := by rfl

def kid11_part579 : Audit := .cycle 1 11 true (1)
theorem kid11_part579_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part579) = true := by rfl

def kid11_part580 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 44 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 30 (4,false),
.cycle 13 7 true (2),
.last 20 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 8, 128, 256, 8, 128, 4096, 32, 4096],[128, 32, 4096, 1, 4, 32, 128, 32, 8, 1, 4, 32, 4096],5136⟩,
.cycle 7 14 true (2),
.cycle 9 11 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 20 (4,false),
.cycle 1 29 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 18 3 true (4)
])
theorem kid11_part580_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part580) = true := by rfl

def kid11_part581 : Audit := .cycle 3 9 true (1)
theorem kid11_part581_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part581) = true := by rfl

def kid11_part582 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 28 1 false (6),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 15 (5,true)
])
theorem kid11_part582_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part582) = true := by rfl

def kid11_part583 : Audit := .cycle 8 4 true (3)
theorem kid11_part583_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part583) = true := by rfl

def kid11_part584 : Audit := .cycle 6 6 true (2)
theorem kid11_part584_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part584) = true := by rfl

def kid11_part585 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 21 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (4,false),
.cycle 0 23 true (0),
.last 14 (4,false),
.cycle 27 3 false (2),
.cycle 7 8 true (2),
.cycle 22 3 false (1),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.last 14 (4,false),
.cycle 21 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 12 3 true (2)
])
theorem kid11_part585_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part585) = true := by rfl

def kid11_part586 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (0),
.last 34 (5,true),
.cycle 17 1 false (-1),
.cycle 21 1 false (-1),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 7 8 true (1),
.cycle 0 19 true (0),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 0 18 true (0),
.cycle 14 14 true (-2),
.cycle 15 8 false (2),
.last 15 (5,true),
.cycle 14 10 true (-2),
.cycle 21 1 false (-1),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 20 18 true (-2),
.cycle 24 5 false (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 16 14 true (-2),
.last 16 (5,true)
])
theorem kid11_part586_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part586) = true := by rfl

def kid11_part587 : Audit := .cycle 1 13 true (1)
theorem kid11_part587_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part587) = true := by rfl

def kid11_part588 : Audit := .split 13 (4,false) (byMove [
.cycle 15 6 false (2),
.last 25 (5,true),
.cycle 17 1 false (-1),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (1),
.last 15 (5,true),
.cycle 0 18 true (0),
.cycle 1 15 true (1),
.cycle 12 2 true (1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 26 (5,true),
.last 15 (5,true),
.cycle 16 3 false (0),
.cycle 1 15 true (1),
.cycle 15 3 false (1),
.last 14 (5,true)
])
theorem kid11_part588_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part588) = true := by rfl

def kid11_part589 : Audit := .split 12 (5,true) (byMove [
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.cycle 20 1 false (0),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 1 13 true (1),
.cycle 24 4 false (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 19 4 false (1),
.cycle 24 4 false (2),
.cycle 14 10 true (1),
.cycle 17 4 false (0),
.cycle 1 15 true (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 18 4 false (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 13 3 true (3)
])
theorem kid11_part589_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part589) = true := by rfl

def kid11_part590 : Audit := .cycle 0 12 true (0)
theorem kid11_part590_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part590) = true := by rfl

def kid11_part591 : Audit := .cycle 1 11 true (1)
theorem kid11_part591_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part591) = true := by rfl

def kid11_part592 : Audit := .cycle 2 10 true (1)
theorem kid11_part592_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part592) = true := by rfl

def kid11_part593 : Audit := .cycle 1 14 true (1)
theorem kid11_part593_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part593) = true := by rfl

def kid11_part594 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 21 1 false (-1),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 38 (5,true),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 15 (5,true)
])
theorem kid11_part594_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part594) = true := by rfl

def kid11_part595 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 25 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (4,false),
.cycle 13 7 true (2),
.last 15 (4,false),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 25 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 12 3 true (3)
])
theorem kid11_part595_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part595) = true := by rfl

def kid11_part571 : Audit := .split 11 (4,true) (byMove [(kid11_part572),(kid11_part573),(kid11_part574),(kid11_part575),(kid11_part576),(kid11_part577),(kid11_part578),(kid11_part579),(kid11_part580),(kid11_part581),(kid11_part582),(kid11_part583),(kid11_part584),(kid11_part585),(kid11_part586),(kid11_part587),(kid11_part588),(kid11_part589),(kid11_part590),(kid11_part591),(kid11_part592),(kid11_part593),(kid11_part594),(kid11_part595)])

theorem kid11_part571_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part571) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part572),(kid11_part573),(kid11_part574),(kid11_part575),(kid11_part576),(kid11_part577),(kid11_part578),(kid11_part579),(kid11_part580),(kid11_part581),(kid11_part582),(kid11_part583),(kid11_part584),(kid11_part585),(kid11_part586),(kid11_part587),(kid11_part588),(kid11_part589),(kid11_part590),(kid11_part591),(kid11_part592),(kid11_part593),(kid11_part594),(kid11_part595)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part572_checked

  · exact kid11_part578_checked

  · exact kid11_part584_checked

  · exact kid11_part590_checked

  · exact kid11_part573_checked

  · exact kid11_part579_checked

  · exact kid11_part585_checked

  · exact kid11_part591_checked

  · exact kid11_part574_checked

  · exact kid11_part580_checked

  · exact kid11_part586_checked

  · exact kid11_part592_checked

  · exact kid11_part575_checked

  · exact kid11_part581_checked

  · exact kid11_part587_checked

  · exact kid11_part593_checked

  · exact kid11_part576_checked

  · exact kid11_part582_checked

  · exact kid11_part588_checked

  · exact kid11_part594_checked

  · exact kid11_part577_checked

  · exact kid11_part583_checked

  · exact kid11_part589_checked

  · exact kid11_part595_checked

def kid11_part596 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,false),
.last 20 (4,false),
.last 13 (4,false),
.last 17 (4,false),
.cycle 21 7 false (2),
.last 20 (4,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 22 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 29 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.last 29 (4,true),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 4 true (3)
]),
.cycle 8 4 true (3),
.cycle 6 6 true (2),
.cycle 21 3 false (1),
.cycle 21 11 false (4),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.last 20 (4,false),
.cycle 20 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 1 13 true (1),
.last 18 (4,false),
.last 24 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.last 16 (4,false),
.last 20 (4,false),
.cycle 1 15 true (1),
.last 18 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 11 2 true (2)
]),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 19 6 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 9 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 19 6 false (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 4 true (3)
]),
.cycle 11 3 true (3)
])
theorem kid11_part596_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part596) = true := by rfl

def kid11_part597 : Audit := .cycle 0 11 true (0)
theorem kid11_part597_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part597) = true := by rfl

def kid11_part598 : Audit := .cycle 1 10 true (1)
theorem kid11_part598_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part598) = true := by rfl

def kid11_part599 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 45 1 false (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 22 14 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 19 1 true (5),
.cycle 8 12 true (3),
.cycle 6 14 true (2),
.cycle 9 14 true (3),
.cycle 1 37 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 20 26 true (-3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (5),
.cycle 17 4 true (5)
]),
.cycle 8 14 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 12 7 true (3),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.last 22 (4,true),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 30 (4,true),
.last 28 (4,true),
.cycle 19 1 true (7),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.cycle 13 7 true (3),
.last 22 (4,true),
.last 33 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 17 4 true (5)
]),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.split 19 (4,false) (byMove [
.cycle 9 12 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 165, 8, 4, 128, 256, 8, 128, 4, 5, 4096],[128, 32, 4, 1, 4096, 5, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 23 true (0),
.cycle 7 15 true (3),
.last 20 (4,true),
.cycle 0 39 true (-3),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 18 2 true (5),
.cycle 16 4 true (4),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 68 1 false (12),
.cycle 5 15 true (1),
.last 20 (4,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 1048612, 1048580, 1048580, 8192, 16384, 8, 128, 1048580, 1048580, 33554432, 67108864, 2097152, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 1048612, 68157444, 67108864, 33554432, 67108864, 134217728, 1712324612, 1141899268, 1141899268, 1073741824],[128, 32, 4, 1, 1073741824, 1048580, 8192, 32, 4, 1, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1141899268, 33554432, 536870912, 67108864, 16777216, 1073741824, 1141899268, 1073741824],2144153664⟩,
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 10 10 true (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 30 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (3),
.cycle 6 14 true (2),
.cycle 17 3 true (5),
.last 32 (4,true),
.cycle 1 21 true (1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 17 4 true (5)
]),
.cycle 17 3 true (5)
])
theorem kid11_part599_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part599) = true := by rfl

def kid11_part600 : Audit := .cycle 3 8 true (1)
theorem kid11_part600_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part600) = true := by rfl

def kid11_part602 : Audit := .cycle 0 12 true (0)
theorem kid11_part602_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part602) = true := by rfl

def kid11_part603 : Audit := .cycle 1 11 true (1)
theorem kid11_part603_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part603) = true := by rfl

def kid11_part604 : Audit := .cycle 2 10 true (1)
theorem kid11_part604_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part604) = true := by rfl

def kid11_part605 : Audit := .cycle 1 14 true (1)
theorem kid11_part605_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part605) = true := by rfl

def kid11_part606 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 0 18 true (0),
.cycle 1 15 true (1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (3),
.last 16 (5,true)
])
theorem kid11_part606_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part606) = true := by rfl

def kid11_part607 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 18 8 false (0),
.cycle 25 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 44 (4,true),
.cycle 13 7 true (2),
.cycle 8 8 true (3),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 18 8 false (0),
.last 21 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 2 true (4),
.cycle 12 3 true (3)
])
theorem kid11_part607_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part607) = true := by rfl

def kid11_part608 : Audit := .cycle 0 12 true (0)
theorem kid11_part608_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part608) = true := by rfl

def kid11_part609 : Audit := .cycle 1 11 true (1)
theorem kid11_part609_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part609) = true := by rfl

def kid11_part610 : Audit := .split 20 (5,true) (byMove [
.cycle 9 13 true (3),
.cycle 0 24 true (0),
.cycle 2 26 true (1),
.cycle 9 15 true (3),
.cycle 0 24 true (0),
.cycle 0 30 true (0),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 35 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 14 true (3),
.cycle 7 18 true (3),
.last 23 (4,true),
.cycle 1 23 true (1),
.cycle 4 22 true (1),
.last 23 (4,true),
.last 27 (4,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 10 11 true (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 21 3 true (7)
])
theorem kid11_part610_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part610) = true := by rfl

def kid11_part611 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 8 14 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 40 (4,true),
.cycle 12 7 true (3),
.last 28 (4,true),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 0 21 true (0),
.last 25 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 17 3 true (5)
])
theorem kid11_part611_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part611) = true := by rfl

def kid11_part612 : Audit := .cycle 11 1 true (5)
theorem kid11_part612_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part612) = true := by rfl

def kid11_part613 : Audit := .cycle 8 4 true (3)
theorem kid11_part613_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part613) = true := by rfl

def kid11_part614 : Audit := .cycle 7 6 true (3)
theorem kid11_part614_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part614) = true := by rfl

def kid11_part615 : Audit := .cycle 9 3 true (3)
theorem kid11_part615_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part615) = true := by rfl

def kid11_part616 : Audit := .cycle 0 14 true (0)
theorem kid11_part616_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part616) = true := by rfl

def kid11_part617 : Audit := .cycle 4 8 true (1)
theorem kid11_part617_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part617) = true := by rfl

def kid11_part618 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 20 1 false (0),
.last 17 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 25 (5,true),
.cycle 1 15 true (1),
.cycle 40 1 false (8),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 5 12 true (1),
.last 17 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.last 14 (5,true)
])
theorem kid11_part618_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part618) = true := by rfl

def kid11_part619 : Audit := .split 14 (5,true) (byMove [
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.cycle 9 9 true (2),
.last 23 (4,true),
.cycle 25 7 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 20 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 8 8 true (3),
.cycle 7 12 true (3),
.last 17 (4,true),
.cycle 1 17 true (1),
.cycle 4 16 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (3),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 15 3 true (5)
])
theorem kid11_part619_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part619) = true := by rfl

def kid11_part620 : Audit := .cycle 0 12 true (0)
theorem kid11_part620_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part620) = true := by rfl

def kid11_part621 : Audit := .cycle 1 11 true (1)
theorem kid11_part621_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part621) = true := by rfl

def kid11_part622 : Audit := .cycle 2 10 true (1)
theorem kid11_part622_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part622) = true := by rfl

def kid11_part623 : Audit := .cycle 1 14 true (1)
theorem kid11_part623_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part623) = true := by rfl

def kid11_part624 : Audit := .cycle 11 1 true (5)
theorem kid11_part624_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part624) = true := by rfl

def kid11_part625 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 21 true (1),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 26 (4,true),
.cycle 0 24 true (0),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 17 true (1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid11_part625_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part625) = true := by rfl

def kid11_part601 : Audit := .split 11 (4,false) (byMove [(kid11_part602),(kid11_part603),(kid11_part604),(kid11_part605),(kid11_part606),(kid11_part607),(kid11_part608),(kid11_part609),(kid11_part610),(kid11_part611),(kid11_part612),(kid11_part613),(kid11_part614),(kid11_part615),(kid11_part616),(kid11_part617),(kid11_part618),(kid11_part619),(kid11_part620),(kid11_part621),(kid11_part622),(kid11_part623),(kid11_part624),(kid11_part625)])

theorem kid11_part601_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part601) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part602),(kid11_part603),(kid11_part604),(kid11_part605),(kid11_part606),(kid11_part607),(kid11_part608),(kid11_part609),(kid11_part610),(kid11_part611),(kid11_part612),(kid11_part613),(kid11_part614),(kid11_part615),(kid11_part616),(kid11_part617),(kid11_part618),(kid11_part619),(kid11_part620),(kid11_part621),(kid11_part622),(kid11_part623),(kid11_part624),(kid11_part625)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part602_checked

  · exact kid11_part608_checked

  · exact kid11_part614_checked

  · exact kid11_part620_checked

  · exact kid11_part603_checked

  · exact kid11_part609_checked

  · exact kid11_part615_checked

  · exact kid11_part621_checked

  · exact kid11_part604_checked

  · exact kid11_part610_checked

  · exact kid11_part616_checked

  · exact kid11_part622_checked

  · exact kid11_part605_checked

  · exact kid11_part611_checked

  · exact kid11_part617_checked

  · exact kid11_part623_checked

  · exact kid11_part606_checked

  · exact kid11_part612_checked

  · exact kid11_part618_checked

  · exact kid11_part624_checked

  · exact kid11_part607_checked

  · exact kid11_part613_checked

  · exact kid11_part619_checked

  · exact kid11_part625_checked

def kid11_part626 : Audit := .cycle 8 3 true (3)
theorem kid11_part626_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part626) = true := by rfl

def kid11_part627 : Audit := .cycle 6 5 true (2)
theorem kid11_part627_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part627) = true := by rfl

def kid11_part628 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.cycle 27 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 16 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.cycle 22 5 false (1),
.cycle 15 16 true (-2),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 16 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 11 4 true (3)
]),
.cycle 22 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 11 7 true (2),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (2),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (4,true),
.last 22 (4,true),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 11 7 true (2),
.last 16 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 4 true (3)
]),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.split 13 (4,false) (byMove [
.cycle 9 6 true (2),
.cycle 1 24 true (1),
.cycle 27 1 false (-1),
.cycle 7 9 true (2),
.last 14 (4,true),
.cycle 16 6 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (3),
.cycle 11 4 true (2),
.cycle 22 5 false (1),
.cycle 17 12 true (-2),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 16 6 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 22 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.last 19 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 4 true (3)
]),
.cycle 11 3 true (3)
])
theorem kid11_part628_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part628) = true := by rfl

def kid11_part629 : Audit := .cycle 5 9 true (1)
theorem kid11_part629_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part629) = true := by rfl

def kid11_part630 : Audit := .cycle 1 12 true (1)
theorem kid11_part630_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part630) = true := by rfl

def kid11_part632 : Audit := .cycle 9 4 true (2)
theorem kid11_part632_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part632) = true := by rfl

def kid11_part633 : Audit := .cycle 1 20 true (1)
theorem kid11_part633_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part633) = true := by rfl

def kid11_part634 : Audit := .split 13 (4,false) (byMove [
.cycle 15 6 false (2),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.cycle 23 1 false (-1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 9 6 true (1),
.last 25 (5,true),
.cycle 12 2 true (1),
.cycle 7 9 true (1),
.cycle 29 1 false (1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.cycle 23 1 false (-1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 29 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 7 9 true (1),
.cycle 18 1 false (0),
.last 14 (5,true)
])
theorem kid11_part634_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part634) = true := by rfl

def kid11_part635 : Audit := .cycle 7 7 true (2)
theorem kid11_part635_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part635) = true := by rfl

def kid11_part636 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.last 27 (5,true),
.cycle 17 1 false (-1),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 17 1 true (3),
.cycle 18 5 false (0),
.cycle 15 8 false (2),
.last 15 (5,true),
.cycle 21 8 true (-2),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 30 (5,true),
.cycle 0 17 true (0),
.last 20 (5,true),
.cycle 9 8 true (1),
.cycle 21 1 true (-1),
.last 16 (5,true)
])
theorem kid11_part636_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part636) = true := by rfl

def kid11_part637 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 7 7 true (2),
.cycle 21 4 false (2),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.last 13 (4,false),
.cycle 20 4 false (2),
.cycle 21 7 false (2),
.cycle 17 4 false (0),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 7 7 true (2),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 16 3 true (4)
])
theorem kid11_part637_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part637) = true := by rfl

def kid11_part638 : Audit := .cycle 1 12 true (1)
theorem kid11_part638_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part638) = true := by rfl

def kid11_part639 : Audit := .cycle 7 5 true (3)
theorem kid11_part639_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part639) = true := by rfl

def kid11_part640 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 true (2),
.cycle 1 24 true (1),
.cycle 19 1 false (-1),
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 23 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 22 (5,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.last 22 (5,true),
.last 14 (5,true)
])
theorem kid11_part640_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part640) = true := by rfl

def kid11_part641 : Audit := .cycle 0 13 true (0)
theorem kid11_part641_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part641) = true := by rfl

def kid11_part642 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 33 1 false (7),
.cycle 11 7 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.last 16 (5,true)
])
theorem kid11_part642_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part642) = true := by rfl

def kid11_part643 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 23 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,false),
.cycle 12 7 true (2),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 23 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 3 true (4)
])
theorem kid11_part643_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part643) = true := by rfl

def kid11_part644 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 23 10 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (4,false),
.cycle 12 7 true (2),
.last 15 (4,false),
.cycle 13 7 true (3),
.cycle 7 9 true (2),
.cycle 9 6 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 23 10 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 13 3 true (3)
])
theorem kid11_part644_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part644) = true := by rfl

def kid11_part645 : Audit := .split 13 (5,true) (byMove [
.cycle 9 6 true (2),
.cycle 0 17 true (0),
.cycle 42 1 false (4),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 21 3 false (0),
.cycle 1 14 true (1),
.cycle 49 3 false (10),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 26 3 false (2),
.cycle 35 3 false (6),
.cycle 7 11 true (2),
.cycle 22 3 false (1),
.cycle 1 16 true (1),
.cycle 35 1 false (3),
.last 14 (4,false),
.cycle 21 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 24 3 false (2),
.cycle 0 15 true (0),
.last 17 (4,false),
.cycle 14 3 true (4)
])
theorem kid11_part645_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part645) = true := by rfl

def kid11_part646 : Audit := .split 13 (4,false) (byMove [
.cycle 15 6 false (2),
.last 23 (5,true),
.cycle 17 1 false (-1),
.last 17 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 12 2 true (1),
.cycle 5 9 true (1),
.cycle 5 11 true (1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 24 (5,true),
.cycle 5 9 true (1),
.last 21 (5,true),
.last 14 (5,true)
])
theorem kid11_part646_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part646) = true := by rfl

def kid11_part647 : Audit := .cycle 5 7 true (1)
theorem kid11_part647_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part647) = true := by rfl

def kid11_part648 : Audit := .split 13 (4,false) (byMove [
.cycle 15 6 false (2),
.last 25 (5,true),
.cycle 17 1 false (-1),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 13 2 true (1),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 16 3 false (0),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.last 14 (5,true)
])
theorem kid11_part648_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part648) = true := by rfl

def kid11_part649 : Audit := .split 12 (5,true) (byMove [
.cycle 19 5 false (2),
.cycle 1 16 true (1),
.cycle 39 1 false (3),
.cycle 20 1 false (0),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.last 14 (4,false),
.cycle 1 14 true (1),
.cycle 19 4 false (1),
.cycle 30 4 false (6),
.cycle 14 13 true (2),
.cycle 17 4 false (0),
.cycle 5 9 true (1),
.cycle 32 1 false (2),
.last 13 (4,false),
.cycle 16 4 false (0),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 18 4 false (2),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 14 3 true (4)
])
theorem kid11_part649_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part649) = true := by rfl

def kid11_part650 : Audit := .cycle 1 12 true (1)
theorem kid11_part650_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part650) = true := by rfl

def kid11_part651 : Audit := .cycle 7 5 true (3)
theorem kid11_part651_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part651) = true := by rfl

def kid11_part652 : Audit := .cycle 10 2 true (3)
theorem kid11_part652_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part652) = true := by rfl

def kid11_part653 : Audit := .cycle 0 13 true (0)
theorem kid11_part653_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part653) = true := by rfl

def kid11_part654 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 11 5 true (3),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.last 16 (5,true)
])
theorem kid11_part654_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part654) = true := by rfl

def kid11_part655 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 17 (4,false),
.cycle 0 14 true (0),
.last 17 (4,false),
.cycle 17 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 9 6 true (3),
.last 17 (4,false),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 17 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 3 true (4)
])
theorem kid11_part655_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part655) = true := by rfl

def kid11_part631 : Audit := .split 11 (4,true) (byMove [(kid11_part632),(kid11_part633),(kid11_part634),(kid11_part635),(kid11_part636),(kid11_part637),(kid11_part638),(kid11_part639),(kid11_part640),(kid11_part641),(kid11_part642),(kid11_part643),(kid11_part644),(kid11_part645),(kid11_part646),(kid11_part647),(kid11_part648),(kid11_part649),(kid11_part650),(kid11_part651),(kid11_part652),(kid11_part653),(kid11_part654),(kid11_part655)])

theorem kid11_part631_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part631) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part632),(kid11_part633),(kid11_part634),(kid11_part635),(kid11_part636),(kid11_part637),(kid11_part638),(kid11_part639),(kid11_part640),(kid11_part641),(kid11_part642),(kid11_part643),(kid11_part644),(kid11_part645),(kid11_part646),(kid11_part647),(kid11_part648),(kid11_part649),(kid11_part650),(kid11_part651),(kid11_part652),(kid11_part653),(kid11_part654),(kid11_part655)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part632_checked

  · exact kid11_part638_checked

  · exact kid11_part644_checked

  · exact kid11_part650_checked

  · exact kid11_part633_checked

  · exact kid11_part639_checked

  · exact kid11_part645_checked

  · exact kid11_part651_checked

  · exact kid11_part634_checked

  · exact kid11_part640_checked

  · exact kid11_part646_checked

  · exact kid11_part652_checked

  · exact kid11_part635_checked

  · exact kid11_part641_checked

  · exact kid11_part647_checked

  · exact kid11_part653_checked

  · exact kid11_part636_checked

  · exact kid11_part642_checked

  · exact kid11_part648_checked

  · exact kid11_part654_checked

  · exact kid11_part637_checked

  · exact kid11_part643_checked

  · exact kid11_part649_checked

  · exact kid11_part655_checked

def kid11_part656 : Audit := .split 11 (5,true) (byMove [
.cycle 9 4 true (2),
.cycle 1 20 true (1),
.cycle 17 1 false (1),
.cycle 7 7 true (2),
.split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.last 21 (4,false),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 7 7 true (2),
.last 16 (4,false),
.cycle 0 15 true (0),
.last 20 (4,false),
.last 13 (4,false),
.last 17 (4,false),
.cycle 21 7 false (2),
.last 20 (4,false),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 7 7 true (2),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 15 4 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 29 5 false (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 32 6 true (6),
.last 20 (4,false),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 29 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 8 5 true (3),
.cycle 7 9 true (2),
.cycle 21 3 false (1),
.cycle 0 23 true (0),
.cycle 5 7 true (1),
.split 12 (4,true) (byMove [
.cycle 19 5 false (2),
.cycle 1 16 true (1),
.last 20 (4,false),
.cycle 20 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 7 true (2),
.last 15 (4,false),
.last 24 (4,false),
.cycle 1 14 true (1),
.last 15 (4,false),
.last 14 (4,false),
.last 16 (4,false),
.last 20 (4,false),
.cycle 5 9 true (1),
.last 18 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 7 true (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 11 2 true (2)
]),
.cycle 15 4 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 19 6 false (2),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 19 6 false (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 12 3 true (4)
])
theorem kid11_part656_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part656) = true := by rfl

def kid11_part657 : Audit := .cycle 0 11 true (0)
theorem kid11_part657_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part657) = true := by rfl

def kid11_part658 : Audit := .cycle 1 10 true (1)
theorem kid11_part658_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part658) = true := by rfl

def kid11_part659 : Audit := .cycle 2 9 true (1)
theorem kid11_part659_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part659) = true := by rfl

def kid11_part660 : Audit := .cycle 1 13 true (1)
theorem kid11_part660_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part660) = true := by rfl

def kid11_part662 : Audit := .cycle 1 12 true (1)
theorem kid11_part662_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part662) = true := by rfl

def kid11_part663 : Audit := .cycle 7 5 true (3)
theorem kid11_part663_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part663) = true := by rfl

def kid11_part664 : Audit := .cycle 10 2 true (4)
theorem kid11_part664_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part664) = true := by rfl

def kid11_part665 : Audit := .cycle 0 13 true (0)
theorem kid11_part665_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part665) = true := by rfl

def kid11_part666 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 37 1 false (1),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 23 1 false (1),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 1 14 true (1),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.last 15 (5,true)
])
theorem kid11_part666_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part666) = true := by rfl

def kid11_part667 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 37 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 44 (4,true),
.cycle 3 10 true (1),
.cycle 8 10 true (3),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 9 6 true (3),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 21 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part667_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part667) = true := by rfl

def kid11_part668 : Audit := .cycle 0 12 true (0)
theorem kid11_part668_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part668) = true := by rfl

def kid11_part669 : Audit := .cycle 1 11 true (1)
theorem kid11_part669_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part669) = true := by rfl

def kid11_part670 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.cycle 8 15 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 19 true (4),
.cycle 13 7 true (4),
.last 31 (4,true),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 10 11 true (4),
.last 26 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.cycle 18 3 true (6)
])
theorem kid11_part670_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part670) = true := by rfl

def kid11_part671 : Audit := .cycle 3 9 true (1)
theorem kid11_part671_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part671) = true := by rfl

def kid11_part672 : Audit := .cycle 11 1 true (5)
theorem kid11_part672_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part672) = true := by rfl

def kid11_part673 : Audit := .cycle 8 4 true (3)
theorem kid11_part673_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part673) = true := by rfl

def kid11_part674 : Audit := .cycle 6 6 true (2)
theorem kid11_part674_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part674) = true := by rfl

def kid11_part675 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 26 9 false (2),
.cycle 27 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 39 (4,true),
.cycle 12 7 true (3),
.cycle 9 6 true (3),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part675_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part675) = true := by rfl

def kid11_part676 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 0 24 true (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 12 2 true (4),
.cycle 1 15 true (1),
.last 26 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.last 16 (5,true)
])
theorem kid11_part676_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part676) = true := by rfl

def kid11_part677 : Audit := .cycle 1 13 true (1)
theorem kid11_part677_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part677) = true := by rfl

def kid11_part678 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 true (3),
.cycle 7 11 true (3),
.last 25 (5,true),
.cycle 7 8 true (3),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 49 1 false (9),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 5 8 true (1),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.last 13 (5,true)
])
theorem kid11_part678_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part678) = true := by rfl

def kid11_part679 : Audit := .split 12 (5,true) (byMove [
.cycle 9 5 true (3),
.last 17 (4,true),
.cycle 58 1 false (4),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 17 6 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (3),
.cycle 7 10 true (3),
.last 17 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 21 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 13 3 true (5)
])
theorem kid11_part679_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part679) = true := by rfl

def kid11_part680 : Audit := .cycle 0 12 true (0)
theorem kid11_part680_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part680) = true := by rfl

def kid11_part681 : Audit := .cycle 1 11 true (1)
theorem kid11_part681_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part681) = true := by rfl

def kid11_part682 : Audit := .cycle 2 10 true (1)
theorem kid11_part682_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part682) = true := by rfl

def kid11_part683 : Audit := .cycle 1 14 true (1)
theorem kid11_part683_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part683) = true := by rfl

def kid11_part684 : Audit := .cycle 11 1 true (5)
theorem kid11_part684_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part684) = true := by rfl

def kid11_part685 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 31 13 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 14 true (4),
.cycle 13 7 true (4),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 17 (4,true),
.last 27 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid11_part685_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part685) = true := by rfl

def kid11_part661 : Audit := .split 11 (4,false) (byMove [(kid11_part662),(kid11_part663),(kid11_part664),(kid11_part665),(kid11_part666),(kid11_part667),(kid11_part668),(kid11_part669),(kid11_part670),(kid11_part671),(kid11_part672),(kid11_part673),(kid11_part674),(kid11_part675),(kid11_part676),(kid11_part677),(kid11_part678),(kid11_part679),(kid11_part680),(kid11_part681),(kid11_part682),(kid11_part683),(kid11_part684),(kid11_part685)])

theorem kid11_part661_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part661) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part662),(kid11_part663),(kid11_part664),(kid11_part665),(kid11_part666),(kid11_part667),(kid11_part668),(kid11_part669),(kid11_part670),(kid11_part671),(kid11_part672),(kid11_part673),(kid11_part674),(kid11_part675),(kid11_part676),(kid11_part677),(kid11_part678),(kid11_part679),(kid11_part680),(kid11_part681),(kid11_part682),(kid11_part683),(kid11_part684),(kid11_part685)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part662_checked

  · exact kid11_part668_checked

  · exact kid11_part674_checked

  · exact kid11_part680_checked

  · exact kid11_part663_checked

  · exact kid11_part669_checked

  · exact kid11_part675_checked

  · exact kid11_part681_checked

  · exact kid11_part664_checked

  · exact kid11_part670_checked

  · exact kid11_part676_checked

  · exact kid11_part682_checked

  · exact kid11_part665_checked

  · exact kid11_part671_checked

  · exact kid11_part677_checked

  · exact kid11_part683_checked

  · exact kid11_part666_checked

  · exact kid11_part672_checked

  · exact kid11_part678_checked

  · exact kid11_part684_checked

  · exact kid11_part667_checked

  · exact kid11_part673_checked

  · exact kid11_part679_checked

  · exact kid11_part685_checked

def kid11_part686 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.split 14 (4,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 49 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (3),
.cycle 3 12 true (1),
.cycle 14 1 true (4),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 27 9 false (2),
.last 17 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (4),
.cycle 11 4 true (4)
]),
.cycle 26 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 50 true (3),
.cycle 12 7 true (3),
.split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (3),
.cycle 3 12 true (1),
.last 17 (4,true),
.cycle 8 7 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 14 1 true (6),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 12 7 true (3),
.last 17 (4,true),
.last 23 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (6),
.cycle 11 4 true (4)
]),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.split 14 (4,false) (byMove [
.cycle 9 7 true (3),
.last 20 (4,true),
.cycle 39 1 false (1),
.cycle 7 10 true (3),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 13 2 true (4),
.cycle 12 4 true (3),
.last 24 (4,true),
.last 17 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true)
]),
.cycle 24 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.split 14 (4,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 13 2 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (4),
.cycle 3 12 true (1),
.cycle 14 1 true (6),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 12 3 true (4),
.cycle 13 3 true (5),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (6),
.cycle 11 4 true (4)
]),
.cycle 11 3 true (4)
])
theorem kid11_part686_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part686) = true := by rfl

def kid11_part566 : Audit := .split 10 (2,true) (byMove [(kid11_part567),(kid11_part568),(kid11_part569),(kid11_part570),(kid11_part571),(kid11_part596),(kid11_part597),(kid11_part598),(kid11_part599),(kid11_part600),(kid11_part601),(kid11_part626),(kid11_part627),(kid11_part628),(kid11_part629),(kid11_part630),(kid11_part631),(kid11_part656),(kid11_part657),(kid11_part658),(kid11_part659),(kid11_part660),(kid11_part661),(kid11_part686)])

theorem kid11_part566_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (kid11_part566) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part567),(kid11_part568),(kid11_part569),(kid11_part570),(kid11_part571),(kid11_part596),(kid11_part597),(kid11_part598),(kid11_part599),(kid11_part600),(kid11_part601),(kid11_part626),(kid11_part627),(kid11_part628),(kid11_part629),(kid11_part630),(kid11_part631),(kid11_part656),(kid11_part657),(kid11_part658),(kid11_part659),(kid11_part660),(kid11_part661),(kid11_part686)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part567_checked

  · exact kid11_part597_checked

  · exact kid11_part627_checked

  · exact kid11_part657_checked

  · exact kid11_part568_checked

  · exact kid11_part598_checked

  · exact kid11_part628_checked

  · exact kid11_part658_checked

  · exact kid11_part569_checked

  · exact kid11_part599_checked

  · exact kid11_part629_checked

  · exact kid11_part659_checked

  · exact kid11_part570_checked

  · exact kid11_part600_checked

  · exact kid11_part630_checked

  · exact kid11_part660_checked

  · exact kid11_part571_checked

  · exact kid11_part601_checked

  · exact kid11_part631_checked

  · exact kid11_part661_checked

  · exact kid11_part596_checked

  · exact kid11_part626_checked

  · exact kid11_part656_checked

  · exact kid11_part686_checked

def kid11_part687 : Audit := .cycle 0 11 true (0)
theorem kid11_part687_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (kid11_part687) = true := by rfl

def kid11_part688 : Audit := .cycle 4 5 true (1)
theorem kid11_part688_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (kid11_part688) = true := by rfl

def kid11_part691 : Audit := .cycle 1 13 true (1)
theorem kid11_part691_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part691) = true := by rfl

def kid11_part692 : Audit := .cycle 7 6 true (2)
theorem kid11_part692_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part692) = true := by rfl

def kid11_part693 : Audit := .cycle 29 1 false (1)
theorem kid11_part693_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part693) = true := by rfl

def kid11_part694 : Audit := .cycle 0 14 true (0)
theorem kid11_part694_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part694) = true := by rfl

def kid11_part695 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 1 16 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.cycle 17 6 false (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.last 16 (5,true)
])
theorem kid11_part695_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part695) = true := by rfl

def kid11_part696 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 24 true (2),
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 23 3 false (1),
.last 16 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.last 15 (4,true)
])
theorem kid11_part696_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part696) = true := by rfl

def kid11_part697 : Audit := .cycle 0 13 true (0)
theorem kid11_part697_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part697) = true := by rfl

def kid11_part698 : Audit := .cycle 1 12 true (1)
theorem kid11_part698_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part698) = true := by rfl

def kid11_part699 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 256, 4, 128, 256, 8, 128, 256, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 14 7 true (3),
.cycle 0 22 true (0),
.cycle 11 13 true (3),
.cycle 7 15 true (2),
.cycle 11 10 true (3),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.cycle 9 12 true (2),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.last 22 (4,true)
])
theorem kid11_part699_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part699) = true := by rfl

def kid11_part700 : Audit := .cycle 3 10 true (1)
theorem kid11_part700_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part700) = true := by rfl

def kid11_part701 : Audit := .cycle 0 14 true (0)
theorem kid11_part701_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part701) = true := by rfl

def kid11_part702 : Audit := .cycle 8 5 true (2)
theorem kid11_part702_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part702) = true := by rfl

def kid11_part703 : Audit := .cycle 6 7 true (2)
theorem kid11_part703_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part703) = true := by rfl

def kid11_part704 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 256, 4, 128, 256, 8, 128, 256, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 13 7 true (2),
.cycle 0 16 true (0),
.cycle 11 7 true (3),
.cycle 7 9 true (2),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 9 6 true (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.last 16 (4,true)
])
theorem kid11_part704_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part704) = true := by rfl

def kid11_part705 : Audit := .cycle 5 11 true (1)
theorem kid11_part705_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part705) = true := by rfl

def kid11_part706 : Audit := .cycle 1 14 true (1)
theorem kid11_part706_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part706) = true := by rfl

def kid11_part707 : Audit := .split 13 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 25 7 false (2),
.cycle 17 6 false (2),
.cycle 7 9 true (2),
.last 24 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 9 6 true (2),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 17 6 false (2),
.cycle 5 9 true (1),
.cycle 17 6 false (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 1 16 true (1),
.last 14 (5,true)
])
theorem kid11_part707_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part707) = true := by rfl

def kid11_part708 : Audit := .split 13 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 25 7 false (2),
.last 16 (4,true),
.cycle 7 9 true (2),
.last 14 (4,true),
.last 16 (4,true),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 11 7 true (3),
.cycle 7 11 true (2),
.cycle 23 3 false (1),
.last 16 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true)
])
theorem kid11_part708_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part708) = true := by rfl

def kid11_part709 : Audit := .cycle 0 13 true (0)
theorem kid11_part709_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part709) = true := by rfl

def kid11_part710 : Audit := .cycle 1 12 true (1)
theorem kid11_part710_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part710) = true := by rfl

def kid11_part711 : Audit := .cycle 2 11 true (1)
theorem kid11_part711_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part711) = true := by rfl

def kid11_part712 : Audit := .cycle 1 15 true (1)
theorem kid11_part712_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part712) = true := by rfl

def kid11_part713 : Audit := .cycle 1 14 true (1)
theorem kid11_part713_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part713) = true := by rfl

def kid11_part714 : Audit := .split 14 (4,true) (byMove [
.cycle 10 5 true (2),
.last 21 (5,true),
.last 27 (5,true),
.cycle 7 10 true (2),
.last 31 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 0 17 true (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.cycle 5 10 true (1),
.last 21 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.last 15 (5,true)
])
theorem kid11_part714_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part714) = true := by rfl

def kid11_part690 : Audit := .split 12 (2,true) (byMove [(kid11_part691),(kid11_part692),(kid11_part693),(kid11_part694),(kid11_part695),(kid11_part696),(kid11_part697),(kid11_part698),(kid11_part699),(kid11_part700),(kid11_part701),(kid11_part702),(kid11_part703),(kid11_part704),(kid11_part705),(kid11_part706),(kid11_part707),(kid11_part708),(kid11_part709),(kid11_part710),(kid11_part711),(kid11_part712),(kid11_part713),(kid11_part714)])

theorem kid11_part690_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part690) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid11_part691),(kid11_part692),(kid11_part693),(kid11_part694),(kid11_part695),(kid11_part696),(kid11_part697),(kid11_part698),(kid11_part699),(kid11_part700),(kid11_part701),(kid11_part702),(kid11_part703),(kid11_part704),(kid11_part705),(kid11_part706),(kid11_part707),(kid11_part708),(kid11_part709),(kid11_part710),(kid11_part711),(kid11_part712),(kid11_part713),(kid11_part714)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part691_checked

  · exact kid11_part697_checked

  · exact kid11_part703_checked

  · exact kid11_part709_checked

  · exact kid11_part692_checked

  · exact kid11_part698_checked

  · exact kid11_part704_checked

  · exact kid11_part710_checked

  · exact kid11_part693_checked

  · exact kid11_part699_checked

  · exact kid11_part705_checked

  · exact kid11_part711_checked

  · exact kid11_part694_checked

  · exact kid11_part700_checked

  · exact kid11_part706_checked

  · exact kid11_part712_checked

  · exact kid11_part695_checked

  · exact kid11_part701_checked

  · exact kid11_part707_checked

  · exact kid11_part713_checked

  · exact kid11_part696_checked

  · exact kid11_part702_checked

  · exact kid11_part708_checked

  · exact kid11_part714_checked

def kid11_part715 : Audit := .cycle 1 16 true (1)
theorem kid11_part715_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part715) = true := by rfl

def kid11_part717 : Audit := .cycle 0 15 true (0)
theorem kid11_part717_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part717) = true := by rfl

def kid11_part718 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 1 20 true (1),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 28 true (1),
.cycle 13 7 true (1),
.cycle 13 9 true (1),
.cycle 12 9 true (1),
.cycle 43 1 false (1),
.cycle 7 14 true (1),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 9 10 true (1),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 1 20 true (1),
.last 20 (4,true)
])
theorem kid11_part718_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part718) = true := by rfl

def kid11_part719 : Audit := .cycle 21 1 false (1)
theorem kid11_part719_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part719) = true := by rfl

def kid11_part720 : Audit := .cycle 0 17 true (0)
theorem kid11_part720_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part720) = true := by rfl

def kid11_part721 : Audit := .cycle 15 1 false (-1)
theorem kid11_part721_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part721) = true := by rfl

def kid11_part722 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.last 19 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 17 true (0),
.cycle 17 1 false (1),
.cycle 17 1 false (-1),
.last 17 (5,true),
.cycle 16 1 false (2),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 17 true (0),
.cycle 20 1 false (-2),
.last 14 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part722_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part722) = true := by rfl

def kid11_part723 : Audit := .cycle 7 5 true (2)
theorem kid11_part723_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part723) = true := by rfl

def kid11_part724 : Audit := .cycle 1 12 true (1)
theorem kid11_part724_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part724) = true := by rfl

def kid11_part725 : Audit := .cycle 0 13 true (0)
theorem kid11_part725_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part725) = true := by rfl

def kid11_part726 : Audit := .split 17 (5,true) (byMove [
.cycle 3 18 true (0),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.cycle 3 20 true (0),
.cycle 20 1 false (2),
.last 19 (4,true),
.cycle 1 18 true (0),
.cycle 11 11 true (0),
.cycle 11 9 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 11 11 true (0),
.cycle 19 11 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (4),
.cycle 20 1 false (2),
.last 19 (4,true),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.cycle 0 37 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 20 (4,true)
])
theorem kid11_part726_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part726) = true := by rfl

def kid11_part727 : Audit := .split 19 (5,true) (byMove [
.cycle 2 22 true (0),
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 2 24 true (0),
.cycle 24 1 false (2),
.last 21 (4,true),
.cycle 1 20 true (0),
.cycle 11 11 true (0),
.cycle 13 11 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 11 11 true (0),
.cycle 21 13 true (2),
.last 22 (4,true),
.cycle 1 22 true (0),
.cycle 34 1 false (4),
.cycle 24 1 false (2),
.last 21 (4,true),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.last 42 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 22 (4,true)
])
theorem kid11_part727_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part727) = true := by rfl

def kid11_part728 : Audit := .split 19 (5,true) (byMove [
.cycle 35 1 false (1),
.cycle 0 23 true (0),
.cycle 39 1 false (3),
.cycle 34 1 false (2),
.cycle 25 1 false (1),
.last 21 (4,true),
.cycle 1 20 true (0),
.cycle 14 11 true (0),
.cycle 14 11 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 14 11 true (0),
.cycle 37 1 false (1),
.cycle 37 1 false (1),
.cycle 1 22 true (0),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.last 21 (4,true),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.cycle 8 13 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 22 (4,true)
])
theorem kid11_part728_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part728) = true := by rfl

def kid11_part729 : Audit := .cycle 17 5 false (2)
theorem kid11_part729_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part729) = true := by rfl

def kid11_part730 : Audit := .split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 22 true (1),
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.cycle 23 1 false (-1),
.last 16 (4,true),
.cycle 7 9 true (1),
.cycle 1 18 true (1),
.cycle 0 17 true (0),
.cycle 0 23 true (0),
.last 24 (4,true),
.cycle 18 11 true (0),
.cycle 19 9 false (2),
.cycle 11 4 true (1),
.cycle 7 11 true (1),
.cycle 26 1 false (0),
.cycle 23 1 false (-1),
.last 16 (4,true),
.cycle 12 7 true (1),
.cycle 1 18 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 9 6 true (1),
.last 16 (4,true)
])
theorem kid11_part730_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part730) = true := by rfl

def kid11_part731 : Audit := .cycle 7 7 true (1)
theorem kid11_part731_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part731) = true := by rfl

def kid11_part732 : Audit := .cycle 18 1 false (0)
theorem kid11_part732_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part732) = true := by rfl

def kid11_part733 : Audit := .cycle 15 1 false (-1)
theorem kid11_part733_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part733) = true := by rfl

def kid11_part734 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.last 19 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 17 1 false (-1),
.last 17 (5,true),
.cycle 17 1 false (3),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 23 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 13 (5,true)
])
theorem kid11_part734_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part734) = true := by rfl

def kid11_part735 : Audit := .cycle 7 5 true (2)
theorem kid11_part735_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part735) = true := by rfl

def kid11_part736 : Audit := .cycle 1 12 true (1)
theorem kid11_part736_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part736) = true := by rfl

def kid11_part737 : Audit := .cycle 0 13 true (0)
theorem kid11_part737_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part737) = true := by rfl

def kid11_part738 : Audit := .cycle 4 7 true (1)
theorem kid11_part738_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part738) = true := by rfl

def kid11_part739 : Audit := .cycle 9 2 true (2)
theorem kid11_part739_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part739) = true := by rfl

def kid11_part740 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 1 16 true (1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 25 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 13 5 true (3),
.last 13 (5,true)
])
theorem kid11_part740_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part740) = true := by rfl

def kid11_part716 : Audit := .split 10 (2,true) (byMove [(kid11_part717),(kid11_part718),(kid11_part719),(kid11_part720),(kid11_part721),(kid11_part722),(kid11_part723),(kid11_part724),(kid11_part725),(kid11_part726),(kid11_part727),(kid11_part728),(kid11_part729),(kid11_part730),(kid11_part731),(kid11_part732),(kid11_part733),(kid11_part734),(kid11_part735),(kid11_part736),(kid11_part737),(kid11_part738),(kid11_part739),(kid11_part740)])

theorem kid11_part716_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part716) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part717),(kid11_part718),(kid11_part719),(kid11_part720),(kid11_part721),(kid11_part722),(kid11_part723),(kid11_part724),(kid11_part725),(kid11_part726),(kid11_part727),(kid11_part728),(kid11_part729),(kid11_part730),(kid11_part731),(kid11_part732),(kid11_part733),(kid11_part734),(kid11_part735),(kid11_part736),(kid11_part737),(kid11_part738),(kid11_part739),(kid11_part740)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part717_checked

  · exact kid11_part723_checked

  · exact kid11_part729_checked

  · exact kid11_part735_checked

  · exact kid11_part718_checked

  · exact kid11_part724_checked

  · exact kid11_part730_checked

  · exact kid11_part736_checked

  · exact kid11_part719_checked

  · exact kid11_part725_checked

  · exact kid11_part731_checked

  · exact kid11_part737_checked

  · exact kid11_part720_checked

  · exact kid11_part726_checked

  · exact kid11_part732_checked

  · exact kid11_part738_checked

  · exact kid11_part721_checked

  · exact kid11_part727_checked

  · exact kid11_part733_checked

  · exact kid11_part739_checked

  · exact kid11_part722_checked

  · exact kid11_part728_checked

  · exact kid11_part734_checked

  · exact kid11_part740_checked

def kid11_part741 : Audit := .cycle 7 5 true (2)
theorem kid11_part741_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part741) = true := by rfl

def kid11_part742 : Audit := .split 10 (4,true) (byMove [
.cycle 0 15 true (0),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 1 20 true (1),
.cycle 0 24 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 28 (2,true),
.cycle 13 7 true (1),
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 32, 32, 128, 256, 8, 128, 32, 33, 4096],[128, 32, 4096, 1, 8, 32, 128, 32, 4096, 1, 32, 32, 4096],4096⟩,
.cycle 74 1 false (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 9 10 true (1),
.cycle 1 24 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 1 20 true (1),
.cycle 0 24 true (0)
]),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 7 5 true (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 26 (5,true),
.last 21 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 35 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 14 true (1),
.cycle 0 23 true (0)
]),
.cycle 0 13 true (0),
.split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.last 22 (2,true),
.cycle 20 1 false (2),
.cycle 26 1 false (4),
.cycle 1 18 true (0),
.cycle 24 1 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 11 9 true (0),
.cycle 24 1 false (2),
.cycle 19 11 true (2),
.last 19 (2,true),
.cycle 1 20 true (0),
.cycle 30 1 false (4),
.cycle 20 1 false (2),
.cycle 26 1 false (4),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 37 true (0),
.cycle 0 22 true (0)
]),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 17 5 false (2),
.split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 15 (5,true),
.last 13 (5,true),
.cycle 7 7 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 18 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.last 36 (5,true),
.cycle 1 18 true (1),
.last 15 (5,true),
.last 13 (5,true),
.last 19 (5,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (5,true),
.last 16 (5,true)
]),
.cycle 7 7 true (1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 7 5 true (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 14 true (1),
.cycle 7 8 true (2)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 9 2 true (2),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 24 1 false (0),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 10 4 true (2),
.cycle 20 1 false (-2),
.cycle 1 14 true (1),
.last 23 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 6 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 11 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 12 2 true (2),
.cycle 20 1 false (-2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 5 true (4),
.cycle 14 3 true (4)
])
])
theorem kid11_part742_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part742) = true := by rfl

def kid11_part744 : Audit := .cycle 0 15 true (0)
theorem kid11_part744_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part744) = true := by rfl

def kid11_part745 : Audit := .cycle 1 18 true (1)
theorem kid11_part745_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part745) = true := by rfl

def kid11_part746 : Audit := .cycle 21 1 false (1)
theorem kid11_part746_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part746) = true := by rfl

def kid11_part747 : Audit := .cycle 0 17 true (0)
theorem kid11_part747_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part747) = true := by rfl

def kid11_part748 : Audit := .cycle 13 2 false (-1)
theorem kid11_part748_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part748) = true := by rfl

def kid11_part749 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 14 2 false (2),
.last 13 (2,true),
.last 16 (2,true),
.cycle 14 2 false (2),
.cycle 14 2 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 17 2 false (-1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1)
])
theorem kid11_part749_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part749) = true := by rfl

def kid11_part750 : Audit := .cycle 7 5 true (2)
theorem kid11_part750_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part750) = true := by rfl

def kid11_part751 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 22 2 false (2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 128, 256, 1073741824, 128, 256, 2097152, 131072, 1073741824, 537821568, 128, 256, 134217728, 524288, 537821568, 1073741824, 128, 256, 2097152, 536870912, 1073741824, 537821568, 1073741824],[128, 32, 0, 1, 1073741824, 2, 128, 131072, 537821568, 4096, 1073741824, 8192, 128, 8388608, 131072, 262144, 1073741824, 524288, 128, 536870912, 524288, 16777216, 1073741824, 33554432, 128, 8388608, 536870912, 262144, 1073741824, 524288, 1073741824],1350633472⟩,
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 14 true (1),
.last 14 (4,true)
])
theorem kid11_part751_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part751) = true := by rfl

def kid11_part752 : Audit := .cycle 0 13 true (0)
theorem kid11_part752_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part752) = true := by rfl

def kid11_part753 : Audit := .cycle 0 19 true (0)
theorem kid11_part753_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part753) = true := by rfl

def kid11_part754 : Audit := .cycle 15 2 false (1)
theorem kid11_part754_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part754) = true := by rfl

def kid11_part755 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 30 31 false (7),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 17 (2,true),
.cycle 16 2 false (2),
.last 15 (2,true),
.cycle 29 2 false (5),
.cycle 16 2 false (2),
.cycle 16 2 false (2),
.cycle 10 7 false (3),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 17 (2,true),
.cycle 19 2 false (1),
.last 15 (2,true),
.cycle 7 18 true (0),
.cycle 21 2 false (1),
.cycle 19 2 false (1)
])
theorem kid11_part755_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part755) = true := by rfl

def kid11_part756 : Audit := .cycle 17 5 false (2)
theorem kid11_part756_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part756) = true := by rfl

def kid11_part757 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 7 7 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 3 18 true (1),
.last 15 (4,true),
.cycle 17 5 false (2),
.cycle 19 7 false (2),
.cycle 10 4 true (1),
.cycle 37 17 true (1),
.cycle 1 18 true (1),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 10 9 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 10 6 true (1),
.last 14 (4,true)
])
theorem kid11_part757_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part757) = true := by rfl

def kid11_part758 : Audit := .cycle 7 7 true (1)
theorem kid11_part758_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part758) = true := by rfl

def kid11_part759 : Audit := .cycle 18 1 false (0)
theorem kid11_part759_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part759) = true := by rfl

def kid11_part760 : Audit := .cycle 13 2 false (-1)
theorem kid11_part760_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part760) = true := by rfl

def kid11_part761 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 18 2 false (0),
.cycle 15 2 false (1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 15 2 false (3),
.cycle 14 2 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 20 2 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 4 true (0),
.last 13 (2,true),
.last 16 (2,true),
.cycle 19 2 false (-1),
.cycle 15 2 false (-1)
])
theorem kid11_part761_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part761) = true := by rfl

def kid11_part762 : Audit := .cycle 7 5 true (2)
theorem kid11_part762_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part762) = true := by rfl

def kid11_part763 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 7 7 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 14 true (1),
.last 14 (4,true)
])
theorem kid11_part763_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part763) = true := by rfl

def kid11_part764 : Audit := .cycle 0 13 true (0)
theorem kid11_part764_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part764) = true := by rfl

def kid11_part765 : Audit := .cycle 4 7 true (1)
theorem kid11_part765_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part765) = true := by rfl

def kid11_part766 : Audit := .cycle 9 2 true (2)
theorem kid11_part766_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part766) = true := by rfl

def kid11_part767 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.last 23 (2,true),
.last 17 (2,true),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1),
.cycle 6 7 true (2),
.cycle 40 2 false (8),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 25 2 false (3),
.cycle 14 3 true (4),
.cycle 20 5 true (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 5 34 true (0),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1),
.cycle 6 7 true (2),
.cycle 7 10 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 13 5 true (3),
.cycle 14 3 true (4)
])
theorem kid11_part767_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part767) = true := by rfl

def kid11_part743 : Audit := .split 10 (5,true) (byMove [(kid11_part744),(kid11_part745),(kid11_part746),(kid11_part747),(kid11_part748),(kid11_part749),(kid11_part750),(kid11_part751),(kid11_part752),(kid11_part753),(kid11_part754),(kid11_part755),(kid11_part756),(kid11_part757),(kid11_part758),(kid11_part759),(kid11_part760),(kid11_part761),(kid11_part762),(kid11_part763),(kid11_part764),(kid11_part765),(kid11_part766),(kid11_part767)])

theorem kid11_part743_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part743) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part744),(kid11_part745),(kid11_part746),(kid11_part747),(kid11_part748),(kid11_part749),(kid11_part750),(kid11_part751),(kid11_part752),(kid11_part753),(kid11_part754),(kid11_part755),(kid11_part756),(kid11_part757),(kid11_part758),(kid11_part759),(kid11_part760),(kid11_part761),(kid11_part762),(kid11_part763),(kid11_part764),(kid11_part765),(kid11_part766),(kid11_part767)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part744_checked

  · exact kid11_part750_checked

  · exact kid11_part756_checked

  · exact kid11_part762_checked

  · exact kid11_part745_checked

  · exact kid11_part751_checked

  · exact kid11_part757_checked

  · exact kid11_part763_checked

  · exact kid11_part746_checked

  · exact kid11_part752_checked

  · exact kid11_part758_checked

  · exact kid11_part764_checked

  · exact kid11_part747_checked

  · exact kid11_part753_checked

  · exact kid11_part759_checked

  · exact kid11_part765_checked

  · exact kid11_part748_checked

  · exact kid11_part754_checked

  · exact kid11_part760_checked

  · exact kid11_part766_checked

  · exact kid11_part749_checked

  · exact kid11_part755_checked

  · exact kid11_part761_checked

  · exact kid11_part767_checked

def kid11_part768 : Audit := .cycle 1 10 true (1)
theorem kid11_part768_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part768) = true := by rfl

def kid11_part769 : Audit := .cycle 7 3 true (3)
theorem kid11_part769_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part769) = true := by rfl

def kid11_part771 : Audit := .cycle 0 11 true (0)
theorem kid11_part771_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part771) = true := by rfl

def kid11_part772 : Audit := .cycle 1 10 true (1)
theorem kid11_part772_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part772) = true := by rfl

def kid11_part773 : Audit := .cycle 2 9 true (1)
theorem kid11_part773_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part773) = true := by rfl

def kid11_part774 : Audit := .cycle 1 13 true (1)
theorem kid11_part774_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part774) = true := by rfl

def kid11_part775 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 20 11 true (3),
.cycle 13 7 true (2),
.last 31 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 8, 1, 4096, 32, 128, 32, 4096, 1, 4096, 32, 4096],6144⟩,
.cycle 7 14 true (2),
.last 22 (4,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 9 11 true (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (2),
.last 21 (4,true)
])
theorem kid11_part775_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part775) = true := by rfl

def kid11_part776 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 0 16 true (0),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 15 3 false (-1),
.cycle 1 13 true (1),
.cycle 26 3 false (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.last 25 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.cycle 17 3 false (0),
.cycle 15 3 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 22 (5,true),
.last 13 (5,true)
])
theorem kid11_part776_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part776) = true := by rfl

def kid11_part777 : Audit := .cycle 0 11 true (0)
theorem kid11_part777_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part777) = true := by rfl

def kid11_part778 : Audit := .cycle 1 10 true (1)
theorem kid11_part778_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part778) = true := by rfl

def kid11_part779 : Audit := .split 19 (5,true) (byMove [
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 1 35 true (1),
.cycle 0 23 true (0),
.last 21 (4,true),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 2, 128, 32, 4, 1, 4096, 2, 4096],6144⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 21 true (0),
.last 20 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 32, 128, 32, 4, 1, 4096, 32, 4096],6144⟩,
.cycle 7 17 true (2),
.cycle 10 12 true (2),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],6144⟩,
.last 21 (4,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 22 (4,true)
])
theorem kid11_part779_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part779) = true := by rfl

def kid11_part780 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 11 9 true (2),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 19 9 true (3),
.cycle 11 7 true (2),
.last 29 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 8, 1, 4096, 32, 128, 32, 8, 1, 4096, 32, 4096],6144⟩,
.cycle 7 12 true (2),
.cycle 3 17 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 9 9 true (2),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 11 9 true (2),
.last 19 (4,true)
])
theorem kid11_part780_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part780) = true := by rfl

def kid11_part781 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 1 25 true (1),
.cycle 2 34 true (1),
.last 27 (4,true),
.cycle 1 25 true (1),
.last 23 (4,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 23 (4,true),
.cycle 1 23 true (1),
.last 22 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 16, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 16, 1, 4096, 32, 128, 32, 16, 1, 4096, 32, 4096],6144⟩,
.cycle 7 22 true (2),
.last 24 (4,true),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.last 24 (4,true),
.last 23 (4,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 23 (4,true),
.cycle 1 23 true (1),
.last 22 (4,true),
.last 25 (4,true)
])
theorem kid11_part781_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part781) = true := by rfl

def kid11_part782 : Audit := .cycle 8 3 true (3)
theorem kid11_part782_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part782) = true := by rfl

def kid11_part783 : Audit := .cycle 7 5 true (3)
theorem kid11_part783_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part783) = true := by rfl

def kid11_part784 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 9 true (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 13 7 true (2),
.last 26 (4,true),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 9 6 true (3),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 9 true (3),
.last 16 (4,true)
])
theorem kid11_part784_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part784) = true := by rfl

def kid11_part785 : Audit := .cycle 0 13 true (0)
theorem kid11_part785_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part785) = true := by rfl

def kid11_part786 : Audit := .cycle 4 7 true (1)
theorem kid11_part786_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part786) = true := by rfl

def kid11_part787 : Audit := .cycle 9 2 true (3)
theorem kid11_part787_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part787) = true := by rfl

def kid11_part788 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 1 16 true (1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 1 16 true (1),
.cycle 15 3 false (-1),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.last 27 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 17 3 false (0),
.cycle 15 3 false (-1),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 23 (5,true),
.last 13 (5,true)
])
theorem kid11_part788_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part788) = true := by rfl

def kid11_part789 : Audit := .cycle 0 11 true (0)
theorem kid11_part789_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part789) = true := by rfl

def kid11_part790 : Audit := .cycle 1 10 true (1)
theorem kid11_part790_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part790) = true := by rfl

def kid11_part791 : Audit := .cycle 2 9 true (1)
theorem kid11_part791_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part791) = true := by rfl

def kid11_part792 : Audit := .cycle 1 13 true (1)
theorem kid11_part792_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part792) = true := by rfl

def kid11_part793 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 19 true (4),
.cycle 13 7 true (4),
.last 31 (4,true),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 10 11 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 9 11 true (3),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.last 21 (4,true)
])
theorem kid11_part793_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part793) = true := by rfl

def kid11_part794 : Audit := .split 12 (4,true) (byMove [
.cycle 14 5 true (4),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 7 15 true (2),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 25 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 22 (5,true),
.last 13 (5,true)
])
theorem kid11_part794_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part794) = true := by rfl

def kid11_part770 : Audit := .split 10 (2,true) (byMove [(kid11_part771),(kid11_part772),(kid11_part773),(kid11_part774),(kid11_part775),(kid11_part776),(kid11_part777),(kid11_part778),(kid11_part779),(kid11_part780),(kid11_part781),(kid11_part782),(kid11_part783),(kid11_part784),(kid11_part785),(kid11_part786),(kid11_part787),(kid11_part788),(kid11_part789),(kid11_part790),(kid11_part791),(kid11_part792),(kid11_part793),(kid11_part794)])

theorem kid11_part770_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part770) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid11_part771),(kid11_part772),(kid11_part773),(kid11_part774),(kid11_part775),(kid11_part776),(kid11_part777),(kid11_part778),(kid11_part779),(kid11_part780),(kid11_part781),(kid11_part782),(kid11_part783),(kid11_part784),(kid11_part785),(kid11_part786),(kid11_part787),(kid11_part788),(kid11_part789),(kid11_part790),(kid11_part791),(kid11_part792),(kid11_part793),(kid11_part794)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part771_checked

  · exact kid11_part777_checked

  · exact kid11_part783_checked

  · exact kid11_part789_checked

  · exact kid11_part772_checked

  · exact kid11_part778_checked

  · exact kid11_part784_checked

  · exact kid11_part790_checked

  · exact kid11_part773_checked

  · exact kid11_part779_checked

  · exact kid11_part785_checked

  · exact kid11_part791_checked

  · exact kid11_part774_checked

  · exact kid11_part780_checked

  · exact kid11_part786_checked

  · exact kid11_part792_checked

  · exact kid11_part775_checked

  · exact kid11_part781_checked

  · exact kid11_part787_checked

  · exact kid11_part793_checked

  · exact kid11_part776_checked

  · exact kid11_part782_checked

  · exact kid11_part788_checked

  · exact kid11_part794_checked

def kid11_part795 : Audit := .cycle 0 11 true (0)
theorem kid11_part795_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part795) = true := by rfl

def kid11_part796 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 11 1 true (3),
.cycle 14 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.last 24 (2,true),
.last 36 (2,true),
.last 22 (2,true),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 16, 4, 128, 256, 8, 128, 16, 4096, 4096],[128, 32, 4096, 1, 4, 2, 128, 32, 4096, 1, 4, 2, 4096],6144⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.last 32 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 16, 4, 128, 256, 8, 128, 16, 4096, 4096],[128, 32, 4096, 1, 4, 32, 128, 32, 4096, 1, 4, 32, 4096],6144⟩,
.cycle 7 17 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.last 22 (2,true),
.last 22 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 29 1 true (9),
.last 23 (2,true)
]),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 18 1 true (4),
.cycle 0 21 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 11 7 true (2),
.cycle 18 1 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 16, 9, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 9 9 true (2),
.cycle 1 21 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 18 1 true (6),
.cycle 0 21 true (0)
]),
.cycle 11 1 true (5),
.cycle 8 3 true (3),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 13 1 true (5),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.last 16 (5,true)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 9 2 true (3),
.cycle 14 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 11 1 true (5),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 19 7 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 31 (2,true),
.cycle 3 11 true (1),
.cycle 14 1 true (6),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 20 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 1 true (6),
.cycle 11 3 true (4)
])
])
theorem kid11_part796_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part796) = true := by rfl

def kid11_part797 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 4 true (3),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.last 17 (2,true),
.cycle 20 3 false (0),
.cycle 15 3 false (-1),
.cycle 1 13 true (1),
.cycle 26 3 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 31 3 false (3),
.cycle 19 3 false (1),
.cycle 19 5 false (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.cycle 17 3 false (0),
.cycle 15 3 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 7 true (2),
.cycle 18 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 18 true (2),
.cycle 3 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],6144⟩,
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 12 9 true (2),
.last 38 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 32, 1, 4096, 4, 128, 32, 32, 1, 4096, 4, 4096],6144⟩,
.cycle 7 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],6144⟩,
.cycle 19 4 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 8 14 true (2),
.last 22 (4,true)
]),
.cycle 10 7 true (2),
.cycle 8 4 true (3),
.cycle 8 3 true (3),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 23 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 6 true (3),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 23 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 6 true (3),
.last 14 (4,true)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 9 2 true (3),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.last 17 (2,true),
.cycle 20 3 false (0),
.cycle 15 3 false (-1),
.cycle 6 7 true (2),
.cycle 24 3 false (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 40 3 false (8),
.cycle 19 3 false (1),
.cycle 19 5 false (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.cycle 17 3 false (0),
.cycle 15 3 false (-1),
.cycle 6 7 true (2),
.cycle 10 4 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 8 8 true (2),
.cycle 18 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 4 true (3),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 9 true (2),
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 7 true (3),
.cycle 10 3 true (4),
.cycle 10 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 23 5 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 7 true (3),
.cycle 10 3 true (4)
])
])
theorem kid11_part797_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part797) = true := by rfl

def kid11_part798 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 6 8 true (2),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 25 1 false (1),
.last 19 (2,true),
.cycle 17 10 false (2),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 11 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 11 true (2),
.cycle 19 8 false (2),
.cycle 21 5 false (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 22 1 false (0),
.cycle 17 6 false (2),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 11 true (2),
.cycle 16 9 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 10 18 true (2),
.cycle 3 20 true (1),
.cycle 7 18 true (2),
.cycle 8 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 14 9 true (2),
.cycle 7 18 true (2),
.cycle 11 15 true (2),
.cycle 7 17 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 25 true (0),
.cycle 10 16 true (2),
.cycle 11 14 true (2),
.cycle 19 6 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 6 18 true (2),
.last 24 (4,true)
]),
.cycle 10 7 true (2),
.cycle 7 8 true (2),
.cycle 11 5 true (3),
.cycle 7 7 true (2),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 10 true (2),
.cycle 3 12 true (1),
.cycle 7 10 true (2),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.cycle 11 4 true (3),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 6 10 true (2),
.last 16 (4,true)
]),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 25 1 false (1),
.last 19 (2,true),
.cycle 17 10 false (2),
.cycle 15 7 false (1),
.cycle 6 9 true (2),
.cycle 29 9 false (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 7 12 true (2),
.cycle 19 8 false (2),
.cycle 21 5 false (2),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 22 1 false (0),
.cycle 17 6 false (2),
.cycle 15 7 false (1),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 6 12 true (2),
.cycle 16 9 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 6 8 true (2),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 10 9 true (2),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 15 9 false (3),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 11 true (2),
.cycle 12 3 true (4),
.cycle 11 5 true (3),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 10 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 27 5 true (3),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 11 true (2),
.cycle 12 3 true (4)
])
])
theorem kid11_part798_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part798) = true := by rfl

def kid11_part800 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 13 3 true (3),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.cycle 0 17 true (0),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 13 4 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.last 16 (4,true)
])
theorem kid11_part800_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part800) = true := by rfl

def kid11_part801 : Audit := .cycle 0 15 true (0)
theorem kid11_part801_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part801) = true := by rfl

def kid11_part802 : Audit := .cycle 38 1 false (4)
theorem kid11_part802_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part802) = true := by rfl

def kid11_part803 : Audit := .cycle 21 1 false (1)
theorem kid11_part803_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part803) = true := by rfl

def kid11_part804 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 7 9 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 3 24 true (1),
.last 18 (4,true),
.cycle 19 7 false (1),
.cycle 21 9 false (1),
.cycle 18 5 false (1),
.cycle 1 50 true (-1),
.cycle 1 20 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 75 39 false (5),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 18 9 false (2),
.last 16 (4,true)
])
theorem kid11_part804_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part804) = true := by rfl

def kid11_part805 : Audit := .split 19 (2,true) (byMove [
.cycle 0 44 true (-2),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.cycle 12 11 false (2),
.last 20 (4,true),
.cycle 15 5 false (1),
.last 34 (4,true),
.last 32 (4,true),
.cycle 0 36 true (-2),
.last 36 (4,true),
.last 20 (4,true),
.last 22 (4,true),
.last 24 (4,true),
.cycle 14 6 false (1),
.cycle 12 13 false (2),
.cycle 12 11 false (2),
.last 20 (4,true),
.cycle 15 5 false (1),
.last 30 (4,true),
.last 26 (4,true),
.cycle 0 36 true (-2),
.last 32 (4,true),
.last 20 (4,true),
.cycle 15 7 false (1)
])
theorem kid11_part805_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part805) = true := by rfl

def kid11_part806 : Audit := .cycle 1 12 true (1)
theorem kid11_part806_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part806) = true := by rfl

def kid11_part807 : Audit := .split 16 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 47 5 false (10),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 34, 427, 427, 128, 256, 8, 128, 2, 4096, 4096],[128, 32, 34, 1, 4096, 2, 128, 32, 427, 1, 4096, 2, 4096],6144⟩,
.cycle 7 12 true (2),
.last 17 (4,true),
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.cycle 12 5 true (3),
.cycle 10 15 true (2),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 1 17 true (1),
.cycle 1 19 true (1),
.cycle 10 7 true (2),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.last 17 (4,true),
.cycle 1 19 true (1),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 1 17 true (1)
])
theorem kid11_part807_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part807) = true := by rfl

def kid11_part808 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 13 18 true (0),
.cycle 40 1 false (4),
.last 16 (4,true),
.cycle 0 20 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 24 true (0),
.cycle 12 3 true (4),
.cycle 10 15 true (2),
.cycle 7 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 15 true (0),
.cycle 13 16 true (0),
.last 16 (4,true),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 29 (4,true),
.last 14 (4,true)
])
theorem kid11_part808_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part808) = true := by rfl

def kid11_part809 : Audit := .cycle 0 13 true (0)
theorem kid11_part809_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part809) = true := by rfl

def kid11_part810 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 33 (2,true),
.last 22 (2,true),
.last 15 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (2,true),
.cycle 0 24 true (0),
.last 15 (2,true),
.last 16 (2,true),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 29 (2,true),
.last 15 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 18 (2,true),
.last 18 (2,true)
])
theorem kid11_part810_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part810) = true := by rfl

def kid11_part811 : Audit := .split 16 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 36 5 false (6),
.cycle 33 1 false (1),
.cycle 7 12 true (2),
.last 17 (4,true),
.cycle 35 5 false (6),
.cycle 1 17 true (1),
.cycle 13 5 true (3),
.cycle 10 15 true (2),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 12 5 true (3),
.cycle 12 7 true (3),
.cycle 10 7 true (2),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.last 17 (4,true),
.cycle 11 7 true (3),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 8 10 true (2)
])
theorem kid11_part811_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part811) = true := by rfl

def kid11_part812 : Audit := .cycle 7 9 true (2)
theorem kid11_part812_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part812) = true := by rfl

def kid11_part813 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 24 5 false (1),
.cycle 29 1 false (1),
.cycle 7 9 true (2),
.last 14 (4,true),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.cycle 12 5 true (2),
.cycle 10 12 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 8 9 true (2),
.cycle 6 13 true (2),
.cycle 10 4 true (2),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 20 (4,true)
])
theorem kid11_part813_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part813) = true := by rfl

def kid11_part814 : Audit := .cycle 1 14 true (1)
theorem kid11_part814_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part814) = true := by rfl

def kid11_part815 : Audit := .cycle 31 1 false (3)
theorem kid11_part815_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part815) = true := by rfl

def kid11_part816 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 9 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 6 9 true (1),
.cycle 17 5 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 4, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],6144⟩,
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 18 7 false (2),
.cycle 19 9 false (2),
.cycle 18 5 false (1),
.cycle 15 12 true (-1),
.cycle 9 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 19 15 false (4),
.cycle 18 11 false (3),
.cycle 2 15 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid11_part816_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part816) = true := by rfl

def kid11_part817 : Audit := .split 19 (2,true) (byMove [
.last 52 (4,true),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.last 25 (4,true),
.last 20 (4,true),
.cycle 15 5 false (1),
.last 24 (4,true),
.cycle 10 10 false (3),
.last 39 (4,true),
.last 25 (4,true),
.last 20 (4,true),
.last 22 (4,true),
.last 24 (4,true),
.cycle 14 6 false (1),
.last 27 (4,true),
.last 25 (4,true),
.last 20 (4,true),
.cycle 15 5 false (1),
.last 24 (4,true),
.last 23 (4,true),
.last 40 (4,true),
.last 25 (4,true),
.last 20 (4,true),
.cycle 15 7 false (1)
])
theorem kid11_part817_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part817) = true := by rfl

def kid11_part818 : Audit := .cycle 1 12 true (1)
theorem kid11_part818_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part818) = true := by rfl

def kid11_part819 : Audit := .cycle 7 5 true (2)
theorem kid11_part819_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part819) = true := by rfl

def kid11_part820 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 28 5 false (2),
.cycle 58 1 false (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 19 true (1),
.cycle 3 10 true (1),
.cycle 12 3 true (4),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.last 14 (4,true)
])
theorem kid11_part820_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part820) = true := by rfl

def kid11_part821 : Audit := .cycle 0 13 true (0)
theorem kid11_part821_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part821) = true := by rfl

def kid11_part822 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.last 17 (2,true),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 16 (2,true),
.cycle 13 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 3 true (5),
.cycle 3 10 true (1),
.last 15 (2,true),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.cycle 13 3 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 16 (2,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 3 true (4),
.cycle 15 3 true (5)
])
theorem kid11_part822_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part822) = true := by rfl

def kid11_part823 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.last 19 (2,true),
.last 15 (2,true),
.cycle 7 10 true (2),
.last 18 (2,true),
.last 31 (2,true),
.cycle 1 15 true (1),
.last 19 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 18 (2,true),
.cycle 12 3 true (4),
.cycle 16 5 true (4),
.cycle 10 5 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.last 18 (2,true),
.cycle 11 5 true (3),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part823_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part823) = true := by rfl

def kid11_part799 : Audit := .split 11 (5,true) (byMove [(kid11_part800),(kid11_part801),(kid11_part802),(kid11_part803),(kid11_part804),(kid11_part805),(kid11_part806),(kid11_part807),(kid11_part808),(kid11_part809),(kid11_part810),(kid11_part811),(kid11_part812),(kid11_part813),(kid11_part814),(kid11_part815),(kid11_part816),(kid11_part817),(kid11_part818),(kid11_part819),(kid11_part820),(kid11_part821),(kid11_part822),(kid11_part823)])

theorem kid11_part799_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part799) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,true) (some mv)) (byMove [(kid11_part800),(kid11_part801),(kid11_part802),(kid11_part803),(kid11_part804),(kid11_part805),(kid11_part806),(kid11_part807),(kid11_part808),(kid11_part809),(kid11_part810),(kid11_part811),(kid11_part812),(kid11_part813),(kid11_part814),(kid11_part815),(kid11_part816),(kid11_part817),(kid11_part818),(kid11_part819),(kid11_part820),(kid11_part821),(kid11_part822),(kid11_part823)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part800_checked

  · exact kid11_part806_checked

  · exact kid11_part812_checked

  · exact kid11_part818_checked

  · exact kid11_part801_checked

  · exact kid11_part807_checked

  · exact kid11_part813_checked

  · exact kid11_part819_checked

  · exact kid11_part802_checked

  · exact kid11_part808_checked

  · exact kid11_part814_checked

  · exact kid11_part820_checked

  · exact kid11_part803_checked

  · exact kid11_part809_checked

  · exact kid11_part815_checked

  · exact kid11_part821_checked

  · exact kid11_part804_checked

  · exact kid11_part810_checked

  · exact kid11_part816_checked

  · exact kid11_part822_checked

  · exact kid11_part805_checked

  · exact kid11_part811_checked

  · exact kid11_part817_checked

  · exact kid11_part823_checked

def kid11_part825 : Audit := .cycle 1 17 true (1)
theorem kid11_part825_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part825) = true := by rfl

def kid11_part826 : Audit := .cycle 1 14 true (1)
theorem kid11_part826_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part826) = true := by rfl

def kid11_part827 : Audit := .split 17 (5,true) (byMove [
.cycle 25 1 false (1),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.last 19 (4,true),
.cycle 1 18 true (0),
.cycle 1 23 true (0),
.cycle 12 18 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 1 23 true (0),
.cycle 29 1 false (1),
.cycle 23 1 false (1),
.cycle 1 20 true (0),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.last 19 (4,true),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.cycle 30 1 false (2),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 20 (4,true)
])
theorem kid11_part827_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part827) = true := by rfl

def kid11_part828 : Audit := .cycle 7 11 true (0)
theorem kid11_part828_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part828) = true := by rfl

def kid11_part829 : Audit := .split 26 (5,true) (byMove [
.last 30 (4,true),
.cycle 1 30 true (-2),
.cycle 39 15 true (1),
.last 32 (4,true),
.cycle 11 16 true (-2),
.last 28 (4,true),
.cycle 0 38 true (-2),
.cycle 27 16 true (3),
.cycle 0 55 true (-2),
.cycle 1 28 true (-2),
.last 27 (4,true),
.cycle 1 33 true (-2),
.last 38 (4,true),
.last 29 (4,true),
.cycle 0 42 true (-2),
.cycle 35 13 true (1),
.cycle 19 8 true (-2),
.last 28 (4,true),
.last 32 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 160, 1, 128, 8192, 16384, 8, 160, 33, 16777216, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 8923136, 25427968, 17301504, 16777216],[128, 32, 128, 1, 16777216, 128, 8192, 32, 16777216, 1, 16777216, 8192, 524288, 2048, 16777216, 64, 16777216, 524288, 524288, 8388608, 17301504, 262144, 16777216, 524288, 16777216],33503296⟩,
.last 28 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 673, 1, 640, 8192, 16384, 8, 160, 33, 16777216, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 11315264, 25427968, 19398656, 16777216],[128, 32, 640, 1, 16777216, 512, 8192, 32, 16777216, 1, 16777216, 32768, 524288, 2048, 16777216, 64, 16777216, 2097152, 524288, 8388608, 19398656, 262144, 16777216, 2097152, 16777216],33503296⟩,
.last 27 (4,true),
.last 30 (4,true)
])
theorem kid11_part829_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part829) = true := by rfl

def kid11_part830 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.last 18 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 28 (5,true),
.last 20 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.cycle 1 22 true (-2),
.last 16 (5,true),
.last 29 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.last 28 (5,true),
.last 19 (5,true),
.last 16 (5,true),
.last 24 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part830_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part830) = true := by rfl

def kid11_part831 : Audit := .cycle 6 5 true (2)
theorem kid11_part831_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part831) = true := by rfl

def kid11_part832 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (5),
.cycle 1 22 true (0),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 38, 1, 132, 128, 256, 8, 128, 32, 4096, 4096],[128, 32, 2, 1, 4096, 4, 128, 32, 2, 1, 4096, 4, 4096],6144⟩,
.cycle 1 23 true (0),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 1 16 true (1),
.cycle 5 11 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.last 14 (4,true)
])
theorem kid11_part832_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part832) = true := by rfl

def kid11_part833 : Audit := .split 23 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 1 51 true (0),
.cycle 57 1 false (9),
.cycle 1 71 true (0),
.cycle 37 1 false (9),
.last 25 (4,true),
.cycle 0 27 true (0),
.cycle 1 31 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 1, 132, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 0 50 true (0),
.last 24 (4,true),
.cycle 1 31 true (0),
.cycle 25 23 true (3),
.cycle 10 16 true (0),
.cycle 0 31 true (0),
.cycle 49 1 false (9),
.cycle 32 1 false (8),
.last 25 (4,true),
.cycle 0 27 true (0),
.cycle 7 19 true (0),
.cycle 10 71 true (0),
.cycle 5 19 true (0),
.last 24 (4,true),
.last 28 (4,true)
])
theorem kid11_part833_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part833) = true := by rfl

def kid11_part834 : Audit := .cycle 1 12 true (1)
theorem kid11_part834_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part834) = true := by rfl

def kid11_part835 : Audit := .split 11 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 7 9 true (1),
.cycle 1 26 true (-2),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 0 20 true (0),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 5 9 true (1),
.last 22 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.last 12 (5,true)
])
theorem kid11_part835_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part835) = true := by rfl

def kid11_part836 : Audit := .split 11 (5,true) (byMove [
.cycle 8 7 true (2),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.cycle 21 1 false (1),
.cycle 7 9 true (1),
.last 28 (4,true),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 17 true (1),
.cycle 7 9 true (2),
.cycle 8 9 true (2),
.cycle 1 14 true (1),
.cycle 31 1 false (3),
.cycle 5 9 true (1),
.last 24 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true)
])
theorem kid11_part836_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part836) = true := by rfl

def kid11_part837 : Audit := .split 13 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.cycle 12 13 true (1),
.cycle 17 5 false (2),
.last 15 (4,true),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.cycle 7 9 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 19 true (1),
.cycle 12 11 true (2),
.cycle 12 15 true (2),
.cycle 1 16 true (1),
.cycle 4 15 true (1),
.cycle 17 5 false (2),
.last 15 (4,true),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.cycle 6 9 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true)
])
theorem kid11_part837_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part837) = true := by rfl

def kid11_part838 : Audit := .split 14 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 1 18 true (1),
.cycle 43 1 false (3),
.cycle 1 31 true (0),
.cycle 13 24 true (-2),
.last 16 (4,true),
.cycle 6 9 true (1),
.cycle 1 16 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 1, 132, 128, 256, 8, 128, 4, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 1 21 true (1),
.cycle 12 13 true (1),
.cycle 11 4 true (1),
.cycle 5 11 true (1),
.cycle 36 1 false (2),
.cycle 13 12 true (-2),
.last 16 (4,true),
.cycle 12 7 true (1),
.cycle 1 16 true (1),
.cycle 2 19 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 18 (4,true)
])
theorem kid11_part838_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part838) = true := by rfl

def kid11_part839 : Audit := .cycle 5 7 true (1)
theorem kid11_part839_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part839) = true := by rfl

def kid11_part840 : Audit := .split 15 (5,true) (byMove [
.cycle 1 20 true (0),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.cycle 1 22 true (0),
.cycle 18 1 false (0),
.last 17 (4,true),
.cycle 1 16 true (0),
.cycle 1 21 true (0),
.cycle 11 16 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 1 21 true (0),
.cycle 17 9 true (2),
.cycle 5 13 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.last 17 (4,true),
.cycle 1 16 true (0),
.cycle 7 9 true (0),
.cycle 1 18 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.last 18 (4,true)
])
theorem kid11_part840_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part840) = true := by rfl

def kid11_part841 : Audit := .split 18 (5,true) (byMove [
.last 22 (4,true),
.cycle 1 22 true (-2),
.cycle 29 15 true (1),
.last 24 (4,true),
.cycle 11 16 true (-2),
.last 20 (4,true),
.cycle 0 30 true (-2),
.cycle 19 16 true (3),
.cycle 1 47 true (-2),
.cycle 1 20 true (-2),
.last 19 (4,true),
.cycle 1 25 true (-2),
.last 30 (4,true),
.last 21 (4,true),
.cycle 0 34 true (-2),
.cycle 25 13 true (1),
.cycle 11 8 true (-2),
.last 20 (4,true),
.last 24 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 160, 1, 128, 8192, 16384, 8, 160, 33, 16777216, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 8923136, 25427968, 17301504, 16777216],[128, 32, 128, 1, 16777216, 128, 8192, 32, 16777216, 1, 16777216, 8192, 524288, 2048, 16777216, 64, 16777216, 524288, 524288, 8388608, 17301504, 262144, 16777216, 524288, 16777216],33503296⟩,
.last 20 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 673, 1, 640, 8192, 16384, 8, 160, 33, 16777216, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 11315264, 25427968, 19398656, 16777216],[128, 32, 640, 1, 16777216, 512, 8192, 32, 16777216, 1, 16777216, 32768, 524288, 2048, 16777216, 64, 16777216, 2097152, 524288, 8388608, 19398656, 262144, 16777216, 2097152, 16777216],33503296⟩,
.last 19 (4,true),
.last 22 (4,true)
])
theorem kid11_part841_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part841) = true := by rfl

def kid11_part842 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.last 18 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 20 (5,true),
.last 16 (5,true),
.cycle 0 20 true (0),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.last 18 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 19 (5,true),
.last 13 (5,true)
])
theorem kid11_part842_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part842) = true := by rfl

def kid11_part843 : Audit := .cycle 6 5 true (2)
theorem kid11_part843_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part843) = true := by rfl

def kid11_part844 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 22 true (1),
.cycle 11 7 true (2),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 14 (4,true)
])
theorem kid11_part844_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part844) = true := by rfl

def kid11_part845 : Audit := .cycle 2 11 true (1)
theorem kid11_part845_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part845) = true := by rfl

def kid11_part846 : Audit := .cycle 1 12 true (1)
theorem kid11_part846_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part846) = true := by rfl

def kid11_part847 : Audit := .split 11 (4,true) (byMove [
.cycle 1 18 true (1),
.cycle 5 11 true (1),
.cycle 9 4 true (2),
.cycle 7 7 true (2),
.last 28 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 10 2 true (2),
.cycle 5 7 true (1),
.last 22 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 14 true (1),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.last 12 (5,true)
])
theorem kid11_part847_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part847) = true := by rfl

def kid11_part848 : Audit := .split 11 (5,true) (byMove [
.last 16 (4,true),
.cycle 5 11 true (1),
.last 14 (4,true),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 17 true (1),
.cycle 7 9 true (2),
.last 22 (4,true),
.cycle 10 2 true (2),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true)
])
theorem kid11_part848_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part848) = true := by rfl

def kid11_part824 : Audit := .split 10 (2,true) (byMove [(kid11_part825),(kid11_part826),(kid11_part827),(kid11_part828),(kid11_part829),(kid11_part830),(kid11_part831),(kid11_part832),(kid11_part833),(kid11_part834),(kid11_part835),(kid11_part836),(kid11_part837),(kid11_part838),(kid11_part839),(kid11_part840),(kid11_part841),(kid11_part842),(kid11_part843),(kid11_part844),(kid11_part845),(kid11_part846),(kid11_part847),(kid11_part848)])

theorem kid11_part824_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part824) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part825),(kid11_part826),(kid11_part827),(kid11_part828),(kid11_part829),(kid11_part830),(kid11_part831),(kid11_part832),(kid11_part833),(kid11_part834),(kid11_part835),(kid11_part836),(kid11_part837),(kid11_part838),(kid11_part839),(kid11_part840),(kid11_part841),(kid11_part842),(kid11_part843),(kid11_part844),(kid11_part845),(kid11_part846),(kid11_part847),(kid11_part848)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part825_checked

  · exact kid11_part831_checked

  · exact kid11_part837_checked

  · exact kid11_part843_checked

  · exact kid11_part826_checked

  · exact kid11_part832_checked

  · exact kid11_part838_checked

  · exact kid11_part844_checked

  · exact kid11_part827_checked

  · exact kid11_part833_checked

  · exact kid11_part839_checked

  · exact kid11_part845_checked

  · exact kid11_part828_checked

  · exact kid11_part834_checked

  · exact kid11_part840_checked

  · exact kid11_part846_checked

  · exact kid11_part829_checked

  · exact kid11_part835_checked

  · exact kid11_part841_checked

  · exact kid11_part847_checked

  · exact kid11_part830_checked

  · exact kid11_part836_checked

  · exact kid11_part842_checked

  · exact kid11_part848_checked

def kid11_part849 : Audit := .cycle 5 5 true (1)
theorem kid11_part849_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part849) = true := by rfl

def kid11_part851 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.cycle 0 19 true (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 21 (5,true),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true)
])
theorem kid11_part851_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part851) = true := by rfl

def kid11_part852 : Audit := .cycle 1 14 true (1)
theorem kid11_part852_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part852) = true := by rfl

def kid11_part853 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.last 22 (2,true),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 1 18 true (0),
.cycle 25 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.cycle 25 1 false (1),
.last 26 (2,true),
.last 19 (2,true),
.cycle 1 20 true (0),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.last 19 (2,true),
.last 21 (2,true)
])
theorem kid11_part853_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part853) = true := by rfl

def kid11_part854 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.cycle 0 23 true (0),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 24 (5,true),
.last 25 (5,true),
.cycle 0 17 true (0),
.cycle 1 19 true (0),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 22 (5,true),
.cycle 5 11 true (0),
.last 20 (5,true),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 23 (5,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.last 16 (5,true)
])
theorem kid11_part854_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part854) = true := by rfl

def kid11_part855 : Audit := .cycle 13 1 false (-1)
theorem kid11_part855_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part855) = true := by rfl

def kid11_part856 : Audit := .cycle 14 1 false (-2)
theorem kid11_part856_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part856) = true := by rfl

def kid11_part857 : Audit := .cycle 6 5 true (2)
theorem kid11_part857_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part857) = true := by rfl

def kid11_part858 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (5),
.cycle 1 22 true (0),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 1 23 true (0),
.cycle 24 1 false (6),
.cycle 25 1 false (5),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 25 37 true (3),
.cycle 27 10 true (5)
])
theorem kid11_part858_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part858) = true := by rfl

def kid11_part859 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 23 (5,true),
.cycle 0 13 true (0),
.last 23 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 15 (5,true),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 20 (5,true),
.last 12 (5,true)
])
theorem kid11_part859_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part859) = true := by rfl

def kid11_part860 : Audit := .cycle 1 12 true (1)
theorem kid11_part860_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part860) = true := by rfl

def kid11_part861 : Audit := .cycle 24 1 false (6)
theorem kid11_part861_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part861) = true := by rfl

def kid11_part862 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 1 12 true (1),
.cycle 37 1 false (9),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 24 1 false (6),
.cycle 25 1 false (5),
.cycle 7 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 31 1 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (2),
.cycle 12 3 true (4)
])
theorem kid11_part862_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part862) = true := by rfl

def kid11_part863 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.last 18 (2,true),
.cycle 17 5 false (2),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 34, 64],[2, 32, 64, 1, 32, 2, 64],64⟩,
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 9 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 12 11 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 4 15 true (1),
.cycle 17 5 false (2),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 6 9 true (1),
.cycle 18 5 true (4)
])
theorem kid11_part863_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part863) = true := by rfl

def kid11_part864 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.last 16 (5,true),
.last 15 (5,true),
.last 13 (5,true),
.cycle 6 7 true (1),
.last 14 (5,true),
.last 24 (5,true),
.cycle 1 14 true (1),
.last 23 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 13 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid11_part864_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part864) = true := by rfl

def kid11_part865 : Audit := .cycle 5 7 true (1)
theorem kid11_part865_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part865) = true := by rfl

def kid11_part866 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.last 20 (2,true),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 22 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 27 1 false (1),
.cycle 22 1 false (0),
.cycle 17 9 true (2),
.last 17 (2,true),
.cycle 1 18 true (0),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 7 9 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 1 18 true (0),
.cycle 5 30 true (0)
])
theorem kid11_part866_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part866) = true := by rfl

def kid11_part867 : Audit := .cycle 13 1 false (-1)
theorem kid11_part867_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part867) = true := by rfl

def kid11_part868 : Audit := .cycle 14 1 false (-2)
theorem kid11_part868_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part868) = true := by rfl

def kid11_part869 : Audit := .cycle 6 5 true (2)
theorem kid11_part869_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part869) = true := by rfl

def kid11_part870 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 11 7 true (2),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 7 8 true (2)
])
theorem kid11_part870_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part870) = true := by rfl

def kid11_part871 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 19 (5,true),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true)
])
theorem kid11_part871_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part871) = true := by rfl

def kid11_part872 : Audit := .cycle 1 12 true (1)
theorem kid11_part872_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part872) = true := by rfl

def kid11_part873 : Audit := .cycle 11 3 true (3)
theorem kid11_part873_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part873) = true := by rfl

def kid11_part874 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 20 1 false (0),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 10 4 true (2),
.cycle 18 1 false (-2),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 8 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 7 9 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.cycle 18 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 3 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part874_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part874) = true := by rfl

def kid11_part850 : Audit := .split 10 (4,true) (byMove [(kid11_part851),(kid11_part852),(kid11_part853),(kid11_part854),(kid11_part855),(kid11_part856),(kid11_part857),(kid11_part858),(kid11_part859),(kid11_part860),(kid11_part861),(kid11_part862),(kid11_part863),(kid11_part864),(kid11_part865),(kid11_part866),(kid11_part867),(kid11_part868),(kid11_part869),(kid11_part870),(kid11_part871),(kid11_part872),(kid11_part873),(kid11_part874)])

theorem kid11_part850_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part850) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part851),(kid11_part852),(kid11_part853),(kid11_part854),(kid11_part855),(kid11_part856),(kid11_part857),(kid11_part858),(kid11_part859),(kid11_part860),(kid11_part861),(kid11_part862),(kid11_part863),(kid11_part864),(kid11_part865),(kid11_part866),(kid11_part867),(kid11_part868),(kid11_part869),(kid11_part870),(kid11_part871),(kid11_part872),(kid11_part873),(kid11_part874)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part851_checked

  · exact kid11_part857_checked

  · exact kid11_part863_checked

  · exact kid11_part869_checked

  · exact kid11_part852_checked

  · exact kid11_part858_checked

  · exact kid11_part864_checked

  · exact kid11_part870_checked

  · exact kid11_part853_checked

  · exact kid11_part859_checked

  · exact kid11_part865_checked

  · exact kid11_part871_checked

  · exact kid11_part854_checked

  · exact kid11_part860_checked

  · exact kid11_part866_checked

  · exact kid11_part872_checked

  · exact kid11_part855_checked

  · exact kid11_part861_checked

  · exact kid11_part867_checked

  · exact kid11_part873_checked

  · exact kid11_part856_checked

  · exact kid11_part862_checked

  · exact kid11_part868_checked

  · exact kid11_part874_checked

def kid11_part876 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.last 14 (4,true),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.last 18 (4,true),
.cycle 0 35 true (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.cycle 10 45 true (-1),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 12 4 true (1),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1)
])
theorem kid11_part876_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part876) = true := by rfl

def kid11_part877 : Audit := .cycle 1 14 true (1)
theorem kid11_part877_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part877) = true := by rfl

def kid11_part878 : Audit := .cycle 35 1 false (3)
theorem kid11_part878_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part878) = true := by rfl

def kid11_part879 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.last 16 (4,true),
.cycle 0 23 true (0),
.cycle 1 16 true (0),
.last 20 (4,true),
.cycle 1 41 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 1 19 true (0),
.cycle 1 21 true (0),
.cycle 1 27 true (0),
.cycle 1 25 true (0),
.cycle 5 11 true (0),
.last 16 (4,true),
.cycle 1 23 true (0),
.cycle 1 16 true (0),
.cycle 1 26 true (0),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 18 true (0)
])
theorem kid11_part879_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part879) = true := by rfl

def kid11_part880 : Audit := .cycle 13 2 false (-1)
theorem kid11_part880_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part880) = true := by rfl

def kid11_part881 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 14 2 false (2),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 14 2 false (2),
.cycle 14 2 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 17 2 false (-1),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1)
])
theorem kid11_part881_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part881) = true := by rfl

def kid11_part882 : Audit := .cycle 6 5 true (2)
theorem kid11_part882_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part882) = true := by rfl

def kid11_part883 : Audit := .cycle 1 12 true (1)
theorem kid11_part883_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part883) = true := by rfl

def kid11_part884 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 2 false (0),
.cycle 1 12 true (1),
.last 18 (4,true),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34734080, 1074790400, 1074790400, 2, 4, 32768, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 131072, 1073741824, 1048580, 128, 256, 2097152, 1048576, 1074790404, 1074790404, 2, 4, 32768, 128, 1048576, 1073741824, 1073741824],[128, 32, 4, 1, 1073741824, 4, 2, 131072, 16384, 4096, 1073741824, 16384, 33554432, 8388608, 1048576, 262144, 1073741824, 1048576, 128, 8388608, 1048576, 262144, 1073741824, 1048576, 2, 131072, 16384, 4096, 1073741824, 16384, 1073741824],1623263280⟩,
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 41 1 false (9),
.cycle 7 19 true (2),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34734084, 1074790404, 1074790404, 2, 4, 32768, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 131072, 1073741824, 1048580, 128, 256, 2097152, 1048580, 1074790404, 1074790404, 2, 4, 32768, 128, 1048580, 1073741824, 1073741824],[128, 32, 1048580, 1, 1073741824, 4, 2, 131072, 1048580, 4096, 1073741824, 16384, 33554432, 8388608, 1048580, 262144, 1073741824, 1048576, 128, 8388608, 1048580, 262144, 1073741824, 1048576, 2, 131072, 1048576, 4096, 1073741824, 16384, 1073741824],1623263280⟩,
.cycle 1 14 true (1),
.cycle 12 16 true (0),
.last 14 (4,true),
.cycle 16 2 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 32 (4,true)
])
theorem kid11_part884_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part884) = true := by rfl

def kid11_part885 : Audit := .cycle 1 12 true (1)
theorem kid11_part885_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part885) = true := by rfl

def kid11_part886 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 35 1 false (3),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 2 false (0),
.cycle 1 12 true (1),
.cycle 24 2 false (6),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 24 2 false (6),
.cycle 24 2 false (6),
.cycle 7 18 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 30 1 false (2),
.cycle 15 2 false (-1),
.cycle 16 2 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 11 8 true (3)
])
theorem kid11_part886_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part886) = true := by rfl

def kid11_part887 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 52 2 false (8),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 11 true (0),
.cycle 24 2 false (6),
.last 19 (2,true),
.cycle 33 2 false (7),
.cycle 24 2 false (6),
.cycle 24 2 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.last 20 (2,true),
.cycle 10 13 true (-1),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 11 true (0),
.cycle 37 2 false (7),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 33, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 20 10 true (2),
.cycle 37 2 false (7)
])
theorem kid11_part887_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part887) = true := by rfl

def kid11_part888 : Audit := .cycle 12 11 true (2)
theorem kid11_part888_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part888) = true := by rfl

def kid11_part889 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 10 14 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 10 13 true (1),
.cycle 10 19 true (1),
.cycle 10 4 true (1),
.cycle 22 19 true (0),
.cycle 1 20 true (1),
.last 13 (4,true),
.cycle 15 3 false (1),
.cycle 10 9 true (1),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 24 (4,true)
])
theorem kid11_part889_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part889) = true := by rfl

def kid11_part890 : Audit := .cycle 5 7 true (1)
theorem kid11_part890_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part890) = true := by rfl

def kid11_part891 : Audit := .cycle 28 1 false (2)
theorem kid11_part891_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part891) = true := by rfl

def kid11_part892 : Audit := .cycle 13 2 false (-1)
theorem kid11_part892_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part892) = true := by rfl

def kid11_part893 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 28 2 false (2),
.cycle 15 2 false (1),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 17 2 false (5),
.cycle 14 2 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 34 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 31 2 false (-1),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 23 2 false (-1),
.cycle 15 2 false (-1)
])
theorem kid11_part893_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part893) = true := by rfl

def kid11_part894 : Audit := .cycle 6 5 true (2)
theorem kid11_part894_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part894) = true := by rfl

def kid11_part895 : Audit := .cycle 1 12 true (1)
theorem kid11_part895_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part895) = true := by rfl

def kid11_part896 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 16 (4,true),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.last 16 (4,true),
.cycle 2 29 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 2 13 true (1),
.cycle 2 15 true (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1)
])
theorem kid11_part896_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part896) = true := by rfl

def kid11_part897 : Audit := .cycle 1 12 true (1)
theorem kid11_part897_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part897) = true := by rfl

def kid11_part898 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 24 45 true (-2),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 17 2 false (-1),
.cycle 9 4 true (2),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 61 2 false (9),
.cycle 8 8 true (2),
.cycle 6 12 true (2),
.cycle 13 5 true (3),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 17 2 false (-1),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 11 6 true (3)
])
theorem kid11_part898_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part898) = true := by rfl

def kid11_part899 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 10 9 true (2),
.last 15 (2,true),
.cycle 7 10 true (2),
.cycle 23 2 false (-1),
.cycle 23 2 false (-1),
.cycle 1 15 true (1),
.cycle 11 10 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 10 true (2),
.cycle 12 3 true (4),
.cycle 16 5 true (4),
.cycle 11 5 true (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 31 2 false (-1),
.cycle 10 5 true (2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 11 6 true (3),
.cycle 12 3 true (4)
])
theorem kid11_part899_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part899) = true := by rfl

def kid11_part875 : Audit := .split 10 (5,true) (byMove [(kid11_part876),(kid11_part877),(kid11_part878),(kid11_part879),(kid11_part880),(kid11_part881),(kid11_part882),(kid11_part883),(kid11_part884),(kid11_part885),(kid11_part886),(kid11_part887),(kid11_part888),(kid11_part889),(kid11_part890),(kid11_part891),(kid11_part892),(kid11_part893),(kid11_part894),(kid11_part895),(kid11_part896),(kid11_part897),(kid11_part898),(kid11_part899)])

theorem kid11_part875_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part875) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part876),(kid11_part877),(kid11_part878),(kid11_part879),(kid11_part880),(kid11_part881),(kid11_part882),(kid11_part883),(kid11_part884),(kid11_part885),(kid11_part886),(kid11_part887),(kid11_part888),(kid11_part889),(kid11_part890),(kid11_part891),(kid11_part892),(kid11_part893),(kid11_part894),(kid11_part895),(kid11_part896),(kid11_part897),(kid11_part898),(kid11_part899)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part876_checked

  · exact kid11_part882_checked

  · exact kid11_part888_checked

  · exact kid11_part894_checked

  · exact kid11_part877_checked

  · exact kid11_part883_checked

  · exact kid11_part889_checked

  · exact kid11_part895_checked

  · exact kid11_part878_checked

  · exact kid11_part884_checked

  · exact kid11_part890_checked

  · exact kid11_part896_checked

  · exact kid11_part879_checked

  · exact kid11_part885_checked

  · exact kid11_part891_checked

  · exact kid11_part897_checked

  · exact kid11_part880_checked

  · exact kid11_part886_checked

  · exact kid11_part892_checked

  · exact kid11_part898_checked

  · exact kid11_part881_checked

  · exact kid11_part887_checked

  · exact kid11_part893_checked

  · exact kid11_part899_checked

def kid11_part900 : Audit := .cycle 1 10 true (1)
theorem kid11_part900_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part900) = true := by rfl

def kid11_part901 : Audit := .cycle 7 3 true (3)
theorem kid11_part901_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part901) = true := by rfl

def kid11_part903 : Audit := .cycle 1 11 true (1)
theorem kid11_part903_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part903) = true := by rfl

def kid11_part904 : Audit := .cycle 7 4 true (3)
theorem kid11_part904_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part904) = true := by rfl

def kid11_part905 : Audit := .cycle 25 1 false (1)
theorem kid11_part905_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part905) = true := by rfl

def kid11_part906 : Audit := .cycle 0 12 true (0)
theorem kid11_part906_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part906) = true := by rfl

def kid11_part907 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 8 4 true (3),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 14 (5,true)
])
theorem kid11_part907_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part907) = true := by rfl

def kid11_part908 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 22 true (2),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 8 4 true (3),
.cycle 6 6 true (2),
.cycle 21 3 false (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 13 (4,true)
])
theorem kid11_part908_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part908) = true := by rfl

def kid11_part909 : Audit := .cycle 0 11 true (0)
theorem kid11_part909_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part909) = true := by rfl

def kid11_part910 : Audit := .cycle 1 10 true (1)
theorem kid11_part910_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part910) = true := by rfl

def kid11_part911 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 2 18 true (1),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 256, 4, 128, 256, 8, 128, 256, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 12 7 true (3),
.cycle 2 18 true (1),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.cycle 10 10 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 9 10 true (3),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 2 18 true (1),
.last 20 (4,true)
])
theorem kid11_part911_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part911) = true := by rfl

def kid11_part912 : Audit := .cycle 3 8 true (1)
theorem kid11_part912_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part912) = true := by rfl

def kid11_part913 : Audit := .cycle 2 10 true (1)
theorem kid11_part913_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part913) = true := by rfl

def kid11_part914 : Audit := .cycle 8 3 true (3)
theorem kid11_part914_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part914) = true := by rfl

def kid11_part915 : Audit := .cycle 6 5 true (2)
theorem kid11_part915_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part915) = true := by rfl

def kid11_part916 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 256, 4, 128, 256, 8, 128, 256, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],6144⟩,
.cycle 11 7 true (2),
.cycle 2 12 true (1),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 14 (4,true)
])
theorem kid11_part916_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part916) = true := by rfl

def kid11_part917 : Audit := .cycle 5 9 true (1)
theorem kid11_part917_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part917) = true := by rfl

def kid11_part918 : Audit := .cycle 1 12 true (1)
theorem kid11_part918_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part918) = true := by rfl

def kid11_part919 : Audit := .split 11 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 1 20 true (1),
.cycle 21 1 false (-1),
.cycle 7 7 true (2),
.last 20 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 24 (5,true),
.cycle 5 7 true (1),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.last 12 (5,true)
])
theorem kid11_part919_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part919) = true := by rfl

def kid11_part920 : Audit := .split 11 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 1 20 true (1),
.last 14 (4,true),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 5 true (3),
.cycle 7 9 true (2),
.cycle 21 3 false (1),
.last 14 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true)
])
theorem kid11_part920_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part920) = true := by rfl

def kid11_part921 : Audit := .cycle 0 11 true (0)
theorem kid11_part921_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part921) = true := by rfl

def kid11_part922 : Audit := .cycle 1 10 true (1)
theorem kid11_part922_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part922) = true := by rfl

def kid11_part923 : Audit := .cycle 2 9 true (1)
theorem kid11_part923_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part923) = true := by rfl

def kid11_part924 : Audit := .cycle 1 13 true (1)
theorem kid11_part924_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part924) = true := by rfl

def kid11_part925 : Audit := .cycle 2 10 true (1)
theorem kid11_part925_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part925) = true := by rfl

def kid11_part926 : Audit := .split 12 (4,true) (byMove [
.cycle 10 5 true (3),
.last 17 (5,true),
.last 25 (5,true),
.cycle 7 8 true (3),
.last 25 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 2 13 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.last 17 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 2 13 true (1),
.last 13 (5,true)
])
theorem kid11_part926_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part926) = true := by rfl

def kid11_part902 : Audit := .split 10 (2,true) (byMove [(kid11_part903),(kid11_part904),(kid11_part905),(kid11_part906),(kid11_part907),(kid11_part908),(kid11_part909),(kid11_part910),(kid11_part911),(kid11_part912),(kid11_part913),(kid11_part914),(kid11_part915),(kid11_part916),(kid11_part917),(kid11_part918),(kid11_part919),(kid11_part920),(kid11_part921),(kid11_part922),(kid11_part923),(kid11_part924),(kid11_part925),(kid11_part926)])

theorem kid11_part902_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part902) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid11_part903),(kid11_part904),(kid11_part905),(kid11_part906),(kid11_part907),(kid11_part908),(kid11_part909),(kid11_part910),(kid11_part911),(kid11_part912),(kid11_part913),(kid11_part914),(kid11_part915),(kid11_part916),(kid11_part917),(kid11_part918),(kid11_part919),(kid11_part920),(kid11_part921),(kid11_part922),(kid11_part923),(kid11_part924),(kid11_part925),(kid11_part926)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part903_checked

  · exact kid11_part909_checked

  · exact kid11_part915_checked

  · exact kid11_part921_checked

  · exact kid11_part904_checked

  · exact kid11_part910_checked

  · exact kid11_part916_checked

  · exact kid11_part922_checked

  · exact kid11_part905_checked

  · exact kid11_part911_checked

  · exact kid11_part917_checked

  · exact kid11_part923_checked

  · exact kid11_part906_checked

  · exact kid11_part912_checked

  · exact kid11_part918_checked

  · exact kid11_part924_checked

  · exact kid11_part907_checked

  · exact kid11_part913_checked

  · exact kid11_part919_checked

  · exact kid11_part925_checked

  · exact kid11_part908_checked

  · exact kid11_part914_checked

  · exact kid11_part920_checked

  · exact kid11_part926_checked

def kid11_part927 : Audit := .cycle 0 11 true (0)
theorem kid11_part927_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part927) = true := by rfl

def kid11_part929 : Audit := .cycle 1 11 true (1)
theorem kid11_part929_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part929) = true := by rfl

def kid11_part930 : Audit := .cycle 7 4 true (3)
theorem kid11_part930_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part930) = true := by rfl

def kid11_part931 : Audit := .split 11 (2,true) (byMove [
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
.cycle 12 1 true (4),
.cycle 8 4 true (3),
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
.cycle 12 1 true (4),
.last 23 (5,true)
])
theorem kid11_part931_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part931) = true := by rfl

def kid11_part932 : Audit := .cycle 0 12 true (0)
theorem kid11_part932_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part932) = true := by rfl

def kid11_part933 : Audit := .cycle 13 1 true (1)
theorem kid11_part933_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part933) = true := by rfl

def kid11_part934 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 32 1 true (-6),
.cycle 15 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (2,true),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 8 4 true (3),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 16 3 false (-1),
.cycle 15 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 17 6 false (1)
])
theorem kid11_part934_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part934) = true := by rfl

def kid11_part935 : Audit := .cycle 0 11 true (0)
theorem kid11_part935_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part935) = true := by rfl

def kid11_part936 : Audit := .cycle 1 10 true (1)
theorem kid11_part936_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part936) = true := by rfl

def kid11_part937 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 19 1 true (5),
.last 21 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 28 (2,true),
.cycle 12 7 true (3),
.cycle 19 1 true (7),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 9 10 true (3),
.last 21 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 19 1 true (7),
.last 21 (2,true)
])
theorem kid11_part937_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part937) = true := by rfl

def kid11_part938 : Audit := .cycle 3 8 true (1)
theorem kid11_part938_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part938) = true := by rfl

def kid11_part939 : Audit := .cycle 11 1 true (5)
theorem kid11_part939_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part939) = true := by rfl

def kid11_part940 : Audit := .cycle 8 3 true (3)
theorem kid11_part940_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part940) = true := by rfl

def kid11_part941 : Audit := .cycle 6 5 true (2)
theorem kid11_part941_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part941) = true := by rfl

def kid11_part942 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 11 7 true (2),
.cycle 13 1 true (5),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (3),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.last 16 (2,true)
])
theorem kid11_part942_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part942) = true := by rfl

def kid11_part943 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
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
])
theorem kid11_part943_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part943) = true := by rfl

def kid11_part944 : Audit := .cycle 1 12 true (1)
theorem kid11_part944_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part944) = true := by rfl

def kid11_part945 : Audit := .cycle 15 3 false (1)
theorem kid11_part945_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part945) = true := by rfl

def kid11_part946 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 14 9 false (0),
.cycle 15 4 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 16 5 false (0),
.cycle 8 5 true (3),
.cycle 7 9 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 16 3 false (-1),
.cycle 15 4 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 11 5 true (3)
])
theorem kid11_part946_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part946) = true := by rfl

def kid11_part947 : Audit := .cycle 0 11 true (0)
theorem kid11_part947_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part947) = true := by rfl

def kid11_part948 : Audit := .cycle 1 10 true (1)
theorem kid11_part948_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part948) = true := by rfl

def kid11_part949 : Audit := .cycle 2 9 true (1)
theorem kid11_part949_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part949) = true := by rfl

def kid11_part950 : Audit := .cycle 1 13 true (1)
theorem kid11_part950_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part950) = true := by rfl

def kid11_part951 : Audit := .cycle 11 1 true (5)
theorem kid11_part951_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part951) = true := by rfl

def kid11_part952 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 19 8 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 31 (2,true),
.cycle 3 11 true (1),
.cycle 14 1 true (6),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 19 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 1 true (6),
.cycle 11 3 true (4)
])
theorem kid11_part952_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part952) = true := by rfl

def kid11_part928 : Audit := .split 10 (4,true) (byMove [(kid11_part929),(kid11_part930),(kid11_part931),(kid11_part932),(kid11_part933),(kid11_part934),(kid11_part935),(kid11_part936),(kid11_part937),(kid11_part938),(kid11_part939),(kid11_part940),(kid11_part941),(kid11_part942),(kid11_part943),(kid11_part944),(kid11_part945),(kid11_part946),(kid11_part947),(kid11_part948),(kid11_part949),(kid11_part950),(kid11_part951),(kid11_part952)])

theorem kid11_part928_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part928) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part929),(kid11_part930),(kid11_part931),(kid11_part932),(kid11_part933),(kid11_part934),(kid11_part935),(kid11_part936),(kid11_part937),(kid11_part938),(kid11_part939),(kid11_part940),(kid11_part941),(kid11_part942),(kid11_part943),(kid11_part944),(kid11_part945),(kid11_part946),(kid11_part947),(kid11_part948),(kid11_part949),(kid11_part950),(kid11_part951),(kid11_part952)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part929_checked

  · exact kid11_part935_checked

  · exact kid11_part941_checked

  · exact kid11_part947_checked

  · exact kid11_part930_checked

  · exact kid11_part936_checked

  · exact kid11_part942_checked

  · exact kid11_part948_checked

  · exact kid11_part931_checked

  · exact kid11_part937_checked

  · exact kid11_part943_checked

  · exact kid11_part949_checked

  · exact kid11_part932_checked

  · exact kid11_part938_checked

  · exact kid11_part944_checked

  · exact kid11_part950_checked

  · exact kid11_part933_checked

  · exact kid11_part939_checked

  · exact kid11_part945_checked

  · exact kid11_part951_checked

  · exact kid11_part934_checked

  · exact kid11_part940_checked

  · exact kid11_part946_checked

  · exact kid11_part952_checked

def kid11_part954 : Audit := .cycle 1 11 true (1)
theorem kid11_part954_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part954) = true := by rfl

def kid11_part955 : Audit := .cycle 7 4 true (3)
theorem kid11_part955_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part955) = true := by rfl

def kid11_part956 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 8 4 true (3),
.cycle 6 6 true (2),
.cycle 35 1 false (3),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 32 1 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.last 13 (4,true)
])
theorem kid11_part956_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part956) = true := by rfl

def kid11_part957 : Audit := .cycle 0 12 true (0)
theorem kid11_part957_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part957) = true := by rfl

def kid11_part958 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.cycle 19 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 11 4 true (3),
.cycle 8 4 true (3),
.cycle 6 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.cycle 19 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 4 true (3),
.cycle 10 4 true (3)
])
theorem kid11_part958_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part958) = true := by rfl

def kid11_part959 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 4 false (-1),
.cycle 1 15 true (0),
.cycle 16 4 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 4 true (0),
.cycle 15 4 false (1),
.cycle 12 5 false (2),
.last 16 (2,true),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 4 false (0),
.cycle 15 4 false (-1),
.cycle 1 15 true (0),
.cycle 19 4 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 4 true (0),
.cycle 15 4 false (1)
])
theorem kid11_part959_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part959) = true := by rfl

def kid11_part960 : Audit := .cycle 0 11 true (0)
theorem kid11_part960_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part960) = true := by rfl

def kid11_part961 : Audit := .cycle 1 10 true (1)
theorem kid11_part961_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part961) = true := by rfl

def kid11_part962 : Audit := .split 28 (2,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 11 18 true (3),
.cycle 3 26 true (1),
.last 31 (4,true),
.cycle 8 21 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 128, 2048, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],7184⟩,
.cycle 20 9 true (4),
.last 31 (4,true),
.cycle 8 21 true (3),
.cycle 7 23 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 128, 2048, 4096, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],7184⟩,
.cycle 0 31 true (0),
.cycle 13 16 true (3),
.cycle 9 20 true (3),
.last 34 (4,true),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.last 31 (4,true),
.last 30 (4,true)
])
theorem kid11_part962_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part962) = true := by rfl

def kid11_part963 : Audit := .cycle 3 8 true (1)
theorem kid11_part963_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part963) = true := by rfl

def kid11_part964 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 20 true (3),
.last 18 (2,true),
.cycle 22 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4),
.cycle 10 6 true (4),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 14 16 true (3),
.cycle 9 8 true (3),
.cycle 25 6 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4)
])
theorem kid11_part964_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part964) = true := by rfl

def kid11_part965 : Audit := .cycle 8 3 true (3)
theorem kid11_part965_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part965) = true := by rfl

def kid11_part966 : Audit := .cycle 6 5 true (2)
theorem kid11_part966_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part966) = true := by rfl

def kid11_part967 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (3),
.cycle 3 12 true (1),
.last 17 (4,true),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 11 4 true (3),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 17 (4,true),
.last 16 (4,true)
])
theorem kid11_part967_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part967) = true := by rfl

def kid11_part968 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 1 24 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
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
])
theorem kid11_part968_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part968) = true := by rfl

def kid11_part969 : Audit := .cycle 1 12 true (1)
theorem kid11_part969_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part969) = true := by rfl

def kid11_part970 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 16 3 false (0),
.cycle 17 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 4 true (3),
.cycle 9 4 true (3),
.cycle 9 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 16 3 false (0),
.cycle 17 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 4 true (3),
.cycle 10 2 true (3)
])
theorem kid11_part970_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part970) = true := by rfl

def kid11_part971 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 1 26 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 4 false (-1),
.cycle 30 4 false (4),
.cycle 16 4 false (2),
.last 15 (2,true),
.cycle 1 22 true (0),
.cycle 17 4 true (3),
.cycle 15 4 false (1),
.cycle 12 5 false (2),
.last 16 (2,true),
.cycle 36 4 false (4),
.cycle 15 1 false (-1),
.cycle 15 4 false (0),
.cycle 15 4 false (-1),
.cycle 33 4 false (1),
.cycle 12 4 true (0),
.last 15 (2,true),
.cycle 1 22 true (0),
.cycle 17 4 true (3),
.cycle 15 4 false (1)
])
theorem kid11_part971_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part971) = true := by rfl

def kid11_part972 : Audit := .cycle 0 11 true (0)
theorem kid11_part972_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part972) = true := by rfl

def kid11_part973 : Audit := .cycle 1 10 true (1)
theorem kid11_part973_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part973) = true := by rfl

def kid11_part974 : Audit := .cycle 2 9 true (1)
theorem kid11_part974_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part974) = true := by rfl

def kid11_part975 : Audit := .cycle 1 13 true (1)
theorem kid11_part975_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part975) = true := by rfl

def kid11_part976 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 7 12 true (3),
.last 14 (2,true),
.cycle 7 9 true (3),
.cycle 20 3 false (0),
.cycle 9 6 true (3),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4),
.cycle 10 6 true (4),
.cycle 10 8 true (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 5 false (2),
.cycle 13 2 true (4),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4)
])
theorem kid11_part976_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part976) = true := by rfl

def kid11_part977 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 10 7 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 18 3 false (0),
.cycle 19 8 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 4 true (4),
.cycle 10 3 true (4),
.cycle 14 5 true (4),
.cycle 10 5 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 10 5 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 4 true (4),
.cycle 10 3 true (4)
])
theorem kid11_part977_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part977) = true := by rfl

def kid11_part953 : Audit := .split 10 (5,true) (byMove [(kid11_part954),(kid11_part955),(kid11_part956),(kid11_part957),(kid11_part958),(kid11_part959),(kid11_part960),(kid11_part961),(kid11_part962),(kid11_part963),(kid11_part964),(kid11_part965),(kid11_part966),(kid11_part967),(kid11_part968),(kid11_part969),(kid11_part970),(kid11_part971),(kid11_part972),(kid11_part973),(kid11_part974),(kid11_part975),(kid11_part976),(kid11_part977)])

theorem kid11_part953_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part953) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid11_part954),(kid11_part955),(kid11_part956),(kid11_part957),(kid11_part958),(kid11_part959),(kid11_part960),(kid11_part961),(kid11_part962),(kid11_part963),(kid11_part964),(kid11_part965),(kid11_part966),(kid11_part967),(kid11_part968),(kid11_part969),(kid11_part970),(kid11_part971),(kid11_part972),(kid11_part973),(kid11_part974),(kid11_part975),(kid11_part976),(kid11_part977)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part954_checked

  · exact kid11_part960_checked

  · exact kid11_part966_checked

  · exact kid11_part972_checked

  · exact kid11_part955_checked

  · exact kid11_part961_checked

  · exact kid11_part967_checked

  · exact kid11_part973_checked

  · exact kid11_part956_checked

  · exact kid11_part962_checked

  · exact kid11_part968_checked

  · exact kid11_part974_checked

  · exact kid11_part957_checked

  · exact kid11_part963_checked

  · exact kid11_part969_checked

  · exact kid11_part975_checked

  · exact kid11_part958_checked

  · exact kid11_part964_checked

  · exact kid11_part970_checked

  · exact kid11_part976_checked

  · exact kid11_part959_checked

  · exact kid11_part965_checked

  · exact kid11_part971_checked

  · exact kid11_part977_checked

def kid11_part689 : Audit := .split 9 (4,false) (byMove [(kid11_part690),(kid11_part715),(kid11_part716),(kid11_part741),(kid11_part742),(kid11_part743),(kid11_part768),(kid11_part769),(kid11_part770),(kid11_part795),(kid11_part796),(kid11_part797),(kid11_part798),(kid11_part799),(kid11_part824),(kid11_part849),(kid11_part850),(kid11_part875),(kid11_part900),(kid11_part901),(kid11_part902),(kid11_part927),(kid11_part928),(kid11_part953)])

theorem kid11_part689_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (kid11_part689) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part690),(kid11_part715),(kid11_part716),(kid11_part741),(kid11_part742),(kid11_part743),(kid11_part768),(kid11_part769),(kid11_part770),(kid11_part795),(kid11_part796),(kid11_part797),(kid11_part798),(kid11_part799),(kid11_part824),(kid11_part849),(kid11_part850),(kid11_part875),(kid11_part900),(kid11_part901),(kid11_part902),(kid11_part927),(kid11_part928),(kid11_part953)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part690_checked

  · exact kid11_part768_checked

  · exact kid11_part798_checked

  · exact kid11_part900_checked

  · exact kid11_part715_checked

  · exact kid11_part769_checked

  · exact kid11_part799_checked

  · exact kid11_part901_checked

  · exact kid11_part716_checked

  · exact kid11_part770_checked

  · exact kid11_part824_checked

  · exact kid11_part902_checked

  · exact kid11_part741_checked

  · exact kid11_part795_checked

  · exact kid11_part849_checked

  · exact kid11_part927_checked

  · exact kid11_part742_checked

  · exact kid11_part796_checked

  · exact kid11_part850_checked

  · exact kid11_part928_checked

  · exact kid11_part743_checked

  · exact kid11_part797_checked

  · exact kid11_part875_checked

  · exact kid11_part953_checked

def kid11_part979 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 24 1 false (0),
.cycle 18 1 false (0),
.cycle 0 21 true (0),
.last 17 (4,false),
.cycle 0 25 true (0),
.cycle 7 9 true (1),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.last 15 (4,false),
.cycle 19 7 false (2),
.cycle 21 9 false (2),
.cycle 0 21 true (0),
.last 29 (4,false),
.cycle 1 21 true (1),
.last 17 (4,false),
.cycle 17 5 false (2),
.cycle 12 9 true (2),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 12 6 true (1)
]),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 0 24 true (0),
.cycle 0 35 true (0),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.last 20 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 27 (4,false),
.cycle 0 22 true (0),
.last 15 (4,false),
.cycle 0 24 true (0),
.cycle 12 9 true (2),
.last 17 (4,false),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 12 6 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.last 20 (4,false)
]),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.cycle 10 45 true (-1),
.cycle 5 9 true (1),
.split 14 (4,true) (byMove [
.cycle 12 4 true (1),
.cycle 24 1 false (0),
.cycle 18 1 false (0),
.cycle 0 19 true (0),
.last 17 (4,false),
.cycle 1 20 true (0),
.cycle 6 9 true (1),
.cycle 0 17 true (0),
.last 16 (4,false),
.cycle 1 16 true (1),
.last 17 (4,false),
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.cycle 10 6 true (1),
.last 51 (4,false),
.cycle 0 19 true (0),
.last 17 (4,false),
.cycle 17 5 false (2),
.cycle 12 9 true (2),
.cycle 0 17 true (0),
.cycle 13 2 true (2),
.cycle 1 16 true (1),
.last 17 (4,false),
.cycle 1 21 true (1)
]),
.cycle 12 4 true (1),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 12 8 true (1),
.last 16 (4,false),
.cycle 0 16 true (0),
.last 19 (4,false),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 12 7 true (2),
.cycle 12 9 true (2),
.cycle 0 17 true (0),
.cycle 13 2 true (3),
.cycle 1 16 true (1),
.last 19 (4,false),
.last 19 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.last 20 (4,false)
]),
.cycle 1 15 true (1)
])
theorem kid11_part979_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part979) = true := by rfl

def kid11_part980 : Audit := .cycle 1 14 true (1)
theorem kid11_part980_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part980) = true := by rfl

def kid11_part981 : Audit := .cycle 35 1 false (3)
theorem kid11_part981_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part981) = true := by rfl

def kid11_part982 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.split 16 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 0 23 true (0),
.last 18 (4,false),
.cycle 18 1 false (0),
.cycle 7 11 true (0),
.cycle 1 43 true (0),
.cycle 0 19 true (0),
.cycle 1 25 true (0),
.last 17 (4,false),
.cycle 20 1 false (0),
.cycle 22 1 false (0),
.cycle 19 1 false (1),
.last 18 (4,false),
.cycle 1 23 true (0),
.last 18 (4,false),
.cycle 18 1 false (0),
.cycle 1 28 true (0),
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.cycle 4 13 true (0),
.last 17 (4,false),
.cycle 1 25 true (0)
]),
.cycle 0 23 true (0),
.cycle 1 16 true (0),
.cycle 3 67 true (0),
.cycle 1 41 true (0),
.cycle 0 17 true (0),
.split 16 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.last 17 (4,false),
.cycle 25 1 false (1),
.cycle 0 17 true (0),
.cycle 1 40 true (0),
.last 31 (4,false),
.cycle 1 26 true (0),
.last 17 (4,false),
.last 30 (4,false),
.cycle 1 28 true (0),
.last 19 (4,false),
.cycle 0 19 true (0),
.cycle 4 13 true (0),
.last 17 (4,false),
.cycle 1 25 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.proven (BB6.Agent11Raw39Pumps.M1093.table) (fun m hm => BB6.Agent11Raw39Pumps.M1093.never m hm),
.cycle 1 19 true (0),
.last 17 (4,false),
.last 24 (4,false)
]),
.cycle 1 19 true (0),
.cycle 1 21 true (0),
.cycle 1 27 true (0),
.cycle 1 25 true (0),
.cycle 5 11 true (0),
.split 16 (4,true) (byMove [
.cycle 13 4 true (1),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 1 23 true (0),
.last 18 (4,false),
.cycle 18 1 false (0),
.cycle 6 11 true (0),
.cycle 27 1 false (1),
.last 18 (4,false),
.cycle 1 18 true (0),
.last 19 (4,false),
.cycle 1 27 true (0),
.cycle 1 31 true (0),
.cycle 19 1 false (1),
.last 18 (4,false),
.cycle 1 23 true (0),
.last 18 (4,false),
.cycle 18 1 false (0),
.cycle 1 28 true (0),
.cycle 1 21 true (0),
.cycle 15 2 true (2),
.cycle 1 18 true (0),
.last 19 (4,false),
.cycle 7 13 true (0)
]),
.cycle 1 23 true (0),
.cycle 1 16 true (0),
.cycle 1 26 true (0),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.split 16 (4,true) (byMove [
.cycle 1 17 true (0),
.cycle 1 27 true (0),
.last 18 (4,false),
.cycle 0 18 true (0),
.last 20 (4,false),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 3 40 true (0),
.cycle 1 27 true (0),
.cycle 3 14 true (0),
.last 17 (4,false),
.cycle 1 26 true (0),
.cycle 1 28 true (0),
.cycle 1 21 true (0),
.cycle 15 2 true (3),
.cycle 1 18 true (0),
.last 20 (4,false),
.cycle 7 13 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.last 17 (4,false),
.cycle 7 14 true (0)
]),
.cycle 0 18 true (0)
])
theorem kid11_part982_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part982) = true := by rfl

def kid11_part984 : Audit := .cycle 1 16 true (0)
theorem kid11_part984_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part984) = true := by rfl

def kid11_part985 : Audit := .cycle 13 1 false (1)
theorem kid11_part985_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part985) = true := by rfl

def kid11_part986 : Audit := .split 12 (2,true) (byMove [
.cycle 14 35 true (0),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 29 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.cycle 42 1 false (2),
.cycle 0 19 true (0),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
])
theorem kid11_part986_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part986) = true := by rfl

def kid11_part987 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 1 16 true (0),
.last 21 (4,true),
.cycle 0 41 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 5 11 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 1 16 true (0),
.last 20 (4,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid11_part987_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part987) = true := by rfl

def kid11_part988 : Audit := .split 12 (4,true) (byMove [
.cycle 14 35 true (0),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 1 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 1 16 true (0),
.cycle 40 1 false (2),
.last 17 (2,true),
.cycle 11 2 true (0),
.cycle 15 1 false (-1)
])
theorem kid11_part988_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part988) = true := by rfl

def kid11_part989 : Audit := .cycle 14 1 false (-2)
theorem kid11_part989_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part989) = true := by rfl

def kid11_part990 : Audit := .cycle 0 16 true (0)
theorem kid11_part990_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part990) = true := by rfl

def kid11_part991 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 23 1 false (1),
.cycle 29 1 false (1),
.cycle 7 9 true (1),
.last 14 (4,true),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 1 24 true (1),
.cycle 1 35 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 1 17 true (1),
.cycle 1 21 true (1),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 10 4 true (1),
.cycle 1 14 true (1),
.last 18 (4,true),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid11_part991_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part991) = true := by rfl

def kid11_part992 : Audit := .cycle 1 14 true (1)
theorem kid11_part992_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part992) = true := by rfl

def kid11_part993 : Audit := .cycle 35 1 false (3)
theorem kid11_part993_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part993) = true := by rfl

def kid11_part994 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 33 1 true (3),
.cycle 25 1 false (1),
.cycle 17 1 true (3),
.cycle 20 1 false (0),
.cycle 1 14 true (1),
.cycle 30 1 false (6),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 true (5),
.cycle 15 1 true (3),
.cycle 17 1 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 29 1 true (3),
.cycle 12 2 true (2),
.cycle 20 1 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 true (5),
.cycle 15 5 true (2)
])
theorem kid11_part994_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part994) = true := by rfl

def kid11_part995 : Audit := .cycle 16 1 false (0)
theorem kid11_part995_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part995) = true := by rfl

def kid11_part996 : Audit := .cycle 13 6 false (2)
theorem kid11_part996_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part996) = true := by rfl

def kid11_part997 : Audit := .split 16 (2,true) (byMove [
.cycle 1 70 false (5),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 1 22 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 1 20 true (-1),
.cycle 1 20 true (-1),
.cycle 10 14 true (-1),
.cycle 10 23 false (2),
.last 23 (4,true),
.cycle 13 6 false (1),
.cycle 13 8 false (1),
.cycle 12 5 false (1),
.cycle 1 24 true (-2),
.cycle 1 22 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 115 82 false (7),
.cycle 1 20 true (-1),
.cycle 2 62 false (5),
.cycle 0 23 true (-1),
.cycle 10 9 false (2),
.last 19 (4,true)
])
theorem kid11_part997_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part997) = true := by rfl

def kid11_part998 : Audit := .split 12 (2,true) (byMove [
.cycle 1 20 true (-1),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 16 true (-2),
.cycle 13 1 false (-1),
.cycle 1 16 true (0),
.cycle 14 1 false (2),
.cycle 1 16 true (0),
.cycle 0 20 true (0),
.last 13 (4,true),
.cycle 0 30 true (-1),
.cycle 10 5 false (2),
.cycle 10 20 true (-2),
.cycle 1 29 true (-1),
.cycle 13 1 false (-1),
.cycle 10 16 true (-2),
.cycle 13 1 false (-1),
.cycle 1 16 true (0),
.cycle 10 12 true (-2),
.cycle 1 16 true (0),
.cycle 0 20 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid11_part998_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part998) = true := by rfl

def kid11_part999 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 1 16 true (0),
.last 21 (4,true),
.cycle 1 41 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 1 19 true (0),
.cycle 1 21 true (0),
.cycle 1 27 true (0),
.cycle 1 25 true (0),
.cycle 5 11 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 1 16 true (0),
.last 20 (4,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid11_part999_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part999) = true := by rfl

def kid11_part1000 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 14 1 false (2),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 17 1 false (-1),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 17 3 true (3),
.cycle 17 1 false (-1)
])
theorem kid11_part1000_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1000) = true := by rfl

def kid11_part1001 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1001_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1001) = true := by rfl

def kid11_part1002 : Audit := .cycle 0 16 true (0)
theorem kid11_part1002_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1002) = true := by rfl

def kid11_part1003 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.last 18 (4,true),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 19 (4,true),
.cycle 1 35 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 1 17 true (1),
.cycle 1 21 true (1),
.cycle 10 45 true (-1),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 18 (4,true),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid11_part1003_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1003) = true := by rfl

def kid11_part1004 : Audit := .cycle 1 14 true (1)
theorem kid11_part1004_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1004) = true := by rfl

def kid11_part1005 : Audit := .cycle 1 20 true (1)
theorem kid11_part1005_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1005) = true := by rfl

def kid11_part1006 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 10 16 true (-1),
.last 14 (2,true),
.cycle 7 9 true (1),
.cycle 28 1 true (-2),
.cycle 28 1 true (-2),
.cycle 1 14 true (1),
.last 21 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 true (5),
.cycle 15 1 true (3),
.cycle 17 1 true (3),
.cycle 21 1 true (3),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.cycle 22 1 false (-2),
.cycle 1 14 true (1),
.last 20 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 true (5),
.cycle 17 13 false (3)
])
theorem kid11_part1006_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1006) = true := by rfl

def kid11_part1007 : Audit := .split 14 (4,true) (byMove [
.cycle 0 46 true (-1),
.cycle 10 12 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 15 1 false (-1),
.cycle 32 3 false (4),
.last 16 (2,true),
.cycle 20 3 false (4),
.cycle 15 1 false (1),
.cycle 24 3 false (5),
.cycle 15 1 false (1),
.cycle 18 3 false (0),
.last 16 (2,true),
.cycle 38 3 false (4),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 19 13 true (1),
.last 16 (2,true),
.cycle 0 40 true (0),
.cycle 38 3 false (4),
.cycle 19 7 true (2),
.cycle 15 3 false (1)
])
theorem kid11_part1007_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1007) = true := by rfl

def kid11_part983 : Audit := .split 11 (4,false) (byMove [(kid11_part984),(kid11_part985),(kid11_part986),(kid11_part987),(kid11_part988),(kid11_part989),(kid11_part990),(kid11_part991),(kid11_part992),(kid11_part993),(kid11_part994),(kid11_part995),(kid11_part996),(kid11_part997),(kid11_part998),(kid11_part999),(kid11_part1000),(kid11_part1001),(kid11_part1002),(kid11_part1003),(kid11_part1004),(kid11_part1005),(kid11_part1006),(kid11_part1007)])

theorem kid11_part983_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part983) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part984),(kid11_part985),(kid11_part986),(kid11_part987),(kid11_part988),(kid11_part989),(kid11_part990),(kid11_part991),(kid11_part992),(kid11_part993),(kid11_part994),(kid11_part995),(kid11_part996),(kid11_part997),(kid11_part998),(kid11_part999),(kid11_part1000),(kid11_part1001),(kid11_part1002),(kid11_part1003),(kid11_part1004),(kid11_part1005),(kid11_part1006),(kid11_part1007)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part984_checked

  · exact kid11_part990_checked

  · exact kid11_part996_checked

  · exact kid11_part1002_checked

  · exact kid11_part985_checked

  · exact kid11_part991_checked

  · exact kid11_part997_checked

  · exact kid11_part1003_checked

  · exact kid11_part986_checked

  · exact kid11_part992_checked

  · exact kid11_part998_checked

  · exact kid11_part1004_checked

  · exact kid11_part987_checked

  · exact kid11_part993_checked

  · exact kid11_part999_checked

  · exact kid11_part1005_checked

  · exact kid11_part988_checked

  · exact kid11_part994_checked

  · exact kid11_part1000_checked

  · exact kid11_part1006_checked

  · exact kid11_part989_checked

  · exact kid11_part995_checked

  · exact kid11_part1001_checked

  · exact kid11_part1007_checked

def kid11_part1008 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1008_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1008) = true := by rfl

def kid11_part1009 : Audit := .cycle 6 5 true (2)
theorem kid11_part1009_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1009) = true := by rfl

def kid11_part1010 : Audit := .cycle 1 12 true (1)
theorem kid11_part1010_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1010) = true := by rfl

def kid11_part1011 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 31 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.last 14 (4,true),
.cycle 19 1 false (1),
.cycle 21 7 false (2),
.last 15 (4,true),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.cycle 9 4 true (2)
]),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 24 1 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,false),
.last 30 (4,false),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (4,false),
.cycle 10 11 true (0),
.last 13 (4,false),
.cycle 24 1 false (6),
.cycle 7 7 true (2),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 21 (4,false),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 41 1 false (9),
.cycle 7 19 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 1 14 true (1),
.cycle 12 16 true (0),
.split 12 (4,false) (byMove [
.last 16 (4,true),
.cycle 1 16 true (1),
.cycle 14 18 true (0),
.last 18 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 53 1 false (9),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4096, 1, 4096, 4, 4096],4096⟩,
.cycle 14 14 true (2),
.last 15 (4,true),
.cycle 5 9 true (1),
.cycle 13 16 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 7 19 true (2),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 13 20 true (3)
]),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 10 13 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.last 31 (4,false),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 29 3 true (7)
])
theorem kid11_part1011_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1011) = true := by rfl

def kid11_part1012 : Audit := .cycle 1 12 true (1)
theorem kid11_part1012_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1012) = true := by rfl

def kid11_part1014 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (4,false),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.last 17 (4,false),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 13 4 true (2),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 0 18 true (0)
])
theorem kid11_part1014_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1014) = true := by rfl

def kid11_part1015 : Audit := .cycle 0 15 true (0)
theorem kid11_part1015_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1015) = true := by rfl

def kid11_part1016 : Audit := .split 29 (4,false) (byMove [
.cycle 0 30 true (0),
.cycle 10 39 true (0),
.cycle 21 9 true (1),
.cycle 40 1 false (4),
.cycle 34 1 false (2),
.cycle 35 1 false (3),
.cycle 0 30 true (0),
.cycle 10 59 true (0),
.cycle 10 29 true (0),
.cycle 13 18 true (0),
.cycle 29 1 true (5),
.cycle 37 1 false (3),
.cycle 7 24 true (0),
.last 31 (2,true),
.cycle 0 32 true (0),
.cycle 23 7 true (1),
.cycle 34 1 false (2),
.cycle 35 1 false (3),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 10 48 true (0),
.cycle 1 32 true (0),
.cycle 29 1 true (5),
.cycle 13 22 true (0)
])
theorem kid11_part1016_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1016) = true := by rfl

def kid11_part1017 : Audit := .cycle 21 1 false (1)
theorem kid11_part1017_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1017) = true := by rfl

def kid11_part1018 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 21 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 15 1 true (3),
.cycle 19 1 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 17 1 true (1),
.cycle 9 4 true (2)
])
theorem kid11_part1018_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1018) = true := by rfl

def kid11_part1019 : Audit := .cycle 16 1 false (0)
theorem kid11_part1019_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1019) = true := by rfl

def kid11_part1020 : Audit := .cycle 1 12 true (1)
theorem kid11_part1020_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1020) = true := by rfl

def kid11_part1021 : Audit := .cycle 24 1 false (6)
theorem kid11_part1021_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1021) = true := by rfl

def kid11_part1022 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 22 true (0),
.last 20 (4,false),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 16777216, 4, 128, 256, 32768, 128, 16777216, 1048580, 128, 256, 2097152, 131072, 16777216, 4, 128, 256, 8, 4194304, 16777216, 4, 16777216],[128, 32, 4, 1, 4, 16, 128, 131072, 16384, 4096, 16384, 65536, 128, 8388608, 1048576, 262144, 1048576, 4194304, 128, 32, 4, 1, 4, 16, 16777216],23151632⟩,
.cycle 10 11 true (0),
.last 13 (4,false),
.cycle 24 1 false (6),
.cycle 7 7 true (2),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 10 20 true (0),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 10 41 true (0)
])
theorem kid11_part1022_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1022) = true := by rfl

def kid11_part1023 : Audit := .cycle 0 13 true (0)
theorem kid11_part1023_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1023) = true := by rfl

def kid11_part1024 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (0),
.cycle 43 1 false (5),
.cycle 19 1 false (1),
.cycle 24 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 13 1 true (5),
.cycle 28 1 false (8),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.cycle 25 1 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 12 4 true (4)
])
theorem kid11_part1024_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1024) = true := by rfl

def kid11_part1025 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (0),
.cycle 33 1 false (5),
.cycle 19 1 false (1),
.cycle 24 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 48, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 41 1 false (9),
.cycle 13 1 true (5),
.cycle 28 1 false (8),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 32 1 false (8)
])
theorem kid11_part1025_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1025) = true := by rfl

def kid11_part1026 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 9 true (2),
.cycle 3 13 true (1),
.cycle 33 13 false (3),
.cycle 8 8 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 10 15 true (2),
.cycle 7 19 true (2),
.cycle 15 1 true (5),
.cycle 10 14 true (2),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 13 7 true (2),
.cycle 10 11 true (1),
.cycle 7 18 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 15 1 true (5),
.cycle 7 13 true (2)
])
theorem kid11_part1026_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1026) = true := by rfl

def kid11_part1027 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 23 1 false (1),
.cycle 29 1 false (1),
.cycle 7 9 true (2),
.last 20 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.last 24 (4,false),
.last 35 (4,false),
.cycle 0 15 true (0),
.last 17 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 20 3 false (2),
.cycle 10 4 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 17 (4,false),
.last 15 (4,false)
])
theorem kid11_part1027_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1027) = true := by rfl

def kid11_part1028 : Audit := .cycle 1 14 true (1)
theorem kid11_part1028_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1028) = true := by rfl

def kid11_part1029 : Audit := .split 25 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 10 33 true (0),
.cycle 19 9 true (1),
.cycle 35 1 false (3),
.cycle 29 1 false (1),
.cycle 30 1 false (2),
.cycle 0 26 true (0),
.cycle 10 49 true (0),
.cycle 10 25 true (0),
.cycle 12 16 true (0),
.cycle 25 1 true (5),
.cycle 32 1 false (2),
.cycle 7 20 true (0),
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 19 7 true (1),
.cycle 29 1 false (1),
.cycle 30 1 false (2),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 10 40 true (0),
.cycle 1 28 true (0),
.cycle 25 1 true (5),
.cycle 12 18 true (0)
])
theorem kid11_part1029_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1029) = true := by rfl

def kid11_part1030 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 23 9 true (1),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 44 1 false (8),
.cycle 7 16 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 7 true (1),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 17 3 false (1),
.cycle 13 6 true (3)
])
theorem kid11_part1030_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1030) = true := by rfl

def kid11_part1031 : Audit := .cycle 16 1 false (0)
theorem kid11_part1031_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1031) = true := by rfl

def kid11_part1032 : Audit := .cycle 1 12 true (1)
theorem kid11_part1032_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1032) = true := by rfl

def kid11_part1033 : Audit := .cycle 7 5 true (2)
theorem kid11_part1033_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1033) = true := by rfl

def kid11_part1034 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 2 14 true (1)
])
theorem kid11_part1034_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1034) = true := by rfl

def kid11_part1035 : Audit := .cycle 0 13 true (0)
theorem kid11_part1035_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1035) = true := by rfl

def kid11_part1036 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 84 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 22 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.last 18 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.cycle 12 3 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 12 4 true (4)
])
theorem kid11_part1036_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1036) = true := by rfl

def kid11_part1037 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 15 3 true (3),
.cycle 14 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 22 3 true (6),
.cycle 29 3 true (7),
.cycle 13 1 true (5),
.cycle 19 3 true (5),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 16 3 true (4),
.cycle 9 5 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 14 3 true (5)
])
theorem kid11_part1037_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1037) = true := by rfl

def kid11_part1013 : Audit := .split 11 (4,true) (byMove [(kid11_part1014),(kid11_part1015),(kid11_part1016),(kid11_part1017),(kid11_part1018),(kid11_part1019),(kid11_part1020),(kid11_part1021),(kid11_part1022),(kid11_part1023),(kid11_part1024),(kid11_part1025),(kid11_part1026),(kid11_part1027),(kid11_part1028),(kid11_part1029),(kid11_part1030),(kid11_part1031),(kid11_part1032),(kid11_part1033),(kid11_part1034),(kid11_part1035),(kid11_part1036),(kid11_part1037)])

theorem kid11_part1013_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1013) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1014),(kid11_part1015),(kid11_part1016),(kid11_part1017),(kid11_part1018),(kid11_part1019),(kid11_part1020),(kid11_part1021),(kid11_part1022),(kid11_part1023),(kid11_part1024),(kid11_part1025),(kid11_part1026),(kid11_part1027),(kid11_part1028),(kid11_part1029),(kid11_part1030),(kid11_part1031),(kid11_part1032),(kid11_part1033),(kid11_part1034),(kid11_part1035),(kid11_part1036),(kid11_part1037)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1014_checked

  · exact kid11_part1020_checked

  · exact kid11_part1026_checked

  · exact kid11_part1032_checked

  · exact kid11_part1015_checked

  · exact kid11_part1021_checked

  · exact kid11_part1027_checked

  · exact kid11_part1033_checked

  · exact kid11_part1016_checked

  · exact kid11_part1022_checked

  · exact kid11_part1028_checked

  · exact kid11_part1034_checked

  · exact kid11_part1017_checked

  · exact kid11_part1023_checked

  · exact kid11_part1029_checked

  · exact kid11_part1035_checked

  · exact kid11_part1018_checked

  · exact kid11_part1024_checked

  · exact kid11_part1030_checked

  · exact kid11_part1036_checked

  · exact kid11_part1019_checked

  · exact kid11_part1025_checked

  · exact kid11_part1031_checked

  · exact kid11_part1037_checked

def kid11_part1038 : Audit := .cycle 24 1 false (6)
theorem kid11_part1038_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1038) = true := by rfl

def kid11_part1039 : Audit := .cycle 12 11 true (2)
theorem kid11_part1039_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1039) = true := by rfl

def kid11_part1040 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.split 13 (4,true) (byMove [
.cycle 1 18 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 0 25 true (0),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.last 14 (4,false),
.cycle 20 1 false (0),
.cycle 15 8 false (2),
.cycle 16 3 false (1),
.last 15 (4,false),
.cycle 1 25 true (0),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 1 24 true (1),
.last 14 (4,false),
.cycle 17 5 false (1)
]),
.cycle 15 3 false (1),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 10 14 true (1),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.last 17 (4,false),
.cycle 0 17 true (0),
.last 23 (4,false),
.last 19 (4,false),
.last 14 (4,false),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 21 27 true (0),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 17 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.cycle 1 16 true (1),
.last 21 (4,false),
.last 14 (4,false),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 19 (4,false)
]),
.cycle 10 13 true (1),
.cycle 10 19 true (1),
.cycle 10 4 true (1),
.cycle 22 19 true (0),
.cycle 1 20 true (1),
.split 13 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 37 1 false (1),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 1 20 true (1),
.cycle 60 1 false (6),
.last 15 (4,false),
.cycle 5 9 true (1),
.last 17 (4,false),
.cycle 10 4 true (1),
.cycle 10 6 true (0),
.cycle 16 3 false (1),
.last 15 (4,false),
.cycle 37 1 false (1),
.last 15 (4,false),
.cycle 18 1 false (-2),
.cycle 1 20 true (1),
.cycle 10 19 true (1),
.cycle 12 2 true (1),
.cycle 5 9 true (1),
.last 17 (4,false),
.cycle 10 6 true (1)
]),
.cycle 15 3 false (1),
.cycle 10 9 true (1),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.last 17 (4,false),
.cycle 19 7 false (2),
.last 15 (4,false),
.cycle 7 9 true (1),
.last 17 (4,false),
.last 19 (4,false),
.cycle 1 14 true (1),
.last 28 (4,false),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 17 (4,false),
.last 19 (4,false),
.last 23 (4,false),
.cycle 12 2 true (2),
.cycle 5 9 true (1),
.last 17 (4,false),
.cycle 10 6 true (1),
.cycle 1 14 true (1),
.cycle 10 9 true (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 19 (4,false)
]),
.cycle 13 11 true (2)
])
theorem kid11_part1040_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1040) = true := by rfl

def kid11_part1041 : Audit := .cycle 5 7 true (1)
theorem kid11_part1041_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1041) = true := by rfl

def kid11_part1042 : Audit := .cycle 28 1 false (2)
theorem kid11_part1042_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1042) = true := by rfl

def kid11_part1044 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.cycle 0 24 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 6 9 true (0),
.cycle 13 20 true (1),
.cycle 10 16 true (0),
.cycle 1 16 true (0),
.last 15 (4,true),
.last 28 (4,true),
.last 34 (4,true),
.cycle 10 6 true (0),
.cycle 13 35 true (-1),
.cycle 1 24 true (0),
.last 15 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 1 20 true (0),
.cycle 2 15 true (0),
.cycle 1 16 true (0),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid11_part1044_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part1044) = true := by rfl

def kid11_part1045 : Audit := .cycle 13 1 false (1)
theorem kid11_part1045_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part1045) = true := by rfl

def kid11_part1046 : Audit := .split 12 (2,true) (byMove [
.cycle 10 19 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 30 1 false (2),
.cycle 10 36 true (0),
.cycle 22 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 36 1 false (2),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 28 (4,true),
.cycle 1 20 true (0),
.cycle 10 17 true (0),
.cycle 36 1 false (2),
.cycle 11 2 true (0),
.cycle 17 1 false (-1)
])
theorem kid11_part1046_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part1046) = true := by rfl

def kid11_part1047 : Audit := .cycle 29 1 false (1)
theorem kid11_part1047_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part1047) = true := by rfl

def kid11_part1048 : Audit := .split 12 (4,true) (byMove [
.cycle 10 23 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 28 1 false (2),
.last 14 (2,true),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 34 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 19 11 true (2),
.last 14 (2,true),
.cycle 10 19 true (0),
.cycle 34 1 false (2),
.cycle 11 2 true (0),
.cycle 15 1 false (-1)
])
theorem kid11_part1048_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part1048) = true := by rfl

def kid11_part1049 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1049_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part1049) = true := by rfl

def kid11_part1050 : Audit := .cycle 1 16 true (1)
theorem kid11_part1050_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part1050) = true := by rfl

def kid11_part1051 : Audit := .cycle 42 1 false (6)
theorem kid11_part1051_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part1051) = true := by rfl

def kid11_part1052 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.cycle 7 13 true (0),
.cycle 1 16 true (1),
.cycle 17 1 false (-1),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 36, 4, 4, 8192, 16384, 8, 128, 4, 4, 33554432, 67108864, 2097152, 128, 1048576, 1073741824, 33554432, 67108864, 2097152, 36, 1048576, 1073741824, 33554432, 67108864, 134217728, 1711276032, 67108864, 1141899264, 1073741824],[128, 32, 4, 1, 1073741824, 4, 8192, 32, 4, 1, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1048576, 33554432, 536870912, 67108864, 16777216, 1073741824, 1140850688, 1073741824],2140024896⟩,
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 42 1 false (6),
.last 28 (4,true),
.cycle 10 6 true (1),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 11 2 true (1),
.cycle 17 1 false (-1),
.last 18 (4,true),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid11_part1052_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part1052) = true := by rfl

def kid11_part1053 : Audit := .cycle 5 7 true (1)
theorem kid11_part1053_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part1053) = true := by rfl

def kid11_part1054 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.last 17 (2,true),
.cycle 19 1 true (3),
.cycle 17 1 false (-1),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 15 1 true (5),
.cycle 42 1 false (6),
.cycle 10 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 11 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 24 true (0),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 15 1 true (5),
.cycle 12 2 true (2)
])
theorem kid11_part1054_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part1054) = true := by rfl

def kid11_part1055 : Audit := .cycle 10 2 true (1)
theorem kid11_part1055_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part1055) = true := by rfl

def kid11_part1056 : Audit := .cycle 10 4 true (0)
theorem kid11_part1056_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part1056) = true := by rfl

def kid11_part1057 : Audit := .split 16 (2,true) (byMove [
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 1048576, 4672924418048, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 131072, 274877906944, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 131072, 274877906944, 4398046511104, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 4398046511104],[128, 32, 1048576, 1, 4398046511104, 274877906944, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 274877906944, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 274877906944, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],6631437893664⟩,
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 10 10 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 131072, 4096, 4398046642176, 524288, 1048576, 32768, 128, 33554432, 131072, 33554432, 67108864, 8, 131072, 1073741824, 131072, 137438953472, 274877906944, 8589934592, 33554432, 131072, 4398046511104, 524288, 1048576, 32768, 128, 33554432, 131072, 33554432, 67108864, 8, 131072, 1073741824, 4398046511104, 137438953472, 274877906944, 8589934592, 33554432, 131072, 4398046511104, 4398046511104],[128, 32, 1, 1, 4398046511104, 33554432, 524288, 131072, 4096, 4096, 4398046511104, 4398046511104, 33554432, 32, 1, 1, 4398046511104, 131072, 137438953472, 34359738368, 1073741824, 1073741824, 4398046511104, 4398046511104, 524288, 131072, 4096, 4096, 4398046511104, 4398046511104, 33554432, 32, 1, 1, 4398046511104, 131072, 137438953472, 34359738368, 1073741824, 1073741824, 4398046511104, 4398046511104, 4398046511104],6631437893664⟩,
.last 37 (4,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 1048612, 1048580, 1048580, 8192, 16384, 8, 128, 1048580, 1048580, 33554432, 67108864, 2097152, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 1048612, 67108864, 1073741824, 33554432, 67108864, 134217728, 1712324612, 1141899268, 1141899268, 1073741824],[128, 32, 4, 1, 1073741824, 1048580, 8192, 32, 4, 1, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 1073741824, 33554432, 8388608, 1048576, 262144, 1073741824, 68157444, 33554432, 536870912, 67108864, 16777216, 1073741824, 1141899268, 1073741824],2144219200⟩,
.cycle 1 28 true (-1),
.last 17 (4,true),
.cycle 10 7 false (2),
.cycle 10 9 false (2),
.cycle 12 5 false (1),
.cycle 10 12 true (-2),
.cycle 10 10 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 10 15 false (3),
.cycle 10 11 false (2),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 1048576, 4672924418048, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 131072, 274877906944, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 131072, 274877906944, 4398046511104, 137438953472, 274877906944, 8589934592, 33554432, 274877906944, 4398046511104, 4398046511104],[128, 32, 256, 1, 4398046511104, 274877906944, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 67108864, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 131072, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 32, 67108864, 1, 4398046511104, 274877906944, 137438953472, 34359738368, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],6631437893664⟩,
.cycle 1 28 true (-1),
.last 17 (4,true),
.last 18 (4,true)
])
theorem kid11_part1057_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part1057) = true := by rfl

def kid11_part1058 : Audit := .split 12 (2,true) (byMove [
.cycle 14 25 true (0),
.cycle 1 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 13 1 false (-1),
.cycle 18 13 true (1),
.cycle 1 28 true (0),
.cycle 18 1 false (6),
.cycle 1 20 true (0),
.last 13 (4,true),
.cycle 22 17 true (0),
.cycle 10 5 false (2),
.cycle 10 12 true (-2),
.cycle 20 15 true (0),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 13 1 false (-1),
.last 28 (4,true),
.cycle 10 4 true (0),
.cycle 2 15 true (0),
.cycle 1 20 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid11_part1058_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part1058) = true := by rfl

def kid11_part1059 : Audit := .cycle 29 1 false (1)
theorem kid11_part1059_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part1059) = true := by rfl

def kid11_part1060 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 28 1 false (2),
.cycle 15 1 false (1),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 17 1 false (5),
.cycle 14 1 false (0),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 34 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 17 11 true (1),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 15 3 true (3),
.cycle 12 2 true (0)
])
theorem kid11_part1060_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1060) = true := by rfl

def kid11_part1061 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1061_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1061) = true := by rfl

def kid11_part1062 : Audit := .cycle 1 16 true (1)
theorem kid11_part1062_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1062) = true := by rfl

def kid11_part1063 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 54 1 false (0),
.last 23 (2,true),
.cycle 12 13 true (1),
.cycle 10 23 true (-1),
.cycle 25 1 false (-1),
.cycle 15 9 true (2),
.cycle 12 11 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 1 26 true (1),
.cycle 10 13 true (1),
.cycle 10 15 true (1),
.cycle 10 17 true (1),
.last 23 (2,true),
.cycle 12 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 25 1 false (-1),
.cycle 15 9 true (2),
.cycle 12 11 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 1 26 true (1),
.cycle 21 2 true (2)
])
theorem kid11_part1063_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1063) = true := by rfl

def kid11_part1064 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.last 13 (4,true),
.last 14 (4,true),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 10 14 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 22 (4,true),
.last 28 (4,true),
.cycle 10 4 true (1),
.cycle 22 19 true (0),
.cycle 1 20 true (1),
.last 13 (4,true),
.last 14 (4,true),
.last 18 (4,true),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid11_part1064_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1064) = true := by rfl

def kid11_part1065 : Audit := .cycle 5 7 true (1)
theorem kid11_part1065_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1065) = true := by rfl

def kid11_part1066 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 20 1 false (0),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 37 1 true (-3),
.cycle 15 1 false (-1),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 15 1 true (5),
.cycle 10 13 true (1),
.cycle 10 21 true (1),
.cycle 10 4 true (1),
.last 13 (2,true),
.cycle 1 20 true (1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 0 24 true (0),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 15 1 true (5),
.cycle 12 2 true (2)
])
theorem kid11_part1066_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1066) = true := by rfl

def kid11_part1067 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 37 1 false (1),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 1 20 true (1),
.cycle 60 1 false (6),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 14 8 true (2),
.cycle 10 4 true (1),
.cycle 10 6 true (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 37 1 false (1),
.cycle 14 3 false (0),
.cycle 18 1 false (-2),
.cycle 1 20 true (1),
.cycle 12 15 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 14 6 true (2),
.cycle 12 2 true (1)
])
theorem kid11_part1067_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1067) = true := by rfl

def kid11_part1043 : Audit := .split 11 (4,false) (byMove [(kid11_part1044),(kid11_part1045),(kid11_part1046),(kid11_part1047),(kid11_part1048),(kid11_part1049),(kid11_part1050),(kid11_part1051),(kid11_part1052),(kid11_part1053),(kid11_part1054),(kid11_part1055),(kid11_part1056),(kid11_part1057),(kid11_part1058),(kid11_part1059),(kid11_part1060),(kid11_part1061),(kid11_part1062),(kid11_part1063),(kid11_part1064),(kid11_part1065),(kid11_part1066),(kid11_part1067)])

theorem kid11_part1043_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1043) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part1044),(kid11_part1045),(kid11_part1046),(kid11_part1047),(kid11_part1048),(kid11_part1049),(kid11_part1050),(kid11_part1051),(kid11_part1052),(kid11_part1053),(kid11_part1054),(kid11_part1055),(kid11_part1056),(kid11_part1057),(kid11_part1058),(kid11_part1059),(kid11_part1060),(kid11_part1061),(kid11_part1062),(kid11_part1063),(kid11_part1064),(kid11_part1065),(kid11_part1066),(kid11_part1067)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1044_checked

  · exact kid11_part1050_checked

  · exact kid11_part1056_checked

  · exact kid11_part1062_checked

  · exact kid11_part1045_checked

  · exact kid11_part1051_checked

  · exact kid11_part1057_checked

  · exact kid11_part1063_checked

  · exact kid11_part1046_checked

  · exact kid11_part1052_checked

  · exact kid11_part1058_checked

  · exact kid11_part1064_checked

  · exact kid11_part1047_checked

  · exact kid11_part1053_checked

  · exact kid11_part1059_checked

  · exact kid11_part1065_checked

  · exact kid11_part1048_checked

  · exact kid11_part1054_checked

  · exact kid11_part1060_checked

  · exact kid11_part1066_checked

  · exact kid11_part1049_checked

  · exact kid11_part1055_checked

  · exact kid11_part1061_checked

  · exact kid11_part1067_checked

def kid11_part1068 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1068_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1068) = true := by rfl

def kid11_part1069 : Audit := .cycle 6 5 true (2)
theorem kid11_part1069_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1069) = true := by rfl

def kid11_part1070 : Audit := .cycle 1 12 true (1)
theorem kid11_part1070_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1070) = true := by rfl

def kid11_part1071 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 10 37 true (0),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 21 7 false (2),
.cycle 53 3 false (5),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 9 4 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.cycle 2 18 true (1),
.cycle 2 29 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,false),
.cycle 2 18 true (1),
.last 13 (4,false),
.cycle 2 18 true (1),
.cycle 7 7 true (2),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 2 11 true (1),
.cycle 2 13 true (1),
.cycle 2 15 true (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.split 12 (4,true) (byMove [
.cycle 14 4 true (1),
.cycle 1 16 true (1),
.cycle 10 37 true (0),
.cycle 44 1 false (2),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.last 14 (4,false),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 2 15 true (1),
.cycle 2 19 true (1),
.cycle 18 3 false (2),
.cycle 5 9 true (1),
.cycle 10 31 true (0),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 2 15 true (1)
]),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 19 true (1),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 2 11 true (1)
])
theorem kid11_part1071_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1071) = true := by rfl

def kid11_part1072 : Audit := .cycle 1 12 true (1)
theorem kid11_part1072_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1072) = true := by rfl

def kid11_part1074 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (4,false),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.last 17 (4,false),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 11 4 true (2),
.cycle 1 17 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 1 18 true (1)
])
theorem kid11_part1074_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1074) = true := by rfl

def kid11_part1075 : Audit := .cycle 19 1 false (1)
theorem kid11_part1075_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1075) = true := by rfl

def kid11_part1076 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 21 (4,false),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 29 (4,false),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 21 7 false (2),
.last 17 (4,false),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 9 4 true (2)
])
theorem kid11_part1076_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1076) = true := by rfl

def kid11_part1077 : Audit := .cycle 7 7 true (2)
theorem kid11_part1077_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1077) = true := by rfl

def kid11_part1078 : Audit := .split 13 (4,false) (byMove [
.cycle 1 24 true (0),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 24 9 true (1),
.cycle 25 1 false (1),
.cycle 17 1 true (3),
.cycle 20 1 false (0),
.cycle 15 8 false (2),
.last 26 (2,true),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (-2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 20 true (1),
.last 18 (2,true),
.cycle 21 1 true (-1),
.cycle 17 5 false (1)
])
theorem kid11_part1078_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1078) = true := by rfl

def kid11_part1079 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 23 1 false (1),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 21 1 false (-1),
.cycle 12 2 true (2),
.cycle 1 14 true (1),
.cycle 1 24 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 19 1 true (3),
.cycle 8 8 true (2),
.cycle 6 12 true (2),
.cycle 17 3 true (3),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 21 1 false (-1),
.cycle 10 4 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 1 true (4),
.cycle 14 5 true (4)
])
theorem kid11_part1079_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1079) = true := by rfl

def kid11_part1080 : Audit := .cycle 1 12 true (1)
theorem kid11_part1080_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1080) = true := by rfl

def kid11_part1081 : Audit := .split 20 (4,false) (byMove [
.cycle 1 21 true (1),
.cycle 1 30 true (1),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 18 9 true (4),
.cycle 3 18 true (1),
.cycle 20 1 true (6),
.cycle 8 13 true (2),
.cycle 6 15 true (2),
.cycle 18 3 true (4),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 10 21 true (2),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (6),
.cycle 1 23 true (1)
])
theorem kid11_part1081_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1081) = true := by rfl

def kid11_part1082 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 24 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (4,false),
.last 20 (4,false),
.last 13 (4,false),
.last 20 (4,false),
.cycle 7 7 true (2),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 24 (4,false)
])
theorem kid11_part1082_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1082) = true := by rfl

def kid11_part1083 : Audit := .cycle 0 13 true (0)
theorem kid11_part1083_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1083) = true := by rfl

def kid11_part1084 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (2),
.cycle 3 29 true (1),
.cycle 13 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 22 true (1),
.cycle 33 1 false (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 12 4 true (4)
])
theorem kid11_part1084_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1084) = true := by rfl

def kid11_part1085 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 8 14 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 14 true (2),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 9 true (4),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 12 3 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.cycle 8 8 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 8 9 true (2)
])
theorem kid11_part1085_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1085) = true := by rfl

def kid11_part1086 : Audit := .split 15 (4,false) (byMove [
.cycle 1 16 true (1),
.cycle 6 20 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 11 true (2),
.cycle 14 2 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 12 9 true (2),
.cycle 3 13 true (1),
.cycle 15 1 true (5),
.cycle 8 8 true (2),
.cycle 6 10 true (2),
.cycle 13 3 true (3),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 13 5 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 15 1 true (5),
.cycle 6 13 true (2)
])
theorem kid11_part1086_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1086) = true := by rfl

def kid11_part1087 : Audit := .split 17 (4,false) (byMove [
.cycle 1 18 true (1),
.cycle 42 1 false (6),
.last 18 (2,true),
.cycle 0 19 true (0),
.last 20 (2,true),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 15 9 true (3),
.cycle 3 15 true (1),
.cycle 17 1 true (5),
.cycle 8 10 true (2),
.cycle 6 12 true (2),
.cycle 15 3 true (3),
.last 18 (2,true),
.cycle 1 19 true (1),
.last 20 (2,true),
.cycle 13 5 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 17 1 true (5),
.cycle 13 6 true (3)
])
theorem kid11_part1087_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1087) = true := by rfl

def kid11_part1088 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.last 29 (4,false),
.cycle 7 13 true (0),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.last 15 (4,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048580, 16777216, 4, 128, 256, 32768, 128, 16777216, 1048580, 128, 256, 2097152, 131072, 16777216, 4, 128, 256, 8, 1024, 16777216, 4, 16777216],[128, 32, 4, 1, 1, 1024, 128, 131072, 16384, 4096, 1048580, 1024, 128, 8388608, 1048576, 262144, 262144, 1024, 128, 32, 4, 1, 1, 1024, 16777216],23151632⟩,
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.last 17 (4,false),
.last 21 (4,false),
.cycle 10 6 true (1),
.cycle 5 9 true (1),
.last 25 (4,false),
.last 13 (4,false),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.last 17 (4,false)
])
theorem kid11_part1088_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1088) = true := by rfl

def kid11_part1089 : Audit := .cycle 5 7 true (1)
theorem kid11_part1089_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1089) = true := by rfl

def kid11_part1090 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 0 27 true (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (0),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.cycle 10 4 true (1),
.cycle 10 6 true (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 1 27 true (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.cycle 16 5 false (2)
])
theorem kid11_part1090_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1090) = true := by rfl

def kid11_part1091 : Audit := .cycle 10 2 true (2)
theorem kid11_part1091_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1091) = true := by rfl

def kid11_part1092 : Audit := .cycle 1 12 true (1)
theorem kid11_part1092_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1092) = true := by rfl

def kid11_part1093 : Audit := .cycle 7 5 true (2)
theorem kid11_part1093_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1093) = true := by rfl

def kid11_part1094 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 2 14 true (1)
])
theorem kid11_part1094_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1094) = true := by rfl

def kid11_part1095 : Audit := .cycle 0 13 true (0)
theorem kid11_part1095_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1095) = true := by rfl

def kid11_part1096 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 13 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 13 9 true (4),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 13 3 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.cycle 12 3 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 12 4 true (4)
])
theorem kid11_part1096_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1096) = true := by rfl

def kid11_part1097 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 3 true (4),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 9 true (4),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 12 3 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.cycle 14 3 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 14 3 true (5)
])
theorem kid11_part1097_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1097) = true := by rfl

def kid11_part1073 : Audit := .split 11 (4,true) (byMove [(kid11_part1074),(kid11_part1075),(kid11_part1076),(kid11_part1077),(kid11_part1078),(kid11_part1079),(kid11_part1080),(kid11_part1081),(kid11_part1082),(kid11_part1083),(kid11_part1084),(kid11_part1085),(kid11_part1086),(kid11_part1087),(kid11_part1088),(kid11_part1089),(kid11_part1090),(kid11_part1091),(kid11_part1092),(kid11_part1093),(kid11_part1094),(kid11_part1095),(kid11_part1096),(kid11_part1097)])

theorem kid11_part1073_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1073) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1074),(kid11_part1075),(kid11_part1076),(kid11_part1077),(kid11_part1078),(kid11_part1079),(kid11_part1080),(kid11_part1081),(kid11_part1082),(kid11_part1083),(kid11_part1084),(kid11_part1085),(kid11_part1086),(kid11_part1087),(kid11_part1088),(kid11_part1089),(kid11_part1090),(kid11_part1091),(kid11_part1092),(kid11_part1093),(kid11_part1094),(kid11_part1095),(kid11_part1096),(kid11_part1097)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1074_checked

  · exact kid11_part1080_checked

  · exact kid11_part1086_checked

  · exact kid11_part1092_checked

  · exact kid11_part1075_checked

  · exact kid11_part1081_checked

  · exact kid11_part1087_checked

  · exact kid11_part1093_checked

  · exact kid11_part1076_checked

  · exact kid11_part1082_checked

  · exact kid11_part1088_checked

  · exact kid11_part1094_checked

  · exact kid11_part1077_checked

  · exact kid11_part1083_checked

  · exact kid11_part1089_checked

  · exact kid11_part1095_checked

  · exact kid11_part1078_checked

  · exact kid11_part1084_checked

  · exact kid11_part1090_checked

  · exact kid11_part1096_checked

  · exact kid11_part1079_checked

  · exact kid11_part1085_checked

  · exact kid11_part1091_checked

  · exact kid11_part1097_checked

def kid11_part1098 : Audit := .cycle 11 3 true (3)
theorem kid11_part1098_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1098) = true := by rfl

def kid11_part978 : Audit := .split 10 (5,true) (byMove [(kid11_part979),(kid11_part980),(kid11_part981),(kid11_part982),(kid11_part983),(kid11_part1008),(kid11_part1009),(kid11_part1010),(kid11_part1011),(kid11_part1012),(kid11_part1013),(kid11_part1038),(kid11_part1039),(kid11_part1040),(kid11_part1041),(kid11_part1042),(kid11_part1043),(kid11_part1068),(kid11_part1069),(kid11_part1070),(kid11_part1071),(kid11_part1072),(kid11_part1073),(kid11_part1098)])

theorem kid11_part978_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (kid11_part978) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part979),(kid11_part980),(kid11_part981),(kid11_part982),(kid11_part983),(kid11_part1008),(kid11_part1009),(kid11_part1010),(kid11_part1011),(kid11_part1012),(kid11_part1013),(kid11_part1038),(kid11_part1039),(kid11_part1040),(kid11_part1041),(kid11_part1042),(kid11_part1043),(kid11_part1068),(kid11_part1069),(kid11_part1070),(kid11_part1071),(kid11_part1072),(kid11_part1073),(kid11_part1098)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part979_checked

  · exact kid11_part1009_checked

  · exact kid11_part1039_checked

  · exact kid11_part1069_checked

  · exact kid11_part980_checked

  · exact kid11_part1010_checked

  · exact kid11_part1040_checked

  · exact kid11_part1070_checked

  · exact kid11_part981_checked

  · exact kid11_part1011_checked

  · exact kid11_part1041_checked

  · exact kid11_part1071_checked

  · exact kid11_part982_checked

  · exact kid11_part1012_checked

  · exact kid11_part1042_checked

  · exact kid11_part1072_checked

  · exact kid11_part983_checked

  · exact kid11_part1013_checked

  · exact kid11_part1043_checked

  · exact kid11_part1073_checked

  · exact kid11_part1008_checked

  · exact kid11_part1038_checked

  · exact kid11_part1068_checked

  · exact kid11_part1098_checked

def kid11_part1099 : Audit := .cycle 0 9 true (0)
theorem kid11_part1099_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,0⟩)) (kid11_part1099) = true := by rfl

def kid11_part1100 : Audit := .cycle 1 8 true (1)
theorem kid11_part1100_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,1⟩)) (kid11_part1100) = true := by rfl

def kid11_part1101 : Audit := .cycle 2 7 true (1)
theorem kid11_part1101_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,2⟩)) (kid11_part1101) = true := by rfl

def kid11_part1102 : Audit := .cycle 1 11 true (1)
theorem kid11_part1102_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,3⟩)) (kid11_part1102) = true := by rfl

def kid11_part1104 : Audit := .cycle 1 10 true (1)
theorem kid11_part1104_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part1104) = true := by rfl

def kid11_part1105 : Audit := .cycle 7 3 true (3)
theorem kid11_part1105_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part1105) = true := by rfl

def kid11_part1106 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 17 1 false (-1),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 1 17 true (0),
.cycle 15 3 false (1),
.cycle 19 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 33 1 false (3),
.cycle 14 7 true (0),
.cycle 14 9 true (0),
.cycle 25 3 false (2),
.cycle 25 9 false (3),
.cycle 19 3 false (1),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 15 3 false (1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 21 3 false (1),
.cycle 11 4 true (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (5,true) (byMove [
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 1 35 true (1),
.cycle 35 1 false (3),
.cycle 0 25 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 42, 16, 64],[2, 32, 4, 1, 64, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 46, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 21 true (0),
.last 20 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 42, 16, 64],[2, 32, 4, 1, 64, 32, 64],64⟩,
.cycle 7 17 true (2),
.cycle 10 12 true (2),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.cycle 1 24 true (1),
.last 21 (4,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 20 11 true (6)
]),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 30 1 false (2),
.cycle 3 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 19 9 true (3),
.cycle 11 7 true (2),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 8, 1, 64, 32, 64],64⟩,
.cycle 7 12 true (2),
.cycle 3 17 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 30 1 false (2),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (2),
.cycle 3 18 true (1)
]),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 36 1 false (2),
.cycle 2 22 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 20 11 true (3),
.cycle 13 7 true (2),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 16, 1, 64, 32, 64],64⟩,
.cycle 7 14 true (2),
.cycle 2 21 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 36 1 false (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 2 22 true (1)
]),
.cycle 8 3 true (4),
.cycle 7 5 true (3),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 29 1 false (-1),
.cycle 29 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 46, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 13 7 true (2),
.cycle 13 9 true (2),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 29 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (3),
.cycle 12 5 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 17 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 22 1 false (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 22 1 false (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 16 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid11_part1106_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part1106) = true := by rfl

def kid11_part1107 : Audit := .cycle 0 11 true (0)
theorem kid11_part1107_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part1107) = true := by rfl

def kid11_part1108 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 1 17 true (0),
.cycle 15 3 false (1),
.cycle 19 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 14 7 true (0),
.cycle 17 3 false (1),
.cycle 25 3 false (2),
.cycle 25 9 false (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 15 3 false (1),
.cycle 18 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 21 3 false (1),
.cycle 11 4 true (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.last 24 (2,true),
.cycle 35 1 false (3),
.cycle 0 25 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 62, 16, 64],[2, 32, 64, 1, 4, 2, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.last 32 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 62, 16, 64],[2, 32, 64, 1, 4, 32, 64],64⟩,
.cycle 7 17 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.cycle 1 24 true (1),
.last 22 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 20 true (2),
.cycle 20 11 true (6)
]),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 30 1 false (2),
.cycle 3 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 11 7 true (2),
.cycle 21 9 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 62, 16, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 30 1 false (2),
.cycle 3 17 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (2),
.cycle 3 18 true (1)
]),
.cycle 19 1 false (1),
.cycle 8 3 true (4),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.last 17 (5,true),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,true),
.last 17 (5,true)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 15 1 false (-1),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 21 true (0),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 22 1 false (-2),
.cycle 17 6 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (3),
.cycle 8 7 true (3),
.cycle 7 11 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 22 1 false (-2),
.cycle 18 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.cycle 12 5 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid11_part1108_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part1108) = true := by rfl

def kid11_part1109 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 13 4 false (1),
.cycle 18 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 18 true (2),
.cycle 3 18 true (1),
.cycle 10 22 true (2),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 12 9 true (2),
.last 36 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 15 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (2),
.cycle 0 27 true (0),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 34 (4,true),
.cycle 10 21 true (2)
]),
.cycle 10 7 true (2),
.cycle 8 4 true (4),
.cycle 8 3 true (4),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 23 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 10 8 true (3),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 23 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 6 true (3),
.cycle 10 7 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 13 4 false (1),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 15 7 false (1),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 0, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 0, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 22 5 false (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid11_part1109_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part1109) = true := by rfl

def kid11_part1110 : Audit := .cycle 0 10 true (0)
theorem kid11_part1110_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part1110) = true := by rfl

def kid11_part1111 : Audit := .cycle 1 9 true (1)
theorem kid11_part1111_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part1111) = true := by rfl

def kid11_part1112 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (4),
.cycle 8 10 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 27 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 10 18 true (4),
.cycle 3 25 true (1),
.cycle 18 11 true (5),
.cycle 8 20 true (4),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 19 9 true (5),
.last 41 (4,true),
.cycle 8 20 true (4),
.cycle 7 22 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 30 true (0),
.cycle 12 16 true (4),
.cycle 27 2 true (8),
.last 29 (4,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 9 19 true (4),
.cycle 8 20 true (4)
]),
.cycle 11 7 true (4),
.split 29 (4,true) (byMove [
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 10 29 true (4),
.cycle 0 38 true (0),
.cycle 0 33 true (0),
.last 32 (2,true),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 16 15 true (5),
.last 31 (2,true),
.cycle 1 32 true (1),
.cycle 12 25 true (4),
.last 31 (2,true),
.cycle 28 4 true (8),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 9 22 true (4),
.cycle 8 34 true (4)
]),
.cycle 8 10 true (4),
.cycle 7 12 true (3),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 47 1 false (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 41 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.last 32 (4,true),
.cycle 8 12 true (4),
.cycle 6 14 true (2),
.cycle 16 4 true (6),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 41 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4)
]),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 11 9 true (4),
.last 33 (4,true),
.cycle 8 12 true (4),
.cycle 7 14 true (3),
.cycle 16 6 true (6),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (6),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4)
]),
.split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 52 1 false (2),
.cycle 32 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 12 true (4),
.cycle 6 14 true (2),
.cycle 16 4 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 23 (2,true),
.cycle 32 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (4),
.cycle 8 10 true (4)
])
theorem kid11_part1112_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part1112) = true := by rfl

def kid11_part1113 : Audit := .cycle 3 7 true (1)
theorem kid11_part1113_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part1113) = true := by rfl

def kid11_part1114 : Audit := .cycle 9 1 true (5)
theorem kid11_part1114_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part1114) = true := by rfl

def kid11_part1115 : Audit := .cycle 8 2 true (4)
theorem kid11_part1115_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part1115) = true := by rfl

def kid11_part1116 : Audit := .cycle 6 4 true (2)
theorem kid11_part1116_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part1116) = true := by rfl

def kid11_part1117 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (3),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 26 5 false (1),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 30 9 false (2),
.cycle 35 13 false (3)
]),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 22 (2,true) (byMove [
.cycle 1 26 true (1),
.cycle 0 26 true (0),
.cycle 24 18 true (3),
.last 29 (4,true),
.last 26 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 47, 12, 16, 64],[2, 32, 12, 1, 64, 4, 64],64⟩,
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 6, 16, 64],[2, 32, 2, 1, 64, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 24 true (0),
.last 23 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 36, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 7 30 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 1 25 true (1),
.cycle 23 16 true (3),
.last 26 (4,true),
.last 24 (4,true),
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 30 14 true (7)
]),
.cycle 0 21 true (0),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 26 true (1),
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
.cycle 1 18 true (1),
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
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 27 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.cycle 12 3 true (4),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.cycle 10 4 true (4),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 27 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4)
]),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.last 17 (4,true),
.cycle 33 1 false (1),
.cycle 7 10 true (3),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 28 7 false (2),
.cycle 31 9 false (2),
.cycle 26 5 false (1),
.cycle 15 12 true (1),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true)
]),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 29 (2,true),
.cycle 22 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.last 16 (2,true),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.cycle 10 4 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 29 (2,true),
.cycle 22 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1117_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part1117) = true := by rfl

def kid11_part1119 : Audit := .cycle 1 14 true (1)
theorem kid11_part1119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1119) = true := by rfl

def kid11_part1120 : Audit := .cycle 0 14 true (0)
theorem kid11_part1120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1120) = true := by rfl

def kid11_part1121 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 31 1 false (1),
.cycle 35 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 18 true (2),
.cycle 12 7 true (2),
.cycle 0 21 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 32, 1, 1024, 8192, 16384, 8, 128, 32, 65536, 128, 256, 8, 128, 262144, 1024, 262144],[128, 32, 32, 1, 262144, 32, 8192, 32, 1024, 1, 262144, 32, 128, 32, 32, 1, 262144, 32, 262144],329728⟩,
.cycle 7 12 true (2),
.cycle 35 1 false (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 31 1 false (1),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (2),
.last 29 (4,true)
])
theorem kid11_part1121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1121) = true := by rfl

def kid11_part1122 : Audit := .cycle 0 17 true (0)
theorem kid11_part1122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1122) = true := by rfl

def kid11_part1123 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (-2),
.last 31 (5,true),
.cycle 11 20 true (-2),
.cycle 0 28 true (-2),
.cycle 11 20 true (-2),
.last 22 (5,true),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 262176, 1, 1024, 8192, 16384, 8, 2208, 33, 65536, 8192, 16384, 512, 8320, 2145, 65536, 262144],[128, 32, 1152, 1, 1, 262144, 8192, 32, 74880, 1, 1, 262144, 8192, 2048, 8320, 64, 64, 262144, 262144],262414⟩,
.cycle 24 19 true (4),
.cycle 0 24 true (-2),
.last 27 (5,true),
.cycle 1 25 true (-2),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 262176, 1, 1024, 8192, 16384, 8, 2208, 33, 65536, 8192, 16384, 512, 8320, 2080, 65536, 262144],[128, 32, 1152, 1, 32, 262144, 8192, 32, 66560, 1, 32, 262144, 8192, 2048, 66560, 64, 2048, 262144, 262144],262414⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 262176, 1, 1024, 8192, 16384, 8, 2208, 2081, 65536, 8192, 16384, 512, 8320, 2080, 65536, 262144],[128, 32, 66688, 1, 2080, 262144, 8192, 32, 66560, 1, 2080, 262144, 8192, 2048, 66560, 64, 2048, 262144, 262144],262414⟩,
.last 23 (5,true),
.cycle 12 10 true (-2),
.cycle 1 28 true (-2),
.last 30 (5,true),
.last 22 (5,true),
.cycle 18 32 true (0),
.cycle 24 35 true (3),
.cycle 0 24 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 16777248, 1, 1024, 8192, 16384, 8, 160, 32801, 65536, 524288, 1048576, 512, 128, 16810016, 4194304, 524288, 1048576, 2097152, 25700352, 27559968, 4194304, 16777216],[128, 32, 1152, 1, 512, 16777216, 8192, 32, 16778400, 1, 32768, 16777216, 524288, 2048, 128, 64, 2097152, 16777216, 524288, 8388608, 29961344, 262144, 2097152, 16777216, 16777216],33503566⟩,
.proven (BB6.Agent11Raw39Pumps.M1141.table) (fun m hm => BB6.Agent11Raw39Pumps.M1141.never m hm),
.cycle 21 6 true (3)
])
theorem kid11_part1123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1123) = true := by rfl

def kid11_part1124 : Audit := .split 14 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 0 26 true (0),
.last 22 (4,true),
.cycle 1 21 true (0),
.cycle 15 3 false (1),
.cycle 19 3 false (0),
.cycle 0 18 true (0),
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.cycle 1 23 true (0),
.cycle 5 12 true (1),
.last 16 (4,true),
.last 18 (4,true),
.cycle 19 3 false (1),
.cycle 0 22 true (0),
.last 20 (4,true),
.cycle 15 3 false (1),
.last 16 (4,true),
.cycle 0 18 true (0),
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.cycle 1 22 true (1),
.cycle 21 3 false (1),
.last 16 (4,true)
])
theorem kid11_part1124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1124) = true := by rfl

def kid11_part1125 : Audit := .cycle 1 11 true (1)
theorem kid11_part1125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1125) = true := by rfl

def kid11_part1126 : Audit := .cycle 7 4 true (3)
theorem kid11_part1126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1126) = true := by rfl

def kid11_part1127 : Audit := .split 21 (5,true) (byMove [
.cycle 0 46 true (0),
.cycle 1 25 true (1),
.cycle 2 34 true (1),
.cycle 1 52 true (1),
.cycle 1 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 1, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 1068, 4096],4096⟩,
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 5, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 1 23 true (1),
.last 22 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 5, 16, 64],[2, 32, 4, 1, 64, 32, 64],64⟩,
.cycle 7 22 true (2),
.cycle 10 14 true (2),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.cycle 53 1 false (11),
.last 23 (4,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.cycle 2 40 true (1),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 22 14 true (6)
])
theorem kid11_part1127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1127) = true := by rfl

def kid11_part1128 : Audit := .cycle 0 12 true (0)
theorem kid11_part1128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1128) = true := by rfl

def kid11_part1129 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1129) = true := by rfl

def kid11_part1130 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 5, 16, 64],[2, 32, 32, 1, 64, 4, 64],64⟩,
.cycle 0 21 true (0),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.cycle 1 15 true (1),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1130) = true := by rfl

def kid11_part1131 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 27 5 false (2),
.cycle 12 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 18 true (3),
.cycle 12 7 true (3),
.cycle 0 17 true (0),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 27 5 false (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 12 6 true (4)
])
theorem kid11_part1131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1131) = true := by rfl

def kid11_part1132 : Audit := .split 14 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 33 (4,true),
.cycle 29 7 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 5, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 8 8 true (3),
.cycle 7 12 true (3),
.cycle 11 4 true (3),
.cycle 1 17 true (1),
.cycle 4 16 true (1),
.cycle 19 12 true (-2),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 12 6 true (3)
])
theorem kid11_part1132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1132) = true := by rfl

def kid11_part1133 : Audit := .cycle 1 13 true (1)
theorem kid11_part1133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1133) = true := by rfl

def kid11_part1134 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 26 1 false (0),
.cycle 5 14 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 11 16 true (2),
.cycle 11 7 true (2),
.cycle 0 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 33, 16, 64],[2, 32, 34, 1, 64, 32, 64],64⟩,
.cycle 7 10 true (2),
.cycle 1 19 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 26 1 false (0),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 9 7 true (2),
.cycle 5 14 true (1)
])
theorem kid11_part1134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1134) = true := by rfl

def kid11_part1135 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 40 true (-2),
.cycle 31 24 true (1),
.last 26 (4,true),
.last 29 (4,true),
.last 24 (4,true),
.cycle 0 24 true (-2),
.cycle 21 20 true (3),
.cycle 1 41 true (-2),
.cycle 0 36 true (-2),
.last 21 (4,true),
.cycle 22 20 true (4),
.last 37 (4,true),
.last 23 (4,true),
.cycle 0 28 true (-2),
.cycle 27 20 true (1),
.cycle 13 8 true (-2),
.last 22 (4,true),
.last 39 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 160, 1, 1024, 8192, 16384, 8, 160, 33, 65536, 524288, 1048576, 512, 128, 16777216, 4194304, 524288, 1048576, 2097152, 8923136, 25427968, 4194304, 16777216],[128, 32, 128, 1, 16777216, 128, 8192, 32, 16777216, 1, 16777216, 8192, 524288, 2048, 16777216, 64, 16777216, 524288, 524288, 8388608, 17301504, 262144, 16777216, 524288, 16777216],33503296⟩,
.last 22 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 673, 1, 1024, 8192, 16384, 8, 160, 33, 65536, 524288, 1048576, 512, 128, 16777216, 4194304, 524288, 1048576, 2097152, 11315264, 25427968, 4194304, 16777216],[128, 32, 640, 1, 16777216, 512, 8192, 32, 16777216, 1, 16777216, 32768, 524288, 2048, 16777216, 64, 16777216, 2097152, 524288, 8388608, 19398656, 262144, 16777216, 2097152, 16777216],33503296⟩,
.last 21 (4,true),
.last 27 (4,true)
])
theorem kid11_part1135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1135) = true := by rfl

def kid11_part1136 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 7 9 true (3),
.last 14 (5,true),
.cycle 7 8 true (3),
.last 26 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 0 17 true (0),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.last 25 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part1136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1136) = true := by rfl

def kid11_part1137 : Audit := .cycle 1 11 true (1)
theorem kid11_part1137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1137) = true := by rfl

def kid11_part1138 : Audit := .cycle 7 4 true (3)
theorem kid11_part1138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1138) = true := by rfl

def kid11_part1139 : Audit := .cycle 2 10 true (1)
theorem kid11_part1139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1139) = true := by rfl

def kid11_part1140 : Audit := .cycle 0 12 true (0)
theorem kid11_part1140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1140) = true := by rfl

def kid11_part1141 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (4),
.cycle 0 13 true (0),
.cycle 0 24 true (-2),
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
.last 26 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1141) = true := by rfl

def kid11_part1142 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 23 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 22 true (4),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 8 8 true (4),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1142) = true := by rfl

def kid11_part1118 : Audit := .split 10 (2,true) (byMove [(kid11_part1119),(kid11_part1120),(kid11_part1121),(kid11_part1122),(kid11_part1123),(kid11_part1124),(kid11_part1125),(kid11_part1126),(kid11_part1127),(kid11_part1128),(kid11_part1129),(kid11_part1130),(kid11_part1131),(kid11_part1132),(kid11_part1133),(kid11_part1134),(kid11_part1135),(kid11_part1136),(kid11_part1137),(kid11_part1138),(kid11_part1139),(kid11_part1140),(kid11_part1141),(kid11_part1142)])

theorem kid11_part1118_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part1118) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part1119),(kid11_part1120),(kid11_part1121),(kid11_part1122),(kid11_part1123),(kid11_part1124),(kid11_part1125),(kid11_part1126),(kid11_part1127),(kid11_part1128),(kid11_part1129),(kid11_part1130),(kid11_part1131),(kid11_part1132),(kid11_part1133),(kid11_part1134),(kid11_part1135),(kid11_part1136),(kid11_part1137),(kid11_part1138),(kid11_part1139),(kid11_part1140),(kid11_part1141),(kid11_part1142)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1119_checked

  · exact kid11_part1125_checked

  · exact kid11_part1131_checked

  · exact kid11_part1137_checked

  · exact kid11_part1120_checked

  · exact kid11_part1126_checked

  · exact kid11_part1132_checked

  · exact kid11_part1138_checked

  · exact kid11_part1121_checked

  · exact kid11_part1127_checked

  · exact kid11_part1133_checked

  · exact kid11_part1139_checked

  · exact kid11_part1122_checked

  · exact kid11_part1128_checked

  · exact kid11_part1134_checked

  · exact kid11_part1140_checked

  · exact kid11_part1123_checked

  · exact kid11_part1129_checked

  · exact kid11_part1135_checked

  · exact kid11_part1141_checked

  · exact kid11_part1124_checked

  · exact kid11_part1130_checked

  · exact kid11_part1136_checked

  · exact kid11_part1142_checked

def kid11_part1143 : Audit := .cycle 1 11 true (1)
theorem kid11_part1143_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part1143) = true := by rfl

def kid11_part1145 : Audit := .split 13 (2,true) (byMove [
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
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 21 (5,true),
.cycle 1 15 true (1),
.cycle 12 4 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (4),
.cycle 12 6 true (4)
])
theorem kid11_part1145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1145) = true := by rfl

def kid11_part1146 : Audit := .cycle 0 14 true (0)
theorem kid11_part1146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1146) = true := by rfl

def kid11_part1147 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 31 1 false (1),
.last 21 (2,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 12 7 true (2),
.cycle 62 1 false (4),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 32, 262176, 1024, 8192, 16384, 8, 128, 32, 65536, 8192, 16384, 8, 128, 262144, 65536, 262144],[128, 32, 262144, 1, 32, 32, 8192, 32, 262144, 1, 262144, 32, 8192, 32, 262144, 1, 262144, 32, 262144],460816⟩,
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 31 1 false (1),
.last 20 (2,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (2),
.last 21 (2,true)
])
theorem kid11_part1147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1147) = true := by rfl

def kid11_part1148 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.last 25 (5,true),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 23 (5,true),
.cycle 3 13 true (1),
.last 22 (5,true),
.cycle 8 8 true (2),
.cycle 6 10 true (2),
.last 17 (5,true),
.cycle 5 14 true (1),
.cycle 1 17 true (1),
.cycle 7 12 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 7 13 true (2),
.cycle 7 14 true (2)
])
theorem kid11_part1148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1148) = true := by rfl

def kid11_part1149 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1149) = true := by rfl

def kid11_part1150 : Audit := .split 14 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 0 26 true (0),
.cycle 47 1 false (3),
.cycle 1 21 true (0),
.cycle 15 3 false (1),
.cycle 19 3 false (0),
.cycle 0 18 true (0),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 1 23 true (0),
.cycle 17 3 false (1),
.cycle 52 3 false (7),
.cycle 16 19 true (2),
.last 16 (2,true),
.cycle 0 22 true (0),
.cycle 40 1 false (2),
.cycle 15 3 false (1),
.cycle 18 3 false (0),
.cycle 0 18 true (0),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 1 22 true (1),
.cycle 21 3 false (1),
.cycle 16 7 true (3)
])
theorem kid11_part1150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1150) = true := by rfl

def kid11_part1151 : Audit := .cycle 1 11 true (1)
theorem kid11_part1151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1151) = true := by rfl

def kid11_part1152 : Audit := .cycle 7 4 true (3)
theorem kid11_part1152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1152) = true := by rfl

def kid11_part1153 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 20 1 false (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.last 33 (5,true),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 15 (5,true),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 20 1 false (0),
.last 21 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1153) = true := by rfl

def kid11_part1154 : Audit := .cycle 0 12 true (0)
theorem kid11_part1154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1154) = true := by rfl

def kid11_part1155 : Audit := .cycle 36 1 false (8)
theorem kid11_part1155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1155) = true := by rfl

def kid11_part1156 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 20 1 false (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 44 1 false (10),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.cycle 20 1 false (0),
.cycle 8 6 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1156) = true := by rfl

def kid11_part1157 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 27 5 false (2),
.cycle 12 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 12 7 true (3),
.cycle 19 11 true (3),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 27 5 false (2),
.cycle 6 10 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 12 6 true (4)
])
theorem kid11_part1157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1157) = true := by rfl

def kid11_part1158 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 17 (5,true),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (5,true),
.cycle 0 14 true (0),
.last 20 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid11_part1158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1158) = true := by rfl

def kid11_part1159 : Audit := .cycle 1 13 true (1)
theorem kid11_part1159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1159) = true := by rfl

def kid11_part1160 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 26 1 false (0),
.cycle 5 14 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 25 (2,true),
.cycle 11 7 true (2),
.cycle 51 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 34, 32, 64],64⟩,
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 26 1 false (0),
.cycle 1 19 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 9 7 true (2),
.cycle 5 14 true (1)
])
theorem kid11_part1160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1160) = true := by rfl

def kid11_part1161 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1161) = true := by rfl

def kid11_part1162 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 1 20 true (1),
.cycle 22 1 false (-2),
.cycle 17 6 false (1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 7 14 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 4 14 true (1),
.cycle 22 1 false (-2),
.cycle 18 3 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (3),
.cycle 12 6 true (3)
])
theorem kid11_part1162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1162) = true := by rfl

def kid11_part1163 : Audit := .cycle 1 11 true (1)
theorem kid11_part1163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1163) = true := by rfl

def kid11_part1164 : Audit := .cycle 7 4 true (3)
theorem kid11_part1164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1164) = true := by rfl

def kid11_part1165 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
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
.cycle 1 15 true (1),
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
theorem kid11_part1165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1165) = true := by rfl

def kid11_part1166 : Audit := .cycle 0 12 true (0)
theorem kid11_part1166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1166) = true := by rfl

def kid11_part1167 : Audit := .cycle 9 3 true (4)
theorem kid11_part1167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1167) = true := by rfl

def kid11_part1168 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (4),
.cycle 23 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (2,true),
.cycle 3 9 true (1),
.cycle 8 9 true (4),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.cycle 22 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1168) = true := by rfl

def kid11_part1144 : Audit := .split 10 (4,true) (byMove [(kid11_part1145),(kid11_part1146),(kid11_part1147),(kid11_part1148),(kid11_part1149),(kid11_part1150),(kid11_part1151),(kid11_part1152),(kid11_part1153),(kid11_part1154),(kid11_part1155),(kid11_part1156),(kid11_part1157),(kid11_part1158),(kid11_part1159),(kid11_part1160),(kid11_part1161),(kid11_part1162),(kid11_part1163),(kid11_part1164),(kid11_part1165),(kid11_part1166),(kid11_part1167),(kid11_part1168)])

theorem kid11_part1144_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1144) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1145),(kid11_part1146),(kid11_part1147),(kid11_part1148),(kid11_part1149),(kid11_part1150),(kid11_part1151),(kid11_part1152),(kid11_part1153),(kid11_part1154),(kid11_part1155),(kid11_part1156),(kid11_part1157),(kid11_part1158),(kid11_part1159),(kid11_part1160),(kid11_part1161),(kid11_part1162),(kid11_part1163),(kid11_part1164),(kid11_part1165),(kid11_part1166),(kid11_part1167),(kid11_part1168)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1145_checked

  · exact kid11_part1151_checked

  · exact kid11_part1157_checked

  · exact kid11_part1163_checked

  · exact kid11_part1146_checked

  · exact kid11_part1152_checked

  · exact kid11_part1158_checked

  · exact kid11_part1164_checked

  · exact kid11_part1147_checked

  · exact kid11_part1153_checked

  · exact kid11_part1159_checked

  · exact kid11_part1165_checked

  · exact kid11_part1148_checked

  · exact kid11_part1154_checked

  · exact kid11_part1160_checked

  · exact kid11_part1166_checked

  · exact kid11_part1149_checked

  · exact kid11_part1155_checked

  · exact kid11_part1161_checked

  · exact kid11_part1167_checked

  · exact kid11_part1150_checked

  · exact kid11_part1156_checked

  · exact kid11_part1162_checked

  · exact kid11_part1168_checked

def kid11_part1170 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 0 22 true (0),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 12 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (4),
.cycle 12 6 true (4)
])
theorem kid11_part1170_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1170) = true := by rfl

def kid11_part1171 : Audit := .cycle 0 14 true (0)
theorem kid11_part1171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1171) = true := by rfl

def kid11_part1172 : Audit := .cycle 2 16 true (1)
theorem kid11_part1172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1172) = true := by rfl

def kid11_part1173 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.cycle 1 28 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 1 26 true (1),
.cycle 3 13 true (1),
.last 18 (4,true),
.cycle 8 8 true (2),
.cycle 6 10 true (2),
.cycle 1 20 true (1),
.cycle 5 14 true (1),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 7 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 7 13 true (2),
.cycle 7 14 true (2)
])
theorem kid11_part1173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1173) = true := by rfl

def kid11_part1174 : Audit := .split 17 (4,true) (byMove [
.cycle 0 58 true (-2),
.cycle 13 7 false (1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 33, 16, 64],[2, 32, 64, 1, 1, 18, 64],64⟩,
.last 19 (2,true),
.cycle 0 39 true (-2),
.cycle 12 11 false (2),
.cycle 29 3 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 14 5 false (0),
.last 18 (2,true),
.last 21 (2,true),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 17 32 true (-1),
.last 19 (2,true),
.cycle 0 50 true (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1697, 512, 1024, 128, 256, 8, 128, 544, 1024, 4096],[128, 32, 4096, 1, 512, 1152, 128, 32, 4096, 1, 512, 128, 4096],4096⟩,
.cycle 13 8 false (1),
.cycle 21 6 true (3)
])
theorem kid11_part1174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1174) = true := by rfl

def kid11_part1175 : Audit := .cycle 18 3 false (0)
theorem kid11_part1175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1175) = true := by rfl

def kid11_part1176 : Audit := .cycle 1 11 true (1)
theorem kid11_part1176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1176) = true := by rfl

def kid11_part1177 : Audit := .cycle 7 4 true (3)
theorem kid11_part1177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1177) = true := by rfl

def kid11_part1178 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 18 true (2),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4096, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],4112⟩,
.cycle 10 9 true (2),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4096, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 32, 4, 1, 4096, 4, 128, 32, 4, 1, 4096, 4, 4096],4112⟩,
.cycle 0 14 true (0),
.cycle 10 16 true (2),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1178) = true := by rfl

def kid11_part1179 : Audit := .cycle 0 12 true (0)
theorem kid11_part1179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1179) = true := by rfl

def kid11_part1180 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 19 4 false (1),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 10 9 true (2),
.cycle 11 3 true (5),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 1 22 true (1),
.cycle 19 4 false (1),
.cycle 10 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1180) = true := by rfl

def kid11_part1181 : Audit := .cycle 8 4 true (4)
theorem kid11_part1181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1181) = true := by rfl

def kid11_part1182 : Audit := .cycle 7 8 true (3)
theorem kid11_part1182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1182) = true := by rfl

def kid11_part1183 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 23 3 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 12 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 10 4 true (3),
.cycle 5 20 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 23 3 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 12 true (3)
])
theorem kid11_part1183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1183) = true := by rfl

def kid11_part1184 : Audit := .cycle 1 13 true (1)
theorem kid11_part1184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1184) = true := by rfl

def kid11_part1185 : Audit := .cycle 4 12 true (1)
theorem kid11_part1185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1185) = true := by rfl

def kid11_part1186 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 28 13 true (2),
.last 18 (2,true),
.cycle 12 9 false (2),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 10 10 false (4),
.cycle 34 12 true (2),
.last 18 (2,true),
.cycle 30 20 true (0),
.cycle 23 3 true (5),
.cycle 12 6 false (2),
.cycle 12 8 false (2),
.cycle 14 5 false (0),
.last 18 (2,true),
.cycle 12 9 false (2),
.cycle 15 4 false (-1),
.cycle 14 4 false (0),
.cycle 17 6 true (-1),
.cycle 12 12 false (2),
.last 18 (2,true),
.cycle 10 20 false (4),
.cycle 21 5 true (3),
.cycle 17 2 true (-1)
])
theorem kid11_part1186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1186) = true := by rfl

def kid11_part1187 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 7 9 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 17 4 false (0),
.cycle 18 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 3 true (5),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 10 4 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 17 4 false (0),
.cycle 18 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 20 5 false (2)
])
theorem kid11_part1187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1187) = true := by rfl

def kid11_part1188 : Audit := .cycle 1 11 true (1)
theorem kid11_part1188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1188) = true := by rfl

def kid11_part1189 : Audit := .cycle 7 4 true (3)
theorem kid11_part1189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1189) = true := by rfl

def kid11_part1190 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
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
.cycle 1 15 true (1),
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
theorem kid11_part1190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1190) = true := by rfl

def kid11_part1191 : Audit := .cycle 0 12 true (0)
theorem kid11_part1191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1191) = true := by rfl

def kid11_part1192 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 19 4 false (1),
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
.cycle 19 4 false (1),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1192) = true := by rfl

def kid11_part1193 : Audit := .cycle 8 4 true (4)
theorem kid11_part1193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1193) = true := by rfl

def kid11_part1169 : Audit := .split 10 (5,true) (byMove [(kid11_part1170),(kid11_part1171),(kid11_part1172),(kid11_part1173),(kid11_part1174),(kid11_part1175),(kid11_part1176),(kid11_part1177),(kid11_part1178),(kid11_part1179),(kid11_part1180),(kid11_part1181),(kid11_part1182),(kid11_part1183),(kid11_part1184),(kid11_part1185),(kid11_part1186),(kid11_part1187),(kid11_part1188),(kid11_part1189),(kid11_part1190),(kid11_part1191),(kid11_part1192),(kid11_part1193)])

theorem kid11_part1169_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1169) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part1170),(kid11_part1171),(kid11_part1172),(kid11_part1173),(kid11_part1174),(kid11_part1175),(kid11_part1176),(kid11_part1177),(kid11_part1178),(kid11_part1179),(kid11_part1180),(kid11_part1181),(kid11_part1182),(kid11_part1183),(kid11_part1184),(kid11_part1185),(kid11_part1186),(kid11_part1187),(kid11_part1188),(kid11_part1189),(kid11_part1190),(kid11_part1191),(kid11_part1192),(kid11_part1193)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1170_checked

  · exact kid11_part1176_checked

  · exact kid11_part1182_checked

  · exact kid11_part1188_checked

  · exact kid11_part1171_checked

  · exact kid11_part1177_checked

  · exact kid11_part1183_checked

  · exact kid11_part1189_checked

  · exact kid11_part1172_checked

  · exact kid11_part1178_checked

  · exact kid11_part1184_checked

  · exact kid11_part1190_checked

  · exact kid11_part1173_checked

  · exact kid11_part1179_checked

  · exact kid11_part1185_checked

  · exact kid11_part1191_checked

  · exact kid11_part1174_checked

  · exact kid11_part1180_checked

  · exact kid11_part1186_checked

  · exact kid11_part1192_checked

  · exact kid11_part1175_checked

  · exact kid11_part1181_checked

  · exact kid11_part1187_checked

  · exact kid11_part1193_checked

def kid11_part1194 : Audit := .cycle 0 10 true (0)
theorem kid11_part1194_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1194) = true := by rfl

def kid11_part1195 : Audit := .cycle 1 9 true (1)
theorem kid11_part1195_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1195) = true := by rfl

def kid11_part1196 : Audit := .cycle 2 8 true (1)
theorem kid11_part1196_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1196) = true := by rfl

def kid11_part1197 : Audit := .cycle 1 12 true (1)
theorem kid11_part1197_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1197) = true := by rfl

def kid11_part1198 : Audit := .cycle 9 1 true (5)
theorem kid11_part1198_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1198) = true := by rfl

def kid11_part1199 : Audit := .cycle 8 2 true (4)
theorem kid11_part1199_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1199) = true := by rfl

def kid11_part1103 : Audit := .split 9 (4,false) (byMove [(kid11_part1104),(kid11_part1105),(kid11_part1106),(kid11_part1107),(kid11_part1108),(kid11_part1109),(kid11_part1110),(kid11_part1111),(kid11_part1112),(kid11_part1113),(kid11_part1114),(kid11_part1115),(kid11_part1116),(kid11_part1117),(kid11_part1118),(kid11_part1143),(kid11_part1144),(kid11_part1169),(kid11_part1194),(kid11_part1195),(kid11_part1196),(kid11_part1197),(kid11_part1198),(kid11_part1199)])

theorem kid11_part1103_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (kid11_part1103) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part1104),(kid11_part1105),(kid11_part1106),(kid11_part1107),(kid11_part1108),(kid11_part1109),(kid11_part1110),(kid11_part1111),(kid11_part1112),(kid11_part1113),(kid11_part1114),(kid11_part1115),(kid11_part1116),(kid11_part1117),(kid11_part1118),(kid11_part1143),(kid11_part1144),(kid11_part1169),(kid11_part1194),(kid11_part1195),(kid11_part1196),(kid11_part1197),(kid11_part1198),(kid11_part1199)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1104_checked

  · exact kid11_part1110_checked

  · exact kid11_part1116_checked

  · exact kid11_part1194_checked

  · exact kid11_part1105_checked

  · exact kid11_part1111_checked

  · exact kid11_part1117_checked

  · exact kid11_part1195_checked

  · exact kid11_part1106_checked

  · exact kid11_part1112_checked

  · exact kid11_part1118_checked

  · exact kid11_part1196_checked

  · exact kid11_part1107_checked

  · exact kid11_part1113_checked

  · exact kid11_part1143_checked

  · exact kid11_part1197_checked

  · exact kid11_part1108_checked

  · exact kid11_part1114_checked

  · exact kid11_part1144_checked

  · exact kid11_part1198_checked

  · exact kid11_part1109_checked

  · exact kid11_part1115_checked

  · exact kid11_part1169_checked

  · exact kid11_part1199_checked

def kid11_part1200 : Audit := .cycle 8 1 true (4)
theorem kid11_part1200_checked : zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some ⟨true,true,5⟩)) (kid11_part1200) = true := by rfl

def kid11 : Audit := .split 8 (5,false) (byMove [(kid11_part1),(kid11_part2),(kid11_part3),(kid11_part4),(kid11_part5),(kid11_part198),(kid11_part247),(kid11_part248),(kid11_part249),(kid11_part370),(kid11_part419),(kid11_part564),(kid11_part565),(kid11_part566),(kid11_part687),(kid11_part688),(kid11_part689),(kid11_part978),(kid11_part1099),(kid11_part1100),(kid11_part1101),(kid11_part1102),(kid11_part1103),(kid11_part1200)])

theorem check11 : zipCheck 175 (child39 ⟨false,true,5⟩) (kid11) = true := by

  change (zipQueryOK 175 (child39 ⟨false,true,5⟩) 8 (5,false) && allMoves (fun mv => zipCheck 175 (refine (child39 ⟨false,true,5⟩) (5,false) (some mv)) (byMove [(kid11_part1),(kid11_part2),(kid11_part3),(kid11_part4),(kid11_part5),(kid11_part198),(kid11_part247),(kid11_part248),(kid11_part249),(kid11_part370),(kid11_part419),(kid11_part564),(kid11_part565),(kid11_part566),(kid11_part687),(kid11_part688),(kid11_part689),(kid11_part978),(kid11_part1099),(kid11_part1100),(kid11_part1101),(kid11_part1102),(kid11_part1103),(kid11_part1200)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1_checked

  · exact kid11_part247_checked

  · exact kid11_part565_checked

  · exact kid11_part1099_checked

  · exact kid11_part2_checked

  · exact kid11_part248_checked

  · exact kid11_part566_checked

  · exact kid11_part1100_checked

  · exact kid11_part3_checked

  · exact kid11_part249_checked

  · exact kid11_part687_checked

  · exact kid11_part1101_checked

  · exact kid11_part4_checked

  · exact kid11_part370_checked

  · exact kid11_part688_checked

  · exact kid11_part1102_checked

  · exact kid11_part5_checked

  · exact kid11_part419_checked

  · exact kid11_part689_checked

  · exact kid11_part1103_checked

  · exact kid11_part198_checked

  · exact kid11_part564_checked

  · exact kid11_part978_checked

  · exact kid11_part1200_checked

end BB6.Agent11Raw39
