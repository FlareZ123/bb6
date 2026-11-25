import Raw39B0RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid08_part1 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 64, 64, 64],[2, 4, 4, 1, 64, 64, 64],112⟩
theorem kid08_part1_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,0⟩)) (kid08_part1) = true := by rfl

def kid08_part2 : Audit := .cycle 0 51 true (0)
theorem kid08_part2_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,1⟩)) (kid08_part2) = true := by rfl

def kid08_part3 : Audit := .cycle 19 1 false (3)
theorem kid08_part3_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,2⟩)) (kid08_part3) = true := by rfl

def kid08_part4 : Audit := .cycle 18 1 false (2)
theorem kid08_part4_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,3⟩)) (kid08_part4) = true := by rfl

def kid08_part6 : Audit := .cycle 0 57 true (0)
theorem kid08_part6_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part6) = true := by rfl

def kid08_part7 : Audit := .cycle 45 1 false (7)
theorem kid08_part7_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part7) = true := by rfl

def kid08_part8 : Audit := .cycle 20 1 false (2)
theorem kid08_part8_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part8) = true := by rfl

def kid08_part9 : Audit := .cycle 19 1 false (1)
theorem kid08_part9_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part9) = true := by rfl

def kid08_part10 : Audit := .cycle 18 1 false (2)
theorem kid08_part10_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part10) = true := by rfl

def kid08_part12 : Audit := .cycle 0 42 true (0)
theorem kid08_part12_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part12) = true := by rfl

def kid08_part13 : Audit := .cycle 38 1 false (10)
theorem kid08_part13_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part13) = true := by rfl

def kid08_part14 : Audit := .cycle 21 1 false (1)
theorem kid08_part14_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part14) = true := by rfl

def kid08_part15 : Audit := .cycle 20 1 false (0)
theorem kid08_part15_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part15) = true := by rfl

def kid08_part16 : Audit := .cycle 18 2 false (2)
theorem kid08_part16_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part16) = true := by rfl

def kid08_part17 : Audit := .cycle 19 1 false (1)
theorem kid08_part17_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part17) = true := by rfl

def kid08_part18 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 38 true (0),
.cycle 0 30 true (0),
.cycle 0 38 true (0),
.last 24 (5,true),
.cycle 0 36 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 128, 1, 128, 256, 32768, 2, 262144, 4096, 128, 256, 8, 4, 128, 1, 262144],[2, 4, 256, 1, 2, 262144, 8192, 16384, 256, 4096, 8192, 262144, 2, 4, 262144, 1, 2, 262144, 262144],263168⟩,
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.cycle 0 38 true (0),
.cycle 0 63 true (0),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 17 7 false (4),
.cycle 29 1 false (3),
.last 31 (5,true),
.last 24 (5,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.last 25 (5,true),
.cycle 0 57 true (0)
])
theorem kid08_part18_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part18) = true := by rfl

def kid08_part19 : Audit := .cycle 0 57 true (0)
theorem kid08_part19_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part19) = true := by rfl

def kid08_part20 : Audit := .cycle 21 1 false (3)
theorem kid08_part20_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part20) = true := by rfl

def kid08_part21 : Audit := .cycle 20 1 false (2)
theorem kid08_part21_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part21) = true := by rfl

def kid08_part22 : Audit := .cycle 18 2 true (1)
theorem kid08_part22_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part22) = true := by rfl

def kid08_part23 : Audit := .split 22 (5,true) (byMove [
.last 26 (4,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 29 1 true (3),
.cycle 26 1 true (4),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 25 1 true (3),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 24 1 true (6),
.cycle 39 1 true (3),
.last 25 (4,true),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.cycle 20 4 true (2),
.cycle 21 2 true (3),
.cycle 0 63 true (0),
.cycle 33 1 true (5),
.last 24 (4,true),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part23_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part23) = true := by rfl

def kid08_part24 : Audit := .cycle 11 12 true (0)
theorem kid08_part24_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part24) = true := by rfl

def kid08_part25 : Audit := .split 22 (4,true) (byMove [
.cycle 0 98 true (-2),
.cycle 31 1 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.cycle 19 4 true (0),
.cycle 11 15 false (3),
.cycle 20 3 false (1),
.last 260 (5,true),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 0 69 true (0),
.cycle 1 48 true (0),
.cycle 40 1 false (10),
.cycle 0 75 true (0),
.last 24 (5,true),
.cycle 16 8 false (3)
])
theorem kid08_part25_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part25) = true := by rfl

def kid08_part26 : Audit := .split 25 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 28 1 false (4),
.cycle 0 44 true (-1),
.cycle 0 32 true (0),
.cycle 0 44 true (-1),
.last 26 (5,true),
.cycle 0 40 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 128, 1, 128, 256, 32768, 524290, 16777216, 16777472, 128, 256, 2097152, 4, 16809984, 262144, 128, 256, 8, 256, 128, 1, 16777216],[2, 4, 256, 1, 2, 16777216, 8192, 16384, 256, 4096, 8192, 16777216, 524288, 1048576, 16777216, 262144, 524288, 16777216, 2, 4, 16777220, 1, 2, 16777216, 16777216],16845824⟩,
.cycle 0 28 true (0),
.cycle 0 36 true (0),
.cycle 17 11 false (4),
.cycle 0 75 true (0),
.cycle 0 30 true (0),
.cycle 0 36 true (0),
.cycle 17 9 false (4),
.cycle 31 1 false (3),
.last 35 (5,true),
.last 26 (5,true),
.cycle 0 40 true (0),
.cycle 1 28 true (0),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.last 27 (5,true),
.cycle 17 13 false (4)
])
theorem kid08_part26_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part26) = true := by rfl

def kid08_part27 : Audit := .cycle 20 1 false (0)
theorem kid08_part27_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part27) = true := by rfl

def kid08_part28 : Audit := .cycle 18 2 false (2)
theorem kid08_part28_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part28) = true := by rfl

def kid08_part29 : Audit := .cycle 19 1 false (1)
theorem kid08_part29_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part29) = true := by rfl

def kid08_part30 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 50 true (0),
.cycle 27 1 false (1),
.cycle 0 30 true (0),
.cycle 0 38 true (-1),
.last 24 (5,true),
.cycle 0 36 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 128, 64, 128, 256, 32768, 2, 262144, 64, 128, 256, 8, 4, 128, 64, 262144],[2, 4, 256, 1, 2, 262144, 8192, 16384, 256, 4096, 8192, 262144, 2, 4, 262144, 1, 2, 262144, 262144],263168⟩,
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.cycle 0 38 true (0),
.cycle 0 69 true (0),
.cycle 0 28 true (0),
.last 27 (5,true),
.cycle 0 32 true (0),
.cycle 0 37 true (0),
.last 32 (5,true),
.last 24 (5,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.last 25 (5,true),
.cycle 0 69 true (0)
])
theorem kid08_part30_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part30) = true := by rfl

def kid08_part31 : Audit := .cycle 0 57 true (0)
theorem kid08_part31_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part31) = true := by rfl

def kid08_part32 : Audit := .cycle 45 1 false (7)
theorem kid08_part32_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part32) = true := by rfl

def kid08_part33 : Audit := .split 25 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 47 1 false (9),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 0 34 true (0),
.cycle 45 1 false (9),
.cycle 49 1 false (11),
.cycle 37 1 false (9),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 33 1 false (7),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.cycle 23 3 false (4),
.cycle 51 1 false (11),
.cycle 26 1 false (2),
.cycle 0 34 true (0),
.last 78 (5,true),
.last 73 (5,true),
.cycle 1 28 true (0),
.cycle 0 28 true (0),
.cycle 31 1 false (7),
.last 27 (5,true),
.cycle 0 28 true (0)
])
theorem kid08_part33_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part33) = true := by rfl

def kid08_part34 : Audit := .split 21 (5,true) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.cycle 19 3 false (2),
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 18 4 true (1),
.last 26 (4,true),
.cycle 11 14 true (0),
.last 24 (4,true),
.last 27 (4,true),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.last 23 (4,true),
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.last 27 (4,true),
.cycle 20 2 true (1),
.last 26 (4,true)
])
theorem kid08_part34_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part34) = true := by rfl

def kid08_part35 : Audit := .split 22 (5,true) (byMove [
.last 26 (4,true),
.cycle 0 26 true (0),
.last 24 (4,true),
.cycle 35 1 true (5),
.last 23 (4,true),
.cycle 37 1 true (-1),
.cycle 52 1 true (8),
.cycle 64 1 true (10),
.cycle 35 1 true (3),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 24 1 true (6),
.cycle 27 1 true (3),
.cycle 47 1 true (-1),
.last 24 (4,true),
.cycle 5 18 true (0),
.last 23 (4,true),
.cycle 24 3 false (2),
.cycle 0 63 true (0),
.cycle 33 1 true (5),
.last 24 (4,true),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part35_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part35) = true := by rfl

def kid08_part11 : Audit := .split 19 (5,false) (byMove [(kid08_part12),(kid08_part13),(kid08_part14),(kid08_part15),(kid08_part16),(kid08_part17),(kid08_part18),(kid08_part19),(kid08_part20),(kid08_part21),(kid08_part22),(kid08_part23),(kid08_part24),(kid08_part25),(kid08_part26),(kid08_part27),(kid08_part28),(kid08_part29),(kid08_part30),(kid08_part31),(kid08_part32),(kid08_part33),(kid08_part34),(kid08_part35)])

theorem kid08_part11_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part11) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part12),(kid08_part13),(kid08_part14),(kid08_part15),(kid08_part16),(kid08_part17),(kid08_part18),(kid08_part19),(kid08_part20),(kid08_part21),(kid08_part22),(kid08_part23),(kid08_part24),(kid08_part25),(kid08_part26),(kid08_part27),(kid08_part28),(kid08_part29),(kid08_part30),(kid08_part31),(kid08_part32),(kid08_part33),(kid08_part34),(kid08_part35)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part12_checked

  · exact kid08_part18_checked

  · exact kid08_part24_checked

  · exact kid08_part30_checked

  · exact kid08_part13_checked

  · exact kid08_part19_checked

  · exact kid08_part25_checked

  · exact kid08_part31_checked

  · exact kid08_part14_checked

  · exact kid08_part20_checked

  · exact kid08_part26_checked

  · exact kid08_part32_checked

  · exact kid08_part15_checked

  · exact kid08_part21_checked

  · exact kid08_part27_checked

  · exact kid08_part33_checked

  · exact kid08_part16_checked

  · exact kid08_part22_checked

  · exact kid08_part28_checked

  · exact kid08_part34_checked

  · exact kid08_part17_checked

  · exact kid08_part23_checked

  · exact kid08_part29_checked

  · exact kid08_part35_checked

def kid08_part36 : Audit := .cycle 0 23 true (0)
theorem kid08_part36_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part36) = true := by rfl

def kid08_part37 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 0 26 true (0),
.split 22 (5,false) (byMove [
.cycle 0 86 true (0),
.cycle 0 32 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 41 1 false (9),
.cycle 22 1 false (2),
.last 27 (5,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 37 1 false (9),
.last 25 (5,true),
.cycle 57 1 false (9),
.cycle 19 4 false (4),
.last 29 (5,true),
.cycle 23 1 false (1),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 27 (5,true),
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 41 1 false (9),
.cycle 18 34 true (2),
.last 25 (5,true)
]),
.cycle 41 1 false (11),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 25 1 false (7),
.split 22 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 37 1 false (9),
.cycle 22 1 false (4),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 34 1 false (12),
.last 23 (5,true),
.cycle 16 88 true (2),
.cycle 19 4 true (3),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.cycle 35 1 false (9),
.cycle 22 1 false (4),
.cycle 0 63 true (0),
.cycle 41 1 false (11),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.last 50 (5,true),
.last 23 (5,true)
]),
.cycle 0 26 true (0),
.cycle 19 3 false (4),
.cycle 43 1 false (11),
.cycle 22 1 false (2),
.cycle 0 26 true (0),
.split 22 (5,false) (byMove [
.last 27 (5,true),
.cycle 0 89 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (4),
.cycle 22 1 false (2),
.cycle 37 1 false (9),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 43 1 false (11),
.cycle 21 2 true (2),
.last 23 (5,true),
.cycle 0 30 true (0),
.cycle 19 4 false (4),
.cycle 41 1 false (9),
.cycle 23 1 false (1),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 19 34 true (2),
.cycle 0 26 true (0),
.cycle 20 3 false (4),
.cycle 63 28 true (7),
.last 24 (5,true),
.last 23 (5,true)
]),
.cycle 16 42 true (2),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.cycle 31 57 true (5),
.split 22 (5,false) (byMove [
.cycle 37 1 false (9),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 43 1 false (11),
.cycle 21 2 true (3),
.last 23 (5,true),
.cycle 0 85 true (0),
.cycle 31 57 true (5),
.cycle 17 78 true (2),
.cycle 0 24 true (0),
.last 51 (5,true),
.last 23 (5,true),
.cycle 35 1 false (9),
.cycle 41 1 false (9),
.cycle 17 6 true (2),
.cycle 27 1 false (7),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 63 true (0),
.cycle 16 42 true (2),
.cycle 2 24 true (0),
.cycle 0 24 true (0),
.last 50 (5,true),
.last 23 (5,true)
])
])
theorem kid08_part37_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part37) = true := by rfl

def kid08_part38 : Audit := .cycle 30 1 false (10)
theorem kid08_part38_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part38) = true := by rfl

def kid08_part39 : Audit := .cycle 19 1 false (3)
theorem kid08_part39_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part39) = true := by rfl

def kid08_part40 : Audit := .split 20 (4,true) (byMove [
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 30 1 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 27 1 true (3),
.cycle 21 1 false (3),
.cycle 32 1 true (6),
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 25 1 true (5),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 20 4 false (4),
.cycle 34 1 true (6),
.cycle 22 1 false (2),
.cycle 19 3 false (4),
.cycle 21 1 false (3),
.cycle 32 1 true (6),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.cycle 25 1 true (5),
.last 23 (5,true)
]),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 22 1 true (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 22 1 true (6),
.last 22 (5,false),
.cycle 32 1 true (6),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 24 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.cycle 22 1 true (6),
.last 22 (5,false)
]),
.cycle 24 1 true (4),
.cycle 20 3 false (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.split 21 (5,false) (byMove [
.last 26 (5,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 18 4 true (2),
.cycle 21 1 false (3),
.cycle 25 1 false (7),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.cycle 32 1 false (10),
.cycle 20 2 true (3),
.last 22 (5,true),
.cycle 32 1 true (4),
.cycle 20 4 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 19 3 false (4),
.cycle 21 1 false (3),
.cycle 63 1 true (11),
.cycle 24 1 true (4),
.cycle 20 3 false (4),
.cycle 51 1 true (9),
.last 23 (5,true),
.last 22 (5,true)
]),
.cycle 0 57 true (0),
.cycle 30 1 true (6),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.split 21 (5,true) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 true (3),
.cycle 0 23 true (0),
.last 23 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.last 57 (5,false),
.cycle 30 1 true (6),
.cycle 28 1 false (8),
.cycle 22 1 true (6),
.last 22 (5,false),
.cycle 25 1 false (7),
.cycle 24 1 true (4),
.last 26 (5,false),
.cycle 32 1 false (10),
.cycle 20 2 true (4),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 22 1 true (6),
.last 22 (5,false)
])
])
theorem kid08_part40_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part40) = true := by rfl

def kid08_part42 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 38 true (0),
.cycle 0 30 true (0),
.cycle 0 38 true (0),
.last 24 (5,true),
.cycle 0 36 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 2, 64, 64],64⟩,
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.last 25 (5,true),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 17 7 false (4),
.cycle 29 1 false (3),
.last 26 (5,true),
.last 24 (5,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.last 25 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 32, 64, 64],64⟩
])
theorem kid08_part42_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part42) = true := by rfl

def kid08_part43 : Audit := .cycle 0 57 true (0)
theorem kid08_part43_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part43) = true := by rfl

def kid08_part44 : Audit := .cycle 21 1 false (3)
theorem kid08_part44_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part44) = true := by rfl

def kid08_part45 : Audit := .cycle 20 1 false (2)
theorem kid08_part45_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part45) = true := by rfl

def kid08_part46 : Audit := .cycle 18 2 true (2)
theorem kid08_part46_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part46) = true := by rfl

def kid08_part47 : Audit := .cycle 19 1 false (3)
theorem kid08_part47_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part47) = true := by rfl

def kid08_part48 : Audit := .cycle 23 1 false (7)
theorem kid08_part48_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part48) = true := by rfl

def kid08_part49 : Audit := .cycle 32 1 false (10)
theorem kid08_part49_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part49) = true := by rfl

def kid08_part50 : Audit := .cycle 27 1 false (7)
theorem kid08_part50_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part50) = true := by rfl

def kid08_part51 : Audit := .cycle 30 1 false (10)
theorem kid08_part51_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part51) = true := by rfl

def kid08_part52 : Audit := .split 20 (4,true) (byMove [
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 2 true (4),
.last 23 (5,true),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true),
.cycle 24 2 true (4),
.cycle 20 3 false (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 22 (5,true),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true)
])
theorem kid08_part52_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part52) = true := by rfl

def kid08_part53 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 25 1 true (5),
.cycle 24 1 true (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6),
.cycle 25 1 true (5),
.last 23 (4,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 2 true (3),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6)
])
theorem kid08_part53_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part53) = true := by rfl

def kid08_part54 : Audit := .cycle 26 12 true (4)
theorem kid08_part54_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part54) = true := by rfl

def kid08_part55 : Audit := .split 22 (4,true) (byMove [
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (3),
.cycle 19 4 false (3),
.cycle 0 31 true (0),
.cycle 37 1 false (9),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.last 24 (5,true),
.cycle 19 4 true (2),
.cycle 14 43 true (0),
.cycle 20 3 false (3),
.cycle 0 58 true (0),
.cycle 23 1 false (1),
.last 24 (5,true),
.cycle 19 4 false (3),
.cycle 0 31 true (0),
.cycle 1 28 true (0),
.cycle 0 63 true (0),
.cycle 44 1 false (10),
.last 24 (5,true),
.cycle 16 8 true (2)
])
theorem kid08_part55_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part55) = true := by rfl

def kid08_part56 : Audit := .cycle 25 1 false (7)
theorem kid08_part56_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part56) = true := by rfl

def kid08_part57 : Audit := .cycle 20 1 false (2)
theorem kid08_part57_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part57) = true := by rfl

def kid08_part58 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 18 4 true (2),
.cycle 19 3 false (3),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.last 22 (4,true),
.cycle 23 3 true (5),
.cycle 30 14 true (4),
.last 24 (4,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 19 3 false (3),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.last 23 (4,true),
.cycle 5 87 true (0),
.last 22 (4,true),
.last 25 (4,true)
])
theorem kid08_part58_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part58) = true := by rfl

def kid08_part59 : Audit := .cycle 19 1 false (3)
theorem kid08_part59_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part59) = true := by rfl

def kid08_part60 : Audit := .cycle 0 59 true (0)
theorem kid08_part60_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part60) = true := by rfl

def kid08_part61 : Audit := .cycle 1 23 true (0)
theorem kid08_part61_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part61) = true := by rfl

def kid08_part62 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 41 1 false (11),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (5,true),
.cycle 33 1 false (9),
.cycle 0 26 true (0),
.cycle 20 3 false (4),
.cycle 43 1 false (11),
.cycle 22 1 false (2),
.last 23 (5,true),
.cycle 19 3 false (4),
.cycle 16 42 true (2),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (5,true),
.cycle 2 24 true (0)
])
theorem kid08_part62_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part62) = true := by rfl

def kid08_part63 : Audit := .cycle 5 77 true (0)
theorem kid08_part63_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part63) = true := by rfl

def kid08_part64 : Audit := .split 20 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.last 25 (5,true),
.cycle 32 2 true (6),
.last 25 (5,true),
.last 21 (5,true),
.cycle 47 2 true (9),
.cycle 57 2 true (11),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true),
.cycle 24 2 true (4),
.cycle 28 2 true (4),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 23 (5,true),
.last 21 (5,true),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true)
])
theorem kid08_part64_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part64) = true := by rfl

def kid08_part65 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 24 true (0),
.last 27 (4,true),
.cycle 33 1 true (7),
.last 21 (4,true),
.cycle 29 1 true (1),
.cycle 48 1 true (10),
.cycle 58 1 true (12),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6),
.cycle 25 1 true (5),
.cycle 29 1 true (5),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 19 3 false (4),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6)
])
theorem kid08_part65_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part65) = true := by rfl

def kid08_part41 : Audit := .split 19 (5,false) (byMove [(kid08_part42),(kid08_part43),(kid08_part44),(kid08_part45),(kid08_part46),(kid08_part47),(kid08_part48),(kid08_part49),(kid08_part50),(kid08_part51),(kid08_part52),(kid08_part53),(kid08_part54),(kid08_part55),(kid08_part56),(kid08_part57),(kid08_part58),(kid08_part59),(kid08_part60),(kid08_part61),(kid08_part62),(kid08_part63),(kid08_part64),(kid08_part65)])

theorem kid08_part41_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part41) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid08_part42),(kid08_part43),(kid08_part44),(kid08_part45),(kid08_part46),(kid08_part47),(kid08_part48),(kid08_part49),(kid08_part50),(kid08_part51),(kid08_part52),(kid08_part53),(kid08_part54),(kid08_part55),(kid08_part56),(kid08_part57),(kid08_part58),(kid08_part59),(kid08_part60),(kid08_part61),(kid08_part62),(kid08_part63),(kid08_part64),(kid08_part65)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part42_checked

  · exact kid08_part48_checked

  · exact kid08_part54_checked

  · exact kid08_part60_checked

  · exact kid08_part43_checked

  · exact kid08_part49_checked

  · exact kid08_part55_checked

  · exact kid08_part61_checked

  · exact kid08_part44_checked

  · exact kid08_part50_checked

  · exact kid08_part56_checked

  · exact kid08_part62_checked

  · exact kid08_part45_checked

  · exact kid08_part51_checked

  · exact kid08_part57_checked

  · exact kid08_part63_checked

  · exact kid08_part46_checked

  · exact kid08_part52_checked

  · exact kid08_part58_checked

  · exact kid08_part64_checked

  · exact kid08_part47_checked

  · exact kid08_part53_checked

  · exact kid08_part59_checked

  · exact kid08_part65_checked

def kid08_part66 : Audit := .cycle 14 35 true (0)
theorem kid08_part66_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part66) = true := by rfl

def kid08_part67 : Audit := .split 21 (4,true) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.split 22 (5,false) (byMove [
.cycle 0 98 true (-2),
.cycle 31 1 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.last 26 (5,true),
.cycle 11 15 false (3),
.cycle 19 4 false (2),
.last 155 (5,true),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 0 69 true (0),
.cycle 1 48 true (0),
.cycle 40 1 false (10),
.cycle 0 75 true (0),
.cycle 16 8 false (3),
.last 26 (5,true)
]),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 18 4 true (1),
.split 22 (5,false) (byMove [
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.cycle 22 1 false (2),
.cycle 0 34 true (0),
.cycle 29 1 false (7),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.last 29 (5,true),
.last 24 (5,true),
.cycle 14 43 true (0),
.cycle 19 4 true (1),
.cycle 0 38 true (0),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.cycle 22 1 false (2),
.cycle 0 37 true (0),
.cycle 1 40 true (0),
.cycle 0 63 true (0),
.cycle 44 1 false (10),
.cycle 16 8 true (1),
.last 24 (5,true)
]),
.cycle 11 14 true (0),
.cycle 19 3 false (2),
.cycle 17 11 false (4),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.split 22 (5,false) (byMove [
.last 27 (5,true),
.last 30 (5,true),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 0 69 true (0),
.cycle 25 1 false (3),
.cycle 17 6 false (3),
.last 28 (5,true),
.cycle 21 2 true (0),
.last 23 (5,true),
.cycle 16 11 false (3),
.cycle 19 4 false (2),
.cycle 0 75 true (-1),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 0 69 true (0),
.cycle 11 14 true (0),
.cycle 20 3 false (2),
.last 28 (5,true),
.last 24 (5,true),
.last 23 (5,true)
]),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 33 1 false (7),
.cycle 16 7 false (3),
.split 22 (5,false) (byMove [
.cycle 0 69 true (0),
.cycle 25 1 false (3),
.cycle 17 6 false (3),
.cycle 0 46 true (0),
.cycle 21 2 true (1),
.last 23 (5,true),
.cycle 0 34 true (0),
.cycle 42 34 true (6),
.cycle 14 39 true (0),
.cycle 51 1 false (7),
.last 29 (5,true),
.last 24 (5,true),
.cycle 36 1 false (10),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 33 1 false (7),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 40 true (0),
.cycle 1 40 true (0),
.cycle 0 63 true (0),
.cycle 13 47 true (0),
.cycle 16 11 false (3),
.last 24 (5,true)
])
])
theorem kid08_part67_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part67) = true := by rfl

def kid08_part68 : Audit := .cycle 0 42 true (0)
theorem kid08_part68_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part68) = true := by rfl

def kid08_part69 : Audit := .cycle 19 1 false (1)
theorem kid08_part69_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part69) = true := by rfl

def kid08_part70 : Audit := .cycle 18 1 false (2)
theorem kid08_part70_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part70) = true := by rfl

def kid08_part72 : Audit := .split 23 (4,true) (byMove [
.cycle 63 1 false (7),
.cycle 26 1 false (2),
.cycle 17 7 false (3),
.cycle 0 75 true (0),
.cycle 18 7 false (2),
.last 24 (5,true),
.cycle 0 44 true (0),
.cycle 0 69 true (0),
.cycle 11 14 true (0),
.cycle 40 1 false (10),
.cycle 18 12 true (0),
.cycle 0 75 true (0),
.cycle 27 1 false (3),
.cycle 16 8 false (3),
.cycle 17 7 false (3),
.cycle 0 75 true (0),
.cycle 18 7 false (2),
.last 24 (5,true),
.cycle 0 44 true (0),
.cycle 0 69 true (0),
.cycle 2 48 true (0),
.cycle 30 115 true (0),
.last 25 (5,true),
.cycle 0 75 true (0)
])
theorem kid08_part72_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part72) = true := by rfl

def kid08_part73 : Audit := .split 27 (5,true) (byMove [
.last 31 (4,true),
.cycle 0 31 true (0),
.cycle 0 56 true (0),
.cycle 0 35 true (0),
.cycle 0 48 true (0),
.cycle 0 42 true (0),
.last 63 (4,true),
.cycle 0 53 true (0),
.cycle 0 34 true (0),
.cycle 0 29 true (0),
.last 28 (4,true),
.cycle 0 93 true (0),
.cycle 0 46 true (-1),
.last 30 (4,true),
.last 67 (4,true),
.cycle 0 54 true (0),
.cycle 36 1 false (6),
.last 70 (4,true),
.last 60 (4,true),
.cycle 0 42 true (0),
.last 29 (4,true),
.cycle 0 29 true (0),
.last 28 (4,true),
.cycle 0 44 true (0)
])
theorem kid08_part73_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part73) = true := by rfl

def kid08_part74 : Audit := .cycle 21 1 false (1)
theorem kid08_part74_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part74) = true := by rfl

def kid08_part75 : Audit := .cycle 20 1 false (0)
theorem kid08_part75_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part75) = true := by rfl

def kid08_part76 : Audit := .cycle 18 2 false (2)
theorem kid08_part76_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part76) = true := by rfl

def kid08_part77 : Audit := .cycle 19 1 false (1)
theorem kid08_part77_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part77) = true := by rfl

def kid08_part78 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 43 1 false (9),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 0 30 true (0),
.last 29 (5,true),
.cycle 45 1 false (11),
.cycle 35 1 false (9),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 29 1 false (7),
.cycle 34 1 false (10),
.cycle 0 28 true (0),
.cycle 21 3 false (4),
.cycle 47 1 false (11),
.cycle 24 1 false (2),
.cycle 0 30 true (0),
.cycle 39 1 false (9),
.last 67 (5,true),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 29 1 false (7),
.last 25 (5,true),
.cycle 0 95 true (0)
])
theorem kid08_part78_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part78) = true := by rfl

def kid08_part79 : Audit := .cycle 32 1 false (10)
theorem kid08_part79_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part79) = true := by rfl

def kid08_part80 : Audit := .cycle 17 3 false (3)
theorem kid08_part80_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part80) = true := by rfl

def kid08_part81 : Audit := .split 25 (5,true) (byMove [
.last 29 (4,true),
.cycle 0 29 true (0),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 0 42 true (0),
.cycle 27 1 false (3),
.cycle 35 1 false (9),
.cycle 28 1 false (6),
.cycle 0 30 true (0),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 28 1 false (6),
.cycle 21 5 false (5),
.last 28 (4,true),
.cycle 37 1 false (9),
.cycle 26 1 false (2),
.cycle 32 1 false (6),
.cycle 37 1 false (9),
.last 56 (4,true),
.cycle 0 38 true (0),
.last 27 (4,true),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 3 25 true (0)
])
theorem kid08_part81_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part81) = true := by rfl

def kid08_part82 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 18 4 true (1),
.last 25 (5,true),
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 25 3 true (5),
.last 23 (5,true),
.cycle 14 39 true (0),
.cycle 20 3 false (2),
.last 27 (5,true),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 19 2 true (1),
.last 25 (5,true),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 22 (5,true),
.last 23 (5,true)
])
theorem kid08_part82_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part82) = true := by rfl

def kid08_part83 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 28 1 true (4),
.cycle 35 1 false (9),
.last 23 (4,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 24 (4,true),
.cycle 24 1 true (6),
.cycle 14 39 true (0),
.last 23 (4,true),
.cycle 39 1 false (9),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 19 2 true (1),
.last 56 (4,true),
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 23 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part83_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part83) = true := by rfl

def kid08_part84 : Audit := .split 24 (5,true) (byMove [
.last 28 (4,true),
.last 31 (4,true),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 18 7 false (2),
.last 33 (4,true),
.cycle 0 75 true (0),
.cycle 27 1 false (3),
.cycle 17 8 false (3),
.last 29 (4,true),
.last 25 (4,true),
.cycle 14 51 true (0),
.cycle 20 5 false (2),
.last 27 (4,true),
.cycle 0 81 true (-1),
.cycle 25 1 false (-1),
.cycle 18 7 false (2),
.cycle 19 6 false (2),
.cycle 0 75 true (0),
.cycle 11 16 true (0),
.last 26 (4,true),
.last 29 (4,true),
.last 25 (4,true),
.cycle 0 127 true (0)
])
theorem kid08_part84_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part84) = true := by rfl

def kid08_part85 : Audit := .split 22 (4,true) (byMove [
.last 31 (5,true),
.cycle 12 13 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 14 43 true (0),
.cycle 0 75 true (0),
.last 29 (5,true),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.cycle 19 4 true (0),
.last 31 (5,true),
.cycle 20 3 false (1),
.cycle 14 47 true (-1),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 14 43 true (0),
.cycle 0 75 true (0),
.last 29 (5,true),
.cycle 38 1 false (10),
.last 24 (5,true),
.cycle 16 8 false (3)
])
theorem kid08_part85_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part85) = true := by rfl

def kid08_part86 : Audit := .split 25 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 47 1 false (9),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 0 34 true (0),
.last 33 (5,true),
.cycle 49 1 false (11),
.cycle 37 1 false (9),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 33 1 false (7),
.cycle 38 1 false (10),
.cycle 0 30 true (0),
.cycle 23 3 false (4),
.cycle 51 1 false (11),
.cycle 26 1 false (2),
.cycle 0 34 true (0),
.cycle 45 1 false (9),
.last 73 (5,true),
.cycle 1 28 true (0),
.cycle 0 28 true (0),
.cycle 31 1 false (7),
.last 27 (5,true),
.cycle 17 10 true (0)
])
theorem kid08_part86_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part86) = true := by rfl

def kid08_part87 : Audit := .cycle 20 1 false (0)
theorem kid08_part87_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part87) = true := by rfl

def kid08_part88 : Audit := .cycle 18 2 false (2)
theorem kid08_part88_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part88) = true := by rfl

def kid08_part89 : Audit := .cycle 19 1 false (1)
theorem kid08_part89_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part89) = true := by rfl

def kid08_part90 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 72 true (0),
.cycle 0 32 true (0),
.cycle 0 30 true (0),
.last 25 (5,true),
.last 29 (5,true),
.last 65 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 8192, 64, 128, 256, 32768, 2, 262144, 64, 128, 256, 8, 4, 8192, 64, 262144],[2, 4, 256, 1, 2, 262144, 8192, 16384, 256, 4096, 8192, 262144, 2, 4, 262144, 1, 2, 262144, 262144],263168⟩,
.cycle 0 26 true (0),
.cycle 11 60 true (0),
.cycle 43 32 true (6),
.cycle 0 69 true (0),
.cycle 0 28 true (0),
.cycle 38 54 true (3),
.last 69 (5,true),
.cycle 0 30 true (0),
.last 25 (5,true),
.cycle 19 36 true (1),
.last 65 (5,true),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 24 32 true (1),
.last 25 (5,true),
.cycle 0 69 true (0)
])
theorem kid08_part90_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part90) = true := by rfl

def kid08_part91 : Audit := .cycle 14 35 true (0)
theorem kid08_part91_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part91) = true := by rfl

def kid08_part92 : Audit := .split 21 (4,true) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.cycle 40 1 false (10),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 18 4 true (1),
.cycle 0 63 true (0),
.cycle 11 14 true (0),
.cycle 20 3 false (2),
.cycle 17 11 false (4),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.cycle 19 3 false (2),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 33 1 false (7),
.last 23 (5,true),
.cycle 0 63 true (0)
])
theorem kid08_part92_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part92) = true := by rfl

def kid08_part93 : Audit := .split 25 (5,true) (byMove [
.last 29 (4,true),
.cycle 0 29 true (0),
.cycle 0 36 true (0),
.last 31 (4,true),
.cycle 0 35 true (-1),
.cycle 4 23 true (0),
.last 58 (4,true),
.cycle 7 19 true (0),
.cycle 0 30 true (0),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 0 83 true (0),
.cycle 0 37 true (0),
.last 28 (4,true),
.last 62 (4,true),
.cycle 0 34 true (0),
.cycle 0 50 true (-1),
.last 61 (4,true),
.last 56 (4,true),
.cycle 0 38 true (0),
.last 27 (4,true),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 29 31 true (4)
])
theorem kid08_part93_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part93) = true := by rfl

def kid08_part94 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 17 4 false (3),
.cycle 0 32 true (0),
.cycle 18 4 false (2),
.last 21 (5,true),
.last 25 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 8192, 1024, 128, 256, 32768, 2, 262144, 1024, 128, 256, 8, 4, 8192, 1024, 262144],[2, 4, 256, 1, 2, 262144, 8192, 16384, 256, 4096, 8192, 262144, 2, 4, 262144, 1, 2, 262144, 262144],396320⟩,
.cycle 14 35 true (0),
.cycle 45 1 false (7),
.cycle 25 3 true (5),
.last 23 (5,true),
.cycle 34 1 false (10),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.cycle 26 1 false (2),
.cycle 18 4 false (2),
.last 21 (5,true),
.last 25 (5,true),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 13 41 true (0),
.last 22 (5,true),
.last 23 (5,true)
])
theorem kid08_part94_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part94) = true := by rfl

def kid08_part95 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 17 4 false (3),
.last 25 (4,true),
.last 21 (4,true),
.cycle 44 1 true (-2),
.last 58 (4,true),
.last 23 (4,true),
.cycle 14 35 true (0),
.cycle 45 1 false (7),
.last 24 (4,true),
.cycle 24 1 true (6),
.cycle 34 1 false (10),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.last 25 (4,true),
.last 21 (4,true),
.cycle 19 3 false (2),
.last 56 (4,true),
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 13 41 true (0),
.last 23 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part95_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part95) = true := by rfl

def kid08_part71 : Audit := .split 19 (5,false) (byMove [(kid08_part72),(kid08_part73),(kid08_part74),(kid08_part75),(kid08_part76),(kid08_part77),(kid08_part78),(kid08_part79),(kid08_part80),(kid08_part81),(kid08_part82),(kid08_part83),(kid08_part84),(kid08_part85),(kid08_part86),(kid08_part87),(kid08_part88),(kid08_part89),(kid08_part90),(kid08_part91),(kid08_part92),(kid08_part93),(kid08_part94),(kid08_part95)])

theorem kid08_part71_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part71) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part72),(kid08_part73),(kid08_part74),(kid08_part75),(kid08_part76),(kid08_part77),(kid08_part78),(kid08_part79),(kid08_part80),(kid08_part81),(kid08_part82),(kid08_part83),(kid08_part84),(kid08_part85),(kid08_part86),(kid08_part87),(kid08_part88),(kid08_part89),(kid08_part90),(kid08_part91),(kid08_part92),(kid08_part93),(kid08_part94),(kid08_part95)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part72_checked

  · exact kid08_part78_checked

  · exact kid08_part84_checked

  · exact kid08_part90_checked

  · exact kid08_part73_checked

  · exact kid08_part79_checked

  · exact kid08_part85_checked

  · exact kid08_part91_checked

  · exact kid08_part74_checked

  · exact kid08_part80_checked

  · exact kid08_part86_checked

  · exact kid08_part92_checked

  · exact kid08_part75_checked

  · exact kid08_part81_checked

  · exact kid08_part87_checked

  · exact kid08_part93_checked

  · exact kid08_part76_checked

  · exact kid08_part82_checked

  · exact kid08_part88_checked

  · exact kid08_part94_checked

  · exact kid08_part77_checked

  · exact kid08_part83_checked

  · exact kid08_part89_checked

  · exact kid08_part95_checked

def kid08_part96 : Audit := .cycle 0 23 true (0)
theorem kid08_part96_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part96) = true := by rfl

def kid08_part97 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 1 32 true (0),
.cycle 0 28 true (0),
.cycle 1 32 true (0),
.split 22 (5,true) (byMove [
.cycle 1 32 true (0),
.cycle 0 32 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 1 32 true (0),
.last 23 (5,false),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 1 28 true (0),
.last 23 (5,false),
.cycle 1 48 true (0),
.last 26 (5,false),
.cycle 0 32 true (0),
.cycle 23 1 false (1),
.cycle 1 48 true (0),
.last 23 (5,false),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 30 true (0),
.last 29 (5,false),
.cycle 1 28 true (0),
.last 23 (5,false)
]),
.cycle 1 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 2, 64, 64],[2, 4, 4, 1, 2, 64, 64],96⟩,
.cycle 0 24 true (0),
.cycle 1 28 true (0),
.cycle 1 32 true (0),
.split 22 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 30 true (0),
.cycle 30 1 false (4),
.cycle 1 28 true (0),
.last 24 (5,true),
.cycle 0 57 true (0),
.cycle 7 16 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 1 25 true (0),
.last 23 (5,true),
.cycle 1 26 true (0),
.cycle 19 4 true (3),
.cycle 0 63 true (0),
.cycle 1 28 true (0),
.cycle 1 26 true (0),
.last 24 (5,true),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 2, 4, 64],[2, 4, 4, 1, 32, 64, 64],64⟩,
.cycle 0 24 true (0),
.cycle 1 25 true (0),
.last 23 (5,true)
]),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 17 5 false (4),
.cycle 27 1 false (3),
.cycle 0 30 true (0),
.split 22 (5,true) (byMove [
.cycle 19 5 false (4),
.cycle 1 36 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (4),
.last 23 (5,false),
.last 27 (5,false),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 1 34 true (0),
.last 24 (5,false),
.last 24 (5,false),
.cycle 0 30 true (0),
.last 26 (5,false),
.last 29 (5,false),
.cycle 23 1 false (1),
.cycle 0 30 true (0),
.last 23 (5,false),
.last 27 (5,false),
.cycle 0 26 true (0),
.last 25 (5,false),
.cycle 1 34 true (0),
.cycle 21 2 true (2),
.last 24 (5,false)
]),
.cycle 1 32 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 1 32 true (0),
.split 22 (5,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 2, 4, 64],[2, 4, 4, 1, 32, 64, 64],64⟩,
.cycle 0 26 true (0),
.cycle 1 36 true (0),
.cycle 1 34 true (0),
.cycle 21 2 true (3),
.last 23 (5,true),
.cycle 1 51 true (0),
.cycle 1 63 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 1 25 true (0),
.last 23 (5,true),
.cycle 1 26 true (0),
.cycle 1 32 true (0),
.cycle 17 9 false (4),
.cycle 5 18 true (0),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.cycle 2 24 true (0),
.cycle 0 24 true (0),
.cycle 1 25 true (0),
.last 23 (5,true)
])
])
theorem kid08_part97_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part97) = true := by rfl

def kid08_part98 : Audit := .cycle 0 51 true (0)
theorem kid08_part98_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part98) = true := by rfl

def kid08_part99 : Audit := .cycle 36 1 false (10)
theorem kid08_part99_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part99) = true := by rfl

def kid08_part100 : Audit := .split 20 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.cycle 32 1 true (6),
.cycle 32 1 true (0),
.split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 33 1 false (1),
.cycle 28 1 false (2),
.last 23 (5,false),
.last 23 (5,false),
.cycle 32 1 true (6),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 28 1 true (4),
.cycle 25 1 true (5),
.last 22 (5,false),
.cycle 0 26 true (0),
.cycle 31 1 true (3),
.cycle 17 5 false (4),
.last 27 (5,false),
.last 23 (5,false),
.last 23 (5,false),
.cycle 32 1 true (6),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 25 1 true (5),
.last 22 (5,false)
]),
.cycle 47 1 true (9),
.cycle 57 1 true (11),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.last 54 (5,false),
.cycle 22 1 true (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 47 1 true (9),
.last 34 (5,false),
.cycle 29 1 true (5),
.cycle 22 1 true (6),
.last 22 (5,false),
.cycle 32 1 true (6),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 24 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 45 (5,false),
.cycle 5 44 true (0),
.cycle 22 1 true (6),
.last 22 (5,false)
]),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.cycle 28 1 true (4),
.cycle 5 16 true (0),
.cycle 21 3 false (3),
.split 21 (5,true) (byMove [
.last 26 (5,false),
.cycle 34 1 false (10),
.last 30 (5,false),
.cycle 26 1 true (4),
.last 23 (5,false),
.last 23 (5,false),
.cycle 6 16 true (0),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.cycle 0 57 true (0),
.last 23 (5,false),
.last 24 (5,false),
.cycle 32 1 true (4),
.cycle 16 6 true (2),
.cycle 17 5 false (4),
.cycle 26 1 true (4),
.last 23 (5,false),
.last 23 (5,false),
.cycle 63 1 true (11),
.cycle 24 1 true (4),
.last 27 (5,false),
.cycle 51 1 true (9),
.cycle 20 2 true (3),
.last 24 (5,false)
]),
.cycle 0 57 true (0),
.cycle 30 1 true (6),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.split 21 (5,true) (byMove [
.last 49 (5,false),
.cycle 31 1 true (5),
.last 24 (5,false),
.cycle 0 23 true (0),
.last 23 (5,false),
.last 25 (5,false),
.cycle 0 22 true (0),
.last 57 (5,false),
.cycle 30 1 true (6),
.cycle 3 19 true (0),
.cycle 22 1 true (6),
.last 22 (5,false),
.last 36 (5,false),
.cycle 24 1 true (4),
.last 24 (5,false),
.cycle 51 1 true (9),
.cycle 20 2 true (4),
.last 25 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 22 1 true (6),
.last 22 (5,false)
])
])
theorem kid08_part100_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part100) = true := by rfl

def kid08_part102 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 43 1 false (9),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 0 30 true (0),
.cycle 0 96 true (0),
.cycle 45 1 false (11),
.cycle 35 1 false (9),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 25 (5,true),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.cycle 21 3 false (4),
.cycle 47 1 false (11),
.cycle 24 1 false (2),
.last 25 (5,true),
.last 29 (5,true),
.cycle 16 48 true (2),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 29 1 false (7),
.last 25 (5,true),
.cycle 39 1 false (9)
])
theorem kid08_part102_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part102) = true := by rfl

def kid08_part103 : Audit := .cycle 32 1 false (10)
theorem kid08_part103_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part103) = true := by rfl

def kid08_part104 : Audit := .cycle 17 3 false (3)
theorem kid08_part104_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part104) = true := by rfl

def kid08_part105 : Audit := .cycle 0 27 true (0)
theorem kid08_part105_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part105) = true := by rfl

def kid08_part106 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 18 4 false (3),
.cycle 0 27 true (0),
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 22 (5,true),
.cycle 18 4 true (2),
.cycle 14 39 true (0),
.cycle 20 3 false (2),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.last 22 (5,true),
.cycle 18 4 false (3),
.cycle 0 27 true (0),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 22 (5,true),
.cycle 19 2 true (2)
])
theorem kid08_part106_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part106) = true := by rfl

def kid08_part107 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 21 1 false (1),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 23 (4,true),
.cycle 21 1 false (3),
.cycle 14 39 true (0),
.last 23 (4,true),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.last 23 (4,true),
.cycle 21 1 false (1),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 23 (4,true),
.cycle 19 2 true (2)
])
theorem kid08_part107_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part107) = true := by rfl

def kid08_part108 : Audit := .cycle 6 14 true (0)
theorem kid08_part108_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part108) = true := by rfl

def kid08_part109 : Audit := .cycle 44 12 true (8)
theorem kid08_part109_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part109) = true := by rfl

def kid08_part110 : Audit := .cycle 23 10 true (4)
theorem kid08_part110_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part110) = true := by rfl

def kid08_part111 : Audit := .cycle 0 51 true (0)
theorem kid08_part111_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part111) = true := by rfl

def kid08_part112 : Audit := .split 20 (4,true) (byMove [
.cycle 0 55 true (0),
.cycle 0 24 true (0),
.cycle 28 2 true (4),
.cycle 27 1 false (3),
.cycle 24 2 true (4),
.last 23 (5,true),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true),
.cycle 24 2 true (4),
.last 29 (5,true),
.cycle 0 57 true (0),
.cycle 26 2 true (4),
.last 22 (5,true),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 0 47 true (0),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true)
])
theorem kid08_part112_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part112) = true := by rfl

def kid08_part113 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 24 true (0),
.cycle 29 1 true (5),
.last 26 (4,true),
.cycle 25 1 true (5),
.cycle 24 1 true (4),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6),
.cycle 25 1 true (5),
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 27 1 true (5),
.last 23 (4,true),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6)
])
theorem kid08_part113_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part113) = true := by rfl

def kid08_part114 : Audit := .cycle 33 1 false (7)
theorem kid08_part114_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part114) = true := by rfl

def kid08_part115 : Audit := .cycle 16 4 true (2)
theorem kid08_part115_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part115) = true := by rfl

def kid08_part116 : Audit := .cycle 17 3 false (3)
theorem kid08_part116_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part116) = true := by rfl

def kid08_part117 : Audit := .cycle 36 1 false (10)
theorem kid08_part117_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part117) = true := by rfl

def kid08_part118 : Audit := .split 20 (4,true) (byMove [
.cycle 0 75 true (0),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.last 23 (5,true),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 22 4 true (4),
.last 21 (5,true),
.cycle 15 12 true (1),
.cycle 20 3 false (2),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 22 (5,true),
.last 23 (5,true),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 0 63 true (0),
.cycle 5 16 true (0),
.cycle 22 4 true (4),
.last 21 (5,true)
])
theorem kid08_part118_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part118) = true := by rfl

def kid08_part119 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 21 1 false (1),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 24 1 false (6),
.cycle 15 12 true (1),
.last 23 (4,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 23 (4,true),
.cycle 21 1 false (1),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 22 (4,true),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 22 3 true (4)
])
theorem kid08_part119_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part119) = true := by rfl

def kid08_part120 : Audit := .cycle 0 59 true (0)
theorem kid08_part120_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part120) = true := by rfl

def kid08_part121 : Audit := .cycle 1 23 true (0)
theorem kid08_part121_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part121) = true := by rfl

def kid08_part122 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 2 32 true (0),
.cycle 0 28 true (0),
.cycle 2 32 true (0),
.last 22 (5,true),
.cycle 2 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 2, 64, 64],64⟩,
.cycle 0 24 true (0),
.cycle 2 28 true (0),
.last 23 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 32, 64, 64],64⟩,
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 17 5 false (4),
.cycle 27 1 false (3),
.last 24 (5,true),
.last 22 (5,true),
.cycle 2 32 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (5,true),
.cycle 2 24 true (0)
])
theorem kid08_part122_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part122) = true := by rfl

def kid08_part123 : Audit := .cycle 20 30 true (3)
theorem kid08_part123_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part123) = true := by rfl

def kid08_part124 : Audit := .split 20 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.cycle 32 2 true (6),
.cycle 32 2 true (0),
.last 21 (5,true),
.cycle 47 2 true (9),
.cycle 57 2 true (11),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true),
.cycle 24 2 true (4),
.cycle 28 2 true (4),
.cycle 28 2 true (4),
.cycle 5 16 true (0),
.last 24 (5,true),
.last 21 (5,true),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 22 2 true (6),
.last 21 (5,true)
])
theorem kid08_part124_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part124) = true := by rfl

def kid08_part125 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 24 true (0),
.last 22 (4,true),
.cycle 33 1 true (7),
.last 21 (4,true),
.cycle 32 1 true (0),
.cycle 48 1 true (10),
.cycle 58 1 true (12),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6),
.cycle 25 1 true (5),
.cycle 29 1 true (5),
.last 22 (4,true),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 21 3 false (3),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 1 true (6)
])
theorem kid08_part125_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part125) = true := by rfl

def kid08_part101 : Audit := .split 19 (5,false) (byMove [(kid08_part102),(kid08_part103),(kid08_part104),(kid08_part105),(kid08_part106),(kid08_part107),(kid08_part108),(kid08_part109),(kid08_part110),(kid08_part111),(kid08_part112),(kid08_part113),(kid08_part114),(kid08_part115),(kid08_part116),(kid08_part117),(kid08_part118),(kid08_part119),(kid08_part120),(kid08_part121),(kid08_part122),(kid08_part123),(kid08_part124),(kid08_part125)])

theorem kid08_part101_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part101) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid08_part102),(kid08_part103),(kid08_part104),(kid08_part105),(kid08_part106),(kid08_part107),(kid08_part108),(kid08_part109),(kid08_part110),(kid08_part111),(kid08_part112),(kid08_part113),(kid08_part114),(kid08_part115),(kid08_part116),(kid08_part117),(kid08_part118),(kid08_part119),(kid08_part120),(kid08_part121),(kid08_part122),(kid08_part123),(kid08_part124),(kid08_part125)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part102_checked

  · exact kid08_part108_checked

  · exact kid08_part114_checked

  · exact kid08_part120_checked

  · exact kid08_part103_checked

  · exact kid08_part109_checked

  · exact kid08_part115_checked

  · exact kid08_part121_checked

  · exact kid08_part104_checked

  · exact kid08_part110_checked

  · exact kid08_part116_checked

  · exact kid08_part122_checked

  · exact kid08_part105_checked

  · exact kid08_part111_checked

  · exact kid08_part117_checked

  · exact kid08_part123_checked

  · exact kid08_part106_checked

  · exact kid08_part112_checked

  · exact kid08_part118_checked

  · exact kid08_part124_checked

  · exact kid08_part107_checked

  · exact kid08_part113_checked

  · exact kid08_part119_checked

  · exact kid08_part125_checked

def kid08_part5 : Audit := .split 18 (4,false) (byMove [(kid08_part6),(kid08_part7),(kid08_part8),(kid08_part9),(kid08_part10),(kid08_part11),(kid08_part36),(kid08_part37),(kid08_part38),(kid08_part39),(kid08_part40),(kid08_part41),(kid08_part66),(kid08_part67),(kid08_part68),(kid08_part69),(kid08_part70),(kid08_part71),(kid08_part96),(kid08_part97),(kid08_part98),(kid08_part99),(kid08_part100),(kid08_part101)])

theorem kid08_part5_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (kid08_part5) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) 18 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part6),(kid08_part7),(kid08_part8),(kid08_part9),(kid08_part10),(kid08_part11),(kid08_part36),(kid08_part37),(kid08_part38),(kid08_part39),(kid08_part40),(kid08_part41),(kid08_part66),(kid08_part67),(kid08_part68),(kid08_part69),(kid08_part70),(kid08_part71),(kid08_part96),(kid08_part97),(kid08_part98),(kid08_part99),(kid08_part100),(kid08_part101)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part6_checked

  · exact kid08_part36_checked

  · exact kid08_part66_checked

  · exact kid08_part96_checked

  · exact kid08_part7_checked

  · exact kid08_part37_checked

  · exact kid08_part67_checked

  · exact kid08_part97_checked

  · exact kid08_part8_checked

  · exact kid08_part38_checked

  · exact kid08_part68_checked

  · exact kid08_part98_checked

  · exact kid08_part9_checked

  · exact kid08_part39_checked

  · exact kid08_part69_checked

  · exact kid08_part99_checked

  · exact kid08_part10_checked

  · exact kid08_part40_checked

  · exact kid08_part70_checked

  · exact kid08_part100_checked

  · exact kid08_part11_checked

  · exact kid08_part41_checked

  · exact kid08_part71_checked

  · exact kid08_part101_checked

def kid08_part127 : Audit := .cycle 0 57 true (0)
theorem kid08_part127_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part127) = true := by rfl

def kid08_part128 : Audit := .cycle 45 1 false (7)
theorem kid08_part128_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part128) = true := by rfl

def kid08_part129 : Audit := .cycle 20 1 false (2)
theorem kid08_part129_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part129) = true := by rfl

def kid08_part130 : Audit := .cycle 19 1 false (1)
theorem kid08_part130_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part130) = true := by rfl

def kid08_part132 : Audit := .cycle 0 42 true (0)
theorem kid08_part132_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part132) = true := by rfl

def kid08_part133 : Audit := .cycle 38 1 false (10)
theorem kid08_part133_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part133) = true := by rfl

def kid08_part134 : Audit := .cycle 21 1 false (1)
theorem kid08_part134_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part134) = true := by rfl

def kid08_part135 : Audit := .cycle 20 1 false (0)
theorem kid08_part135_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part135) = true := by rfl

def kid08_part136 : Audit := .cycle 19 1 false (1)
theorem kid08_part136_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part136) = true := by rfl

def kid08_part137 : Audit := .cycle 18 2 false (2)
theorem kid08_part137_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part137) = true := by rfl

def kid08_part138 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 38 true (0),
.cycle 0 30 true (0),
.last 24 (4,true),
.cycle 0 38 true (0),
.cycle 0 36 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 1, 128, 128, 256, 32768, 2, 4096, 262144, 128, 256, 8, 4, 1, 128, 262144],[2, 4, 256, 1, 262144, 2, 8192, 16384, 256, 4096, 262144, 8192, 2, 4, 262144, 1, 262144, 2, 262144],264192⟩,
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.cycle 0 63 true (0),
.cycle 0 38 true (0),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 17 7 false (4),
.cycle 29 1 false (3),
.last 24 (4,true),
.last 31 (4,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.cycle 0 57 true (0),
.last 25 (4,true)
])
theorem kid08_part138_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part138) = true := by rfl

def kid08_part139 : Audit := .cycle 0 57 true (0)
theorem kid08_part139_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part139) = true := by rfl

def kid08_part140 : Audit := .cycle 21 1 false (3)
theorem kid08_part140_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part140) = true := by rfl

def kid08_part141 : Audit := .cycle 20 1 false (2)
theorem kid08_part141_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part141) = true := by rfl

def kid08_part142 : Audit := .split 22 (4,true) (byMove [
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 26 1 true (4),
.cycle 29 1 true (3),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 25 1 true (3),
.cycle 0 24 true (0),
.cycle 24 1 true (6),
.last 23 (5,true),
.cycle 39 1 true (3),
.last 25 (5,true),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.cycle 21 2 true (3),
.cycle 20 4 true (2),
.cycle 0 63 true (0),
.cycle 33 1 true (5),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 24 1 true (6),
.last 23 (5,true)
])
theorem kid08_part142_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part142) = true := by rfl

def kid08_part143 : Audit := .cycle 18 2 true (1)
theorem kid08_part143_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part143) = true := by rfl

def kid08_part144 : Audit := .cycle 11 12 true (0)
theorem kid08_part144_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part144) = true := by rfl

def kid08_part145 : Audit := .split 22 (5,true) (byMove [
.cycle 0 98 true (-2),
.cycle 31 1 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 19 4 true (0),
.cycle 18 5 false (2),
.cycle 11 15 false (3),
.cycle 20 3 false (1),
.last 260 (4,true),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 0 69 true (0),
.cycle 1 48 true (0),
.cycle 40 1 false (10),
.cycle 0 75 true (0),
.cycle 16 8 false (3),
.last 24 (4,true)
])
theorem kid08_part145_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part145) = true := by rfl

def kid08_part146 : Audit := .split 25 (5,true) (byMove [
.cycle 0 30 true (0),
.cycle 28 1 false (4),
.cycle 0 44 true (-1),
.cycle 0 32 true (0),
.last 26 (4,true),
.cycle 0 44 true (-1),
.cycle 0 40 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 1, 128, 128, 256, 32768, 524290, 16777472, 16777216, 128, 256, 2097152, 4, 262144, 16809984, 128, 256, 8, 256, 1, 128, 16777216],[2, 4, 256, 1, 16777216, 2, 8192, 16384, 256, 4096, 16777216, 8192, 524288, 1048576, 16777216, 262144, 16777216, 524288, 2, 4, 16777220, 1, 16777216, 2, 16777216],16911360⟩,
.cycle 0 28 true (0),
.cycle 0 36 true (0),
.cycle 0 75 true (0),
.cycle 17 11 false (4),
.cycle 0 30 true (0),
.cycle 0 36 true (0),
.cycle 17 9 false (4),
.cycle 31 1 false (3),
.last 26 (4,true),
.last 35 (4,true),
.cycle 0 40 true (0),
.cycle 1 28 true (0),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.cycle 17 13 false (4),
.last 27 (4,true)
])
theorem kid08_part146_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part146) = true := by rfl

def kid08_part147 : Audit := .cycle 20 1 false (0)
theorem kid08_part147_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part147) = true := by rfl

def kid08_part148 : Audit := .cycle 19 1 false (1)
theorem kid08_part148_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part148) = true := by rfl

def kid08_part149 : Audit := .cycle 18 2 false (2)
theorem kid08_part149_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part149) = true := by rfl

def kid08_part150 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 50 true (0),
.cycle 27 1 false (1),
.cycle 0 30 true (0),
.last 24 (4,true),
.cycle 0 38 true (-1),
.cycle 0 36 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 64, 128, 128, 256, 32768, 2, 64, 262144, 128, 256, 8, 4, 64, 128, 262144],[2, 4, 256, 1, 262144, 2, 8192, 16384, 256, 4096, 262144, 8192, 2, 4, 262144, 1, 262144, 2, 262144],264192⟩,
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.cycle 0 69 true (0),
.cycle 0 38 true (0),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 0 32 true (0),
.cycle 0 37 true (0),
.last 24 (4,true),
.last 32 (4,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.cycle 0 69 true (0),
.last 25 (4,true)
])
theorem kid08_part150_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part150) = true := by rfl

def kid08_part151 : Audit := .cycle 0 57 true (0)
theorem kid08_part151_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part151) = true := by rfl

def kid08_part152 : Audit := .cycle 45 1 false (7)
theorem kid08_part152_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part152) = true := by rfl

def kid08_part153 : Audit := .split 25 (5,true) (byMove [
.cycle 0 30 true (0),
.cycle 47 1 false (9),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 45 1 false (9),
.cycle 0 34 true (0),
.cycle 49 1 false (11),
.cycle 37 1 false (9),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 28 true (0),
.cycle 33 1 false (7),
.cycle 0 30 true (0),
.cycle 23 3 false (4),
.cycle 51 1 false (11),
.cycle 26 1 false (2),
.last 78 (4,true),
.cycle 0 34 true (0),
.last 73 (4,true),
.cycle 1 28 true (0),
.cycle 0 28 true (0),
.cycle 31 1 false (7),
.cycle 0 28 true (0),
.last 27 (4,true)
])
theorem kid08_part153_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part153) = true := by rfl

def kid08_part154 : Audit := .split 22 (4,true) (byMove [
.last 26 (5,true),
.cycle 0 26 true (0),
.last 24 (5,true),
.cycle 35 1 true (5),
.cycle 37 1 true (-1),
.last 23 (5,true),
.cycle 52 1 true (8),
.cycle 64 1 true (10),
.cycle 35 1 true (3),
.cycle 0 24 true (0),
.cycle 24 1 true (6),
.last 23 (5,true),
.cycle 27 1 true (3),
.cycle 47 1 true (-1),
.last 24 (5,true),
.cycle 5 18 true (0),
.cycle 24 3 false (2),
.last 23 (5,true),
.cycle 0 63 true (0),
.cycle 33 1 true (5),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 24 1 true (6),
.last 23 (5,true)
])
theorem kid08_part154_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part154) = true := by rfl

def kid08_part155 : Audit := .split 21 (4,true) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 19 3 false (2),
.cycle 18 4 false (2),
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 26 (5,true),
.cycle 18 4 true (1),
.cycle 11 14 true (0),
.last 24 (5,true),
.last 27 (5,true),
.cycle 22 1 false (0),
.last 23 (5,true),
.cycle 18 4 false (2),
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.last 27 (5,true),
.last 26 (5,true),
.cycle 20 2 true (1)
])
theorem kid08_part155_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part155) = true := by rfl

def kid08_part131 : Audit := .split 19 (4,false) (byMove [(kid08_part132),(kid08_part133),(kid08_part134),(kid08_part135),(kid08_part136),(kid08_part137),(kid08_part138),(kid08_part139),(kid08_part140),(kid08_part141),(kid08_part142),(kid08_part143),(kid08_part144),(kid08_part145),(kid08_part146),(kid08_part147),(kid08_part148),(kid08_part149),(kid08_part150),(kid08_part151),(kid08_part152),(kid08_part153),(kid08_part154),(kid08_part155)])

theorem kid08_part131_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part131) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part132),(kid08_part133),(kid08_part134),(kid08_part135),(kid08_part136),(kid08_part137),(kid08_part138),(kid08_part139),(kid08_part140),(kid08_part141),(kid08_part142),(kid08_part143),(kid08_part144),(kid08_part145),(kid08_part146),(kid08_part147),(kid08_part148),(kid08_part149),(kid08_part150),(kid08_part151),(kid08_part152),(kid08_part153),(kid08_part154),(kid08_part155)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part132_checked

  · exact kid08_part138_checked

  · exact kid08_part144_checked

  · exact kid08_part150_checked

  · exact kid08_part133_checked

  · exact kid08_part139_checked

  · exact kid08_part145_checked

  · exact kid08_part151_checked

  · exact kid08_part134_checked

  · exact kid08_part140_checked

  · exact kid08_part146_checked

  · exact kid08_part152_checked

  · exact kid08_part135_checked

  · exact kid08_part141_checked

  · exact kid08_part147_checked

  · exact kid08_part153_checked

  · exact kid08_part136_checked

  · exact kid08_part142_checked

  · exact kid08_part148_checked

  · exact kid08_part154_checked

  · exact kid08_part137_checked

  · exact kid08_part143_checked

  · exact kid08_part149_checked

  · exact kid08_part155_checked

def kid08_part156 : Audit := .cycle 18 1 false (2)
theorem kid08_part156_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part156) = true := by rfl

def kid08_part157 : Audit := .cycle 0 23 true (0)
theorem kid08_part157_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part157) = true := by rfl

def kid08_part158 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.cycle 0 86 true (0),
.cycle 0 32 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 41 1 false (9),
.last 27 (4,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.last 25 (4,true),
.cycle 37 1 false (9),
.cycle 57 1 false (9),
.cycle 19 4 false (4),
.last 29 (4,true),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 26 1 false (4),
.last 27 (4,true),
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 41 1 false (9),
.last 25 (4,true),
.cycle 18 34 true (2)
]),
.cycle 0 26 true (0),
.cycle 41 1 false (11),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.split 22 (4,false) (byMove [
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 22 1 false (4),
.cycle 37 1 false (9),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 34 1 false (12),
.cycle 16 88 true (2),
.cycle 19 4 true (3),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.cycle 22 1 false (4),
.cycle 35 1 false (9),
.cycle 0 63 true (0),
.cycle 41 1 false (11),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 50 (4,true)
]),
.cycle 25 1 false (7),
.cycle 0 26 true (0),
.cycle 19 3 false (4),
.cycle 43 1 false (11),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.last 27 (4,true),
.cycle 0 89 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 18 5 false (4),
.cycle 37 1 false (9),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 43 1 false (11),
.last 23 (4,true),
.cycle 21 2 true (2),
.cycle 0 30 true (0),
.cycle 19 4 false (4),
.cycle 41 1 false (9),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 0 30 true (0),
.cycle 19 34 true (2),
.cycle 0 26 true (0),
.cycle 20 3 false (4),
.cycle 63 28 true (7),
.last 23 (4,true),
.last 24 (4,true)
]),
.cycle 0 26 true (0),
.cycle 16 42 true (2),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.split 22 (4,false) (byMove [
.cycle 37 1 false (9),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 43 1 false (11),
.last 23 (4,true),
.cycle 21 2 true (3),
.cycle 0 85 true (0),
.cycle 31 57 true (5),
.cycle 17 78 true (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 51 (4,true),
.cycle 35 1 false (9),
.cycle 41 1 false (9),
.cycle 17 6 true (2),
.cycle 27 1 false (7),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 63 true (0),
.cycle 16 42 true (2),
.cycle 2 24 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 50 (4,true)
]),
.cycle 31 57 true (5)
])
theorem kid08_part158_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part158) = true := by rfl

def kid08_part159 : Audit := .cycle 30 1 false (10)
theorem kid08_part159_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part159) = true := by rfl

def kid08_part160 : Audit := .cycle 19 1 false (3)
theorem kid08_part160_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part160) = true := by rfl

def kid08_part162 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 38 true (0),
.cycle 0 30 true (0),
.last 24 (4,true),
.cycle 0 38 true (0),
.cycle 0 36 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 16, 64],[2, 4, 4, 1, 64, 2, 64],64⟩,
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.cycle 0 30 true (0),
.last 25 (4,true),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 17 7 false (4),
.cycle 29 1 false (3),
.last 24 (4,true),
.last 26 (4,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 16, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.last 25 (4,true)
])
theorem kid08_part162_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part162) = true := by rfl

def kid08_part163 : Audit := .cycle 0 57 true (0)
theorem kid08_part163_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part163) = true := by rfl

def kid08_part164 : Audit := .cycle 21 1 false (3)
theorem kid08_part164_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part164) = true := by rfl

def kid08_part165 : Audit := .cycle 20 1 false (2)
theorem kid08_part165_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part165) = true := by rfl

def kid08_part166 : Audit := .cycle 19 1 false (3)
theorem kid08_part166_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part166) = true := by rfl

def kid08_part167 : Audit := .cycle 18 2 true (2)
theorem kid08_part167_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part167) = true := by rfl

def kid08_part168 : Audit := .cycle 23 1 false (7)
theorem kid08_part168_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part168) = true := by rfl

def kid08_part169 : Audit := .cycle 32 1 false (10)
theorem kid08_part169_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part169) = true := by rfl

def kid08_part170 : Audit := .cycle 27 1 false (7)
theorem kid08_part170_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part170) = true := by rfl

def kid08_part171 : Audit := .cycle 30 1 false (10)
theorem kid08_part171_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part171) = true := by rfl

def kid08_part172 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.cycle 25 1 true (5),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true),
.cycle 25 1 true (5),
.last 23 (5,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.cycle 20 2 true (3),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true)
])
theorem kid08_part172_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part172) = true := by rfl

def kid08_part173 : Audit := .split 20 (5,true) (byMove [
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 23 (4,true),
.cycle 24 2 true (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6),
.cycle 24 2 true (4),
.cycle 20 3 false (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.last 22 (4,true),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6)
])
theorem kid08_part173_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part173) = true := by rfl

def kid08_part174 : Audit := .cycle 26 12 true (4)
theorem kid08_part174_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part174) = true := by rfl

def kid08_part175 : Audit := .split 22 (5,true) (byMove [
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 19 4 false (3),
.cycle 18 5 false (3),
.cycle 0 31 true (0),
.cycle 37 1 false (9),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.cycle 19 4 true (2),
.last 24 (4,true),
.cycle 14 43 true (0),
.cycle 20 3 false (3),
.cycle 0 58 true (0),
.cycle 23 1 false (1),
.cycle 19 4 false (3),
.last 24 (4,true),
.cycle 0 31 true (0),
.cycle 1 28 true (0),
.cycle 0 63 true (0),
.cycle 44 1 false (10),
.cycle 16 8 true (2),
.last 24 (4,true)
])
theorem kid08_part175_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part175) = true := by rfl

def kid08_part176 : Audit := .cycle 25 1 false (7)
theorem kid08_part176_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part176) = true := by rfl

def kid08_part177 : Audit := .cycle 20 1 false (2)
theorem kid08_part177_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part177) = true := by rfl

def kid08_part178 : Audit := .cycle 19 1 false (3)
theorem kid08_part178_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part178) = true := by rfl

def kid08_part179 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 19 3 false (3),
.cycle 18 4 true (2),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.cycle 23 3 true (5),
.last 22 (5,true),
.cycle 30 14 true (4),
.last 24 (5,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 19 3 false (3),
.cycle 20 2 true (2),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.last 23 (5,true),
.cycle 5 87 true (0),
.last 25 (5,true),
.last 22 (5,true)
])
theorem kid08_part179_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part179) = true := by rfl

def kid08_part180 : Audit := .cycle 0 59 true (0)
theorem kid08_part180_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part180) = true := by rfl

def kid08_part181 : Audit := .cycle 1 23 true (0)
theorem kid08_part181_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part181) = true := by rfl

def kid08_part182 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 39 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 39 1 false (9),
.cycle 0 26 true (0),
.cycle 41 1 false (11),
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 33 1 false (9),
.last 23 (4,true),
.cycle 0 26 true (0),
.cycle 20 3 false (4),
.cycle 43 1 false (11),
.cycle 22 1 false (2),
.cycle 19 3 false (4),
.last 23 (4,true),
.cycle 16 42 true (2),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.cycle 2 24 true (0),
.last 23 (4,true)
])
theorem kid08_part182_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part182) = true := by rfl

def kid08_part183 : Audit := .cycle 5 77 true (0)
theorem kid08_part183_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part183) = true := by rfl

def kid08_part184 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 24 true (0),
.last 27 (5,true),
.cycle 33 1 true (7),
.cycle 29 1 true (1),
.last 21 (5,true),
.cycle 48 1 true (10),
.cycle 58 1 true (12),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true),
.cycle 25 1 true (5),
.cycle 29 1 true (5),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 3 false (4),
.last 21 (5,true),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true)
])
theorem kid08_part184_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part184) = true := by rfl

def kid08_part185 : Audit := .split 20 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.last 25 (4,true),
.cycle 32 2 true (6),
.last 21 (4,true),
.last 25 (4,true),
.cycle 47 2 true (9),
.cycle 57 2 true (11),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6),
.cycle 24 2 true (4),
.cycle 28 2 true (4),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6)
])
theorem kid08_part185_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part185) = true := by rfl

def kid08_part161 : Audit := .split 19 (4,false) (byMove [(kid08_part162),(kid08_part163),(kid08_part164),(kid08_part165),(kid08_part166),(kid08_part167),(kid08_part168),(kid08_part169),(kid08_part170),(kid08_part171),(kid08_part172),(kid08_part173),(kid08_part174),(kid08_part175),(kid08_part176),(kid08_part177),(kid08_part178),(kid08_part179),(kid08_part180),(kid08_part181),(kid08_part182),(kid08_part183),(kid08_part184),(kid08_part185)])

theorem kid08_part161_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part161) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid08_part162),(kid08_part163),(kid08_part164),(kid08_part165),(kid08_part166),(kid08_part167),(kid08_part168),(kid08_part169),(kid08_part170),(kid08_part171),(kid08_part172),(kid08_part173),(kid08_part174),(kid08_part175),(kid08_part176),(kid08_part177),(kid08_part178),(kid08_part179),(kid08_part180),(kid08_part181),(kid08_part182),(kid08_part183),(kid08_part184),(kid08_part185)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part162_checked

  · exact kid08_part168_checked

  · exact kid08_part174_checked

  · exact kid08_part180_checked

  · exact kid08_part163_checked

  · exact kid08_part169_checked

  · exact kid08_part175_checked

  · exact kid08_part181_checked

  · exact kid08_part164_checked

  · exact kid08_part170_checked

  · exact kid08_part176_checked

  · exact kid08_part182_checked

  · exact kid08_part165_checked

  · exact kid08_part171_checked

  · exact kid08_part177_checked

  · exact kid08_part183_checked

  · exact kid08_part166_checked

  · exact kid08_part172_checked

  · exact kid08_part178_checked

  · exact kid08_part184_checked

  · exact kid08_part167_checked

  · exact kid08_part173_checked

  · exact kid08_part179_checked

  · exact kid08_part185_checked

def kid08_part186 : Audit := .split 20 (5,true) (byMove [
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.split 21 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 30 1 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 27 1 true (3),
.cycle 32 1 true (6),
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (4,true),
.cycle 25 1 true (5),
.cycle 0 26 true (0),
.cycle 20 4 false (4),
.cycle 34 1 true (6),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 19 3 false (4),
.cycle 32 1 true (6),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (4,true),
.cycle 25 1 true (5)
]),
.cycle 24 1 true (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.last 22 (4,false),
.cycle 22 1 true (6),
.cycle 32 1 true (6),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 22 (4,false),
.last 24 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.last 22 (4,false),
.cycle 22 1 true (6)
]),
.cycle 22 1 true (6),
.cycle 24 1 true (4),
.cycle 20 3 false (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.split 21 (4,false) (byMove [
.last 26 (4,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 18 4 true (2),
.cycle 25 1 false (7),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.cycle 32 1 false (10),
.last 22 (4,true),
.cycle 20 2 true (3),
.cycle 32 1 true (4),
.cycle 20 4 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 19 3 false (4),
.cycle 63 1 true (11),
.cycle 24 1 true (4),
.cycle 20 3 false (4),
.cycle 51 1 true (9),
.last 22 (4,true),
.last 23 (4,true)
]),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 30 1 true (6),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 true (3),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 57 (4,false),
.cycle 30 1 true (6),
.cycle 28 1 false (8),
.last 22 (4,false),
.cycle 22 1 true (6),
.cycle 25 1 false (7),
.cycle 24 1 true (4),
.last 26 (4,false),
.cycle 32 1 false (10),
.last 23 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 22 1 true (6)
]),
.cycle 22 1 true (6)
])
theorem kid08_part186_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part186) = true := by rfl

def kid08_part187 : Audit := .cycle 14 35 true (0)
theorem kid08_part187_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part187) = true := by rfl

def kid08_part188 : Audit := .split 21 (5,true) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.split 22 (4,false) (byMove [
.cycle 0 98 true (-2),
.cycle 31 1 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 26 (4,true),
.cycle 18 5 false (2),
.cycle 11 15 false (3),
.cycle 19 4 false (2),
.last 155 (4,true),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 0 69 true (0),
.cycle 1 48 true (0),
.cycle 40 1 false (10),
.cycle 0 75 true (0),
.last 26 (4,true),
.cycle 16 8 false (3)
]),
.cycle 18 4 false (2),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 18 5 false (2),
.cycle 0 34 true (0),
.cycle 29 1 false (7),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.last 24 (4,true),
.last 29 (4,true),
.cycle 14 43 true (0),
.cycle 19 4 true (1),
.cycle 0 38 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 18 5 false (2),
.cycle 0 37 true (0),
.cycle 1 40 true (0),
.cycle 0 63 true (0),
.cycle 44 1 false (10),
.last 24 (4,true),
.cycle 16 8 true (1)
]),
.cycle 18 4 true (1),
.cycle 11 14 true (0),
.cycle 19 3 false (2),
.cycle 17 11 false (4),
.cycle 22 1 false (0),
.split 22 (4,false) (byMove [
.last 27 (4,true),
.last 30 (4,true),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 0 69 true (0),
.cycle 25 1 false (3),
.cycle 17 6 false (3),
.last 28 (4,true),
.last 23 (4,true),
.cycle 21 2 true (0),
.cycle 16 11 false (3),
.cycle 19 4 false (2),
.cycle 0 75 true (-1),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 0 69 true (0),
.cycle 11 14 true (0),
.cycle 20 3 false (2),
.last 28 (4,true),
.last 23 (4,true),
.last 24 (4,true)
]),
.cycle 18 4 false (2),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 33 1 false (7),
.split 22 (4,false) (byMove [
.cycle 0 69 true (0),
.cycle 25 1 false (3),
.cycle 17 6 false (3),
.cycle 0 46 true (0),
.last 23 (4,true),
.cycle 21 2 true (1),
.cycle 0 34 true (0),
.cycle 42 34 true (6),
.cycle 14 39 true (0),
.cycle 51 1 false (7),
.last 24 (4,true),
.last 29 (4,true),
.cycle 36 1 false (10),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 33 1 false (7),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 40 true (0),
.cycle 1 40 true (0),
.cycle 0 63 true (0),
.cycle 13 47 true (0),
.last 24 (4,true),
.cycle 16 11 false (3)
]),
.cycle 16 7 false (3)
])
theorem kid08_part188_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part188) = true := by rfl

def kid08_part189 : Audit := .cycle 0 42 true (0)
theorem kid08_part189_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part189) = true := by rfl

def kid08_part190 : Audit := .cycle 19 1 false (1)
theorem kid08_part190_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part190) = true := by rfl

def kid08_part192 : Audit := .split 23 (5,true) (byMove [
.cycle 63 1 false (7),
.cycle 26 1 false (2),
.cycle 17 7 false (3),
.cycle 0 75 true (0),
.last 24 (4,true),
.cycle 18 7 false (2),
.cycle 0 44 true (0),
.cycle 0 69 true (0),
.cycle 11 14 true (0),
.cycle 40 1 false (10),
.cycle 0 75 true (0),
.cycle 18 12 true (0),
.cycle 27 1 false (3),
.cycle 16 8 false (3),
.cycle 17 7 false (3),
.cycle 0 75 true (0),
.last 24 (4,true),
.cycle 18 7 false (2),
.cycle 0 44 true (0),
.cycle 0 69 true (0),
.cycle 2 48 true (0),
.cycle 30 115 true (0),
.cycle 0 75 true (0),
.last 25 (4,true)
])
theorem kid08_part192_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part192) = true := by rfl

def kid08_part193 : Audit := .split 27 (4,true) (byMove [
.last 31 (5,true),
.cycle 0 31 true (0),
.cycle 0 56 true (0),
.cycle 0 35 true (0),
.cycle 0 42 true (0),
.cycle 0 48 true (0),
.last 63 (5,true),
.cycle 0 53 true (0),
.cycle 0 34 true (0),
.cycle 0 29 true (0),
.cycle 0 93 true (0),
.last 28 (5,true),
.cycle 0 46 true (-1),
.last 30 (5,true),
.last 67 (5,true),
.cycle 0 54 true (0),
.last 70 (5,true),
.cycle 36 1 false (6),
.last 60 (5,true),
.cycle 0 42 true (0),
.last 29 (5,true),
.cycle 0 29 true (0),
.cycle 0 44 true (0),
.last 28 (5,true)
])
theorem kid08_part193_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part193) = true := by rfl

def kid08_part194 : Audit := .cycle 21 1 false (1)
theorem kid08_part194_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part194) = true := by rfl

def kid08_part195 : Audit := .cycle 20 1 false (0)
theorem kid08_part195_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part195) = true := by rfl

def kid08_part196 : Audit := .cycle 19 1 false (1)
theorem kid08_part196_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part196) = true := by rfl

def kid08_part197 : Audit := .cycle 18 2 false (2)
theorem kid08_part197_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part197) = true := by rfl

def kid08_part198 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 43 1 false (9),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.last 29 (4,true),
.cycle 0 30 true (0),
.cycle 45 1 false (11),
.cycle 35 1 false (9),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 34 1 false (10),
.cycle 29 1 false (7),
.cycle 0 28 true (0),
.cycle 21 3 false (4),
.cycle 47 1 false (11),
.cycle 24 1 false (2),
.cycle 39 1 false (9),
.cycle 0 30 true (0),
.last 67 (4,true),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 29 1 false (7),
.cycle 0 95 true (0),
.last 25 (4,true)
])
theorem kid08_part198_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part198) = true := by rfl

def kid08_part199 : Audit := .cycle 32 1 false (10)
theorem kid08_part199_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part199) = true := by rfl

def kid08_part200 : Audit := .cycle 17 3 false (3)
theorem kid08_part200_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part200) = true := by rfl

def kid08_part201 : Audit := .split 25 (4,true) (byMove [
.last 29 (5,true),
.cycle 0 29 true (0),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 27 1 false (3),
.cycle 0 42 true (0),
.cycle 35 1 false (9),
.cycle 28 1 false (6),
.cycle 0 30 true (0),
.cycle 0 27 true (0),
.cycle 28 1 false (6),
.last 26 (5,true),
.cycle 21 5 false (5),
.last 28 (5,true),
.cycle 37 1 false (9),
.cycle 26 1 false (2),
.cycle 37 1 false (9),
.cycle 32 1 false (6),
.last 56 (5,true),
.cycle 0 38 true (0),
.last 27 (5,true),
.cycle 0 27 true (0),
.cycle 3 25 true (0),
.last 26 (5,true)
])
theorem kid08_part201_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part201) = true := by rfl

def kid08_part202 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 28 1 true (4),
.cycle 18 3 false (2),
.cycle 35 1 false (9),
.last 23 (5,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 24 1 true (6),
.last 24 (5,true),
.cycle 14 39 true (0),
.last 23 (5,true),
.cycle 39 1 false (9),
.cycle 21 1 false (1),
.cycle 19 2 true (1),
.cycle 18 3 false (2),
.last 56 (5,true),
.last 23 (5,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 24 1 true (6),
.last 23 (5,true)
])
theorem kid08_part202_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part202) = true := by rfl

def kid08_part203 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 4 true (1),
.cycle 18 3 false (2),
.last 25 (4,true),
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 23 (4,true),
.cycle 25 3 true (5),
.cycle 14 39 true (0),
.cycle 20 3 false (2),
.last 27 (4,true),
.cycle 21 1 false (1),
.cycle 19 2 true (1),
.cycle 18 3 false (2),
.last 25 (4,true),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 23 (4,true),
.last 22 (4,true)
])
theorem kid08_part203_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part203) = true := by rfl

def kid08_part204 : Audit := .split 24 (4,true) (byMove [
.last 28 (5,true),
.last 31 (5,true),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.last 33 (5,true),
.cycle 18 7 false (2),
.cycle 0 75 true (0),
.cycle 27 1 false (3),
.cycle 17 8 false (3),
.last 29 (5,true),
.cycle 14 51 true (0),
.last 25 (5,true),
.cycle 20 5 false (2),
.last 27 (5,true),
.cycle 0 81 true (-1),
.cycle 25 1 false (-1),
.cycle 19 6 false (2),
.cycle 18 7 false (2),
.cycle 0 75 true (0),
.cycle 11 16 true (0),
.last 26 (5,true),
.last 29 (5,true),
.cycle 0 127 true (0),
.last 25 (5,true)
])
theorem kid08_part204_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part204) = true := by rfl

def kid08_part205 : Audit := .split 22 (5,true) (byMove [
.last 31 (4,true),
.cycle 12 13 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 14 43 true (0),
.cycle 0 75 true (0),
.last 29 (4,true),
.cycle 23 1 false (1),
.cycle 19 4 true (0),
.cycle 18 5 false (2),
.last 31 (4,true),
.cycle 20 3 false (1),
.cycle 14 47 true (-1),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 14 43 true (0),
.cycle 0 75 true (0),
.last 29 (4,true),
.cycle 38 1 false (10),
.cycle 16 8 false (3),
.last 24 (4,true)
])
theorem kid08_part205_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part205) = true := by rfl

def kid08_part206 : Audit := .split 25 (5,true) (byMove [
.cycle 0 30 true (0),
.cycle 47 1 false (9),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.last 33 (4,true),
.cycle 0 34 true (0),
.cycle 49 1 false (11),
.cycle 37 1 false (9),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 38 1 false (10),
.cycle 33 1 false (7),
.cycle 0 30 true (0),
.cycle 23 3 false (4),
.cycle 51 1 false (11),
.cycle 26 1 false (2),
.cycle 45 1 false (9),
.cycle 0 34 true (0),
.last 73 (4,true),
.cycle 1 28 true (0),
.cycle 0 28 true (0),
.cycle 31 1 false (7),
.cycle 17 10 true (0),
.last 27 (4,true)
])
theorem kid08_part206_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part206) = true := by rfl

def kid08_part207 : Audit := .cycle 20 1 false (0)
theorem kid08_part207_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part207) = true := by rfl

def kid08_part208 : Audit := .cycle 19 1 false (1)
theorem kid08_part208_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part208) = true := by rfl

def kid08_part209 : Audit := .cycle 18 2 false (2)
theorem kid08_part209_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part209) = true := by rfl

def kid08_part210 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 72 true (0),
.cycle 0 32 true (0),
.cycle 0 30 true (0),
.last 29 (4,true),
.last 25 (4,true),
.last 65 (4,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 64, 8192, 128, 256, 32768, 2, 64, 262144, 128, 256, 8, 4, 64, 8192, 262144],[2, 4, 256, 1, 262144, 2, 8192, 16384, 256, 4096, 262144, 8192, 2, 4, 262144, 1, 262144, 2, 262144],264192⟩,
.cycle 0 26 true (0),
.cycle 11 60 true (0),
.cycle 0 69 true (0),
.cycle 43 32 true (6),
.cycle 0 28 true (0),
.cycle 38 54 true (3),
.last 69 (4,true),
.cycle 0 30 true (0),
.cycle 19 36 true (1),
.last 25 (4,true),
.last 65 (4,true),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 24 32 true (1),
.cycle 0 69 true (0),
.last 25 (4,true)
])
theorem kid08_part210_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part210) = true := by rfl

def kid08_part211 : Audit := .cycle 14 35 true (0)
theorem kid08_part211_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part211) = true := by rfl

def kid08_part212 : Audit := .split 21 (5,true) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 40 1 false (10),
.cycle 18 4 false (2),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 0 63 true (0),
.cycle 18 4 true (1),
.cycle 11 14 true (0),
.cycle 20 3 false (2),
.cycle 17 11 false (4),
.cycle 22 1 false (0),
.cycle 19 3 false (2),
.cycle 18 4 false (2),
.cycle 0 40 true (0),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 33 1 false (7),
.cycle 0 63 true (0),
.last 23 (4,true)
])
theorem kid08_part212_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part212) = true := by rfl

def kid08_part213 : Audit := .split 25 (4,true) (byMove [
.last 29 (5,true),
.cycle 0 29 true (0),
.cycle 0 36 true (0),
.last 31 (5,true),
.cycle 4 23 true (0),
.cycle 0 35 true (-1),
.last 58 (5,true),
.cycle 7 19 true (0),
.cycle 0 30 true (0),
.cycle 0 27 true (0),
.cycle 0 83 true (0),
.last 26 (5,true),
.cycle 0 37 true (0),
.last 28 (5,true),
.last 62 (5,true),
.cycle 0 34 true (0),
.last 61 (5,true),
.cycle 0 50 true (-1),
.last 56 (5,true),
.cycle 0 38 true (0),
.last 27 (5,true),
.cycle 0 27 true (0),
.cycle 29 31 true (4),
.last 26 (5,true)
])
theorem kid08_part213_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part213) = true := by rfl

def kid08_part214 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 17 4 false (3),
.last 25 (5,true),
.cycle 44 1 true (-2),
.last 21 (5,true),
.last 58 (5,true),
.last 23 (5,true),
.cycle 14 35 true (0),
.cycle 45 1 false (7),
.cycle 24 1 true (6),
.last 24 (5,true),
.cycle 34 1 false (10),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.last 25 (5,true),
.cycle 19 3 false (2),
.last 21 (5,true),
.last 56 (5,true),
.last 23 (5,true),
.cycle 0 57 true (0),
.cycle 13 41 true (0),
.cycle 24 1 true (6),
.last 23 (5,true)
])
theorem kid08_part214_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part214) = true := by rfl

def kid08_part215 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 17 4 false (3),
.cycle 0 32 true (0),
.last 21 (4,true),
.cycle 18 4 false (2),
.last 25 (4,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 2048, 8192, 128, 256, 32768, 2, 2048, 262144, 128, 256, 8, 4, 2048, 8192, 262144],[2, 4, 256, 1, 262144, 2, 8192, 16384, 256, 4096, 262144, 8192, 2, 4, 262144, 1, 262144, 2, 262144],330768⟩,
.cycle 14 35 true (0),
.cycle 45 1 false (7),
.last 23 (4,true),
.cycle 25 3 true (5),
.cycle 34 1 false (10),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.cycle 26 1 false (2),
.last 21 (4,true),
.cycle 18 4 false (2),
.last 25 (4,true),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 13 41 true (0),
.last 23 (4,true),
.last 22 (4,true)
])
theorem kid08_part215_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part215) = true := by rfl

def kid08_part191 : Audit := .split 19 (4,false) (byMove [(kid08_part192),(kid08_part193),(kid08_part194),(kid08_part195),(kid08_part196),(kid08_part197),(kid08_part198),(kid08_part199),(kid08_part200),(kid08_part201),(kid08_part202),(kid08_part203),(kid08_part204),(kid08_part205),(kid08_part206),(kid08_part207),(kid08_part208),(kid08_part209),(kid08_part210),(kid08_part211),(kid08_part212),(kid08_part213),(kid08_part214),(kid08_part215)])

theorem kid08_part191_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part191) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part192),(kid08_part193),(kid08_part194),(kid08_part195),(kid08_part196),(kid08_part197),(kid08_part198),(kid08_part199),(kid08_part200),(kid08_part201),(kid08_part202),(kid08_part203),(kid08_part204),(kid08_part205),(kid08_part206),(kid08_part207),(kid08_part208),(kid08_part209),(kid08_part210),(kid08_part211),(kid08_part212),(kid08_part213),(kid08_part214),(kid08_part215)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part192_checked

  · exact kid08_part198_checked

  · exact kid08_part204_checked

  · exact kid08_part210_checked

  · exact kid08_part193_checked

  · exact kid08_part199_checked

  · exact kid08_part205_checked

  · exact kid08_part211_checked

  · exact kid08_part194_checked

  · exact kid08_part200_checked

  · exact kid08_part206_checked

  · exact kid08_part212_checked

  · exact kid08_part195_checked

  · exact kid08_part201_checked

  · exact kid08_part207_checked

  · exact kid08_part213_checked

  · exact kid08_part196_checked

  · exact kid08_part202_checked

  · exact kid08_part208_checked

  · exact kid08_part214_checked

  · exact kid08_part197_checked

  · exact kid08_part203_checked

  · exact kid08_part209_checked

  · exact kid08_part215_checked

def kid08_part216 : Audit := .cycle 18 1 false (2)
theorem kid08_part216_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part216) = true := by rfl

def kid08_part217 : Audit := .cycle 0 23 true (0)
theorem kid08_part217_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part217) = true := by rfl

def kid08_part218 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 1 32 true (0),
.cycle 0 28 true (0),
.split 22 (4,true) (byMove [
.cycle 1 32 true (0),
.cycle 0 32 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 1 32 true (0),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 1 28 true (0),
.cycle 1 48 true (0),
.last 26 (4,false),
.cycle 0 32 true (0),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 1 48 true (0),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 30 true (0),
.last 29 (4,false),
.last 23 (4,false),
.cycle 1 28 true (0)
]),
.cycle 1 32 true (0),
.cycle 1 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 64, 2, 64],[2, 4, 4, 1, 64, 2, 64],80⟩,
.cycle 0 24 true (0),
.cycle 1 28 true (0),
.split 22 (4,false) (byMove [
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 30 true (0),
.cycle 30 1 false (4),
.last 24 (4,true),
.cycle 1 28 true (0),
.cycle 0 57 true (0),
.cycle 7 16 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 1 25 true (0),
.cycle 1 26 true (0),
.cycle 19 4 true (3),
.cycle 0 63 true (0),
.cycle 1 28 true (0),
.last 24 (4,true),
.cycle 1 26 true (0),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 2, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 1 25 true (0)
]),
.cycle 1 32 true (0),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 17 5 false (4),
.cycle 27 1 false (3),
.split 22 (4,true) (byMove [
.cycle 19 5 false (4),
.cycle 1 36 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 18 5 false (4),
.last 27 (4,false),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 1 34 true (0),
.last 24 (4,false),
.last 24 (4,false),
.cycle 0 30 true (0),
.last 26 (4,false),
.last 29 (4,false),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 0 30 true (0),
.last 27 (4,false),
.cycle 0 26 true (0),
.last 25 (4,false),
.cycle 1 34 true (0),
.last 24 (4,false),
.cycle 21 2 true (2)
]),
.cycle 0 30 true (0),
.cycle 1 32 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.split 22 (4,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 2, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.cycle 0 26 true (0),
.cycle 1 36 true (0),
.cycle 1 34 true (0),
.last 23 (4,true),
.cycle 21 2 true (3),
.cycle 1 51 true (0),
.cycle 1 63 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 1 25 true (0),
.cycle 1 26 true (0),
.cycle 1 32 true (0),
.cycle 17 9 false (4),
.cycle 5 18 true (0),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.cycle 2 24 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 1 25 true (0)
]),
.cycle 1 32 true (0)
])
theorem kid08_part218_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part218) = true := by rfl

def kid08_part219 : Audit := .cycle 0 51 true (0)
theorem kid08_part219_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part219) = true := by rfl

def kid08_part220 : Audit := .cycle 36 1 false (10)
theorem kid08_part220_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part220) = true := by rfl

def kid08_part222 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 43 1 false (9),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 0 96 true (0),
.cycle 0 30 true (0),
.cycle 45 1 false (11),
.cycle 35 1 false (9),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 0 30 true (0),
.last 25 (4,true),
.cycle 0 28 true (0),
.cycle 21 3 false (4),
.cycle 47 1 false (11),
.cycle 24 1 false (2),
.last 29 (4,true),
.last 25 (4,true),
.cycle 16 48 true (2),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 29 1 false (7),
.cycle 39 1 false (9),
.last 25 (4,true)
])
theorem kid08_part222_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part222) = true := by rfl

def kid08_part223 : Audit := .cycle 32 1 false (10)
theorem kid08_part223_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part223) = true := by rfl

def kid08_part224 : Audit := .cycle 17 3 false (3)
theorem kid08_part224_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part224) = true := by rfl

def kid08_part225 : Audit := .cycle 0 27 true (0)
theorem kid08_part225_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part225) = true := by rfl

def kid08_part226 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 0 27 true (0),
.last 23 (5,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.last 23 (5,true),
.cycle 14 39 true (0),
.last 23 (5,true),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.last 23 (5,true),
.cycle 0 27 true (0),
.last 23 (5,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 19 2 true (2),
.last 23 (5,true)
])
theorem kid08_part226_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part226) = true := by rfl

def kid08_part227 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 4 false (3),
.cycle 18 3 false (3),
.cycle 0 27 true (0),
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 18 4 true (2),
.last 22 (4,true),
.cycle 14 39 true (0),
.cycle 20 3 false (2),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 18 4 false (3),
.last 22 (4,true),
.cycle 0 27 true (0),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 19 2 true (2),
.last 22 (4,true)
])
theorem kid08_part227_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part227) = true := by rfl

def kid08_part228 : Audit := .cycle 6 14 true (0)
theorem kid08_part228_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part228) = true := by rfl

def kid08_part229 : Audit := .cycle 44 12 true (8)
theorem kid08_part229_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part229) = true := by rfl

def kid08_part230 : Audit := .cycle 23 10 true (4)
theorem kid08_part230_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part230) = true := by rfl

def kid08_part231 : Audit := .cycle 0 51 true (0)
theorem kid08_part231_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part231) = true := by rfl

def kid08_part232 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 29 1 true (5),
.last 26 (5,true),
.cycle 24 1 true (4),
.cycle 25 1 true (5),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true),
.cycle 25 1 true (5),
.last 23 (5,true),
.cycle 0 57 true (0),
.cycle 27 1 true (5),
.cycle 19 2 true (3),
.last 23 (5,true),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true)
])
theorem kid08_part232_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part232) = true := by rfl

def kid08_part233 : Audit := .split 20 (5,true) (byMove [
.cycle 0 55 true (0),
.cycle 0 24 true (0),
.cycle 28 2 true (4),
.cycle 27 1 false (3),
.last 23 (4,true),
.cycle 24 2 true (4),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6),
.cycle 24 2 true (4),
.last 29 (4,true),
.cycle 0 57 true (0),
.cycle 26 2 true (4),
.cycle 19 2 true (3),
.last 22 (4,true),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 0 47 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6)
])
theorem kid08_part233_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part233) = true := by rfl

def kid08_part234 : Audit := .cycle 33 1 false (7)
theorem kid08_part234_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part234) = true := by rfl

def kid08_part235 : Audit := .cycle 16 4 true (2)
theorem kid08_part235_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part235) = true := by rfl

def kid08_part236 : Audit := .cycle 17 3 false (3)
theorem kid08_part236_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part236) = true := by rfl

def kid08_part237 : Audit := .cycle 36 1 false (10)
theorem kid08_part237_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part237) = true := by rfl

def kid08_part238 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.last 21 (5,true),
.cycle 15 12 true (1),
.last 23 (5,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.last 23 (5,true),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 22 (5,true),
.cycle 5 16 true (0),
.cycle 22 3 true (4),
.last 21 (5,true)
])
theorem kid08_part238_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part238) = true := by rfl

def kid08_part239 : Audit := .split 20 (5,true) (byMove [
.cycle 0 75 true (0),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 23 (4,true),
.cycle 18 3 false (3),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 22 4 true (4),
.cycle 15 12 true (1),
.cycle 20 3 false (2),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 23 (4,true),
.last 22 (4,true),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 0 63 true (0),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 22 4 true (4)
])
theorem kid08_part239_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part239) = true := by rfl

def kid08_part240 : Audit := .cycle 0 59 true (0)
theorem kid08_part240_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part240) = true := by rfl

def kid08_part241 : Audit := .cycle 1 23 true (0)
theorem kid08_part241_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part241) = true := by rfl

def kid08_part242 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 2 32 true (0),
.cycle 0 28 true (0),
.last 22 (4,true),
.cycle 2 32 true (0),
.cycle 2 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 16, 64],[2, 4, 4, 1, 64, 2, 64],64⟩,
.cycle 0 24 true (0),
.cycle 2 28 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 16, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.last 23 (4,true),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 17 5 false (4),
.cycle 27 1 false (3),
.last 22 (4,true),
.last 24 (4,true),
.cycle 2 32 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 2 24 true (0),
.last 23 (4,true)
])
theorem kid08_part242_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part242) = true := by rfl

def kid08_part243 : Audit := .cycle 20 30 true (3)
theorem kid08_part243_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part243) = true := by rfl

def kid08_part244 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 33 1 true (7),
.cycle 32 1 true (0),
.last 21 (5,true),
.cycle 48 1 true (10),
.cycle 58 1 true (12),
.cycle 23 1 true (5),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true),
.cycle 25 1 true (5),
.cycle 29 1 true (5),
.last 22 (5,true),
.cycle 5 16 true (0),
.cycle 21 3 false (3),
.last 21 (5,true),
.cycle 0 57 true (0),
.cycle 31 1 true (7),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 21 (5,true)
])
theorem kid08_part244_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part244) = true := by rfl

def kid08_part245 : Audit := .split 20 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.cycle 32 2 true (6),
.last 21 (4,true),
.cycle 32 2 true (0),
.cycle 47 2 true (9),
.cycle 57 2 true (11),
.cycle 22 2 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6),
.cycle 24 2 true (4),
.cycle 28 2 true (4),
.cycle 28 2 true (4),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 24 (4,true),
.cycle 0 57 true (0),
.cycle 30 2 true (6),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (6)
])
theorem kid08_part245_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part245) = true := by rfl

def kid08_part221 : Audit := .split 19 (4,false) (byMove [(kid08_part222),(kid08_part223),(kid08_part224),(kid08_part225),(kid08_part226),(kid08_part227),(kid08_part228),(kid08_part229),(kid08_part230),(kid08_part231),(kid08_part232),(kid08_part233),(kid08_part234),(kid08_part235),(kid08_part236),(kid08_part237),(kid08_part238),(kid08_part239),(kid08_part240),(kid08_part241),(kid08_part242),(kid08_part243),(kid08_part244),(kid08_part245)])

theorem kid08_part221_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part221) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid08_part222),(kid08_part223),(kid08_part224),(kid08_part225),(kid08_part226),(kid08_part227),(kid08_part228),(kid08_part229),(kid08_part230),(kid08_part231),(kid08_part232),(kid08_part233),(kid08_part234),(kid08_part235),(kid08_part236),(kid08_part237),(kid08_part238),(kid08_part239),(kid08_part240),(kid08_part241),(kid08_part242),(kid08_part243),(kid08_part244),(kid08_part245)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part222_checked

  · exact kid08_part228_checked

  · exact kid08_part234_checked

  · exact kid08_part240_checked

  · exact kid08_part223_checked

  · exact kid08_part229_checked

  · exact kid08_part235_checked

  · exact kid08_part241_checked

  · exact kid08_part224_checked

  · exact kid08_part230_checked

  · exact kid08_part236_checked

  · exact kid08_part242_checked

  · exact kid08_part225_checked

  · exact kid08_part231_checked

  · exact kid08_part237_checked

  · exact kid08_part243_checked

  · exact kid08_part226_checked

  · exact kid08_part232_checked

  · exact kid08_part238_checked

  · exact kid08_part244_checked

  · exact kid08_part227_checked

  · exact kid08_part233_checked

  · exact kid08_part239_checked

  · exact kid08_part245_checked

def kid08_part246 : Audit := .split 20 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.cycle 32 1 true (6),
.split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 33 1 false (1),
.cycle 28 1 false (2),
.last 23 (4,false),
.last 23 (4,false),
.cycle 32 1 true (6),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 28 1 true (4),
.last 22 (4,false),
.cycle 25 1 true (5),
.cycle 0 26 true (0),
.cycle 31 1 true (3),
.cycle 17 5 false (4),
.last 27 (4,false),
.last 23 (4,false),
.last 23 (4,false),
.cycle 32 1 true (6),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 22 (4,false),
.cycle 25 1 true (5)
]),
.cycle 32 1 true (0),
.cycle 47 1 true (9),
.cycle 57 1 true (11),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.last 54 (4,false),
.last 22 (4,false),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.cycle 47 1 true (9),
.last 34 (4,false),
.cycle 29 1 true (5),
.last 22 (4,false),
.cycle 22 1 true (6),
.cycle 32 1 true (6),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 22 (4,false),
.last 24 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 45 (4,false),
.cycle 5 44 true (0),
.last 22 (4,false),
.cycle 22 1 true (6)
]),
.cycle 22 1 true (6),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.cycle 28 1 true (4),
.cycle 5 16 true (0),
.split 21 (4,true) (byMove [
.last 26 (4,false),
.cycle 34 1 false (10),
.last 30 (4,false),
.cycle 26 1 true (4),
.last 23 (4,false),
.last 23 (4,false),
.cycle 6 16 true (0),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.cycle 0 57 true (0),
.last 24 (4,false),
.last 23 (4,false),
.cycle 32 1 true (4),
.cycle 16 6 true (2),
.cycle 17 5 false (4),
.cycle 26 1 true (4),
.last 23 (4,false),
.last 23 (4,false),
.cycle 63 1 true (11),
.cycle 24 1 true (4),
.last 27 (4,false),
.cycle 51 1 true (9),
.last 24 (4,false),
.cycle 20 2 true (3)
]),
.cycle 21 3 false (3),
.cycle 0 57 true (0),
.cycle 30 1 true (6),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.last 49 (4,false),
.cycle 31 1 true (5),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 25 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 57 (4,false),
.cycle 30 1 true (6),
.cycle 3 19 true (0),
.last 22 (4,false),
.cycle 22 1 true (6),
.last 36 (4,false),
.cycle 24 1 true (4),
.last 24 (4,false),
.cycle 51 1 true (9),
.last 25 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 22 1 true (6)
]),
.cycle 22 1 true (6)
])
theorem kid08_part246_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part246) = true := by rfl

def kid08_part126 : Audit := .split 18 (5,false) (byMove [(kid08_part127),(kid08_part128),(kid08_part129),(kid08_part130),(kid08_part131),(kid08_part156),(kid08_part157),(kid08_part158),(kid08_part159),(kid08_part160),(kid08_part161),(kid08_part186),(kid08_part187),(kid08_part188),(kid08_part189),(kid08_part190),(kid08_part191),(kid08_part216),(kid08_part217),(kid08_part218),(kid08_part219),(kid08_part220),(kid08_part221),(kid08_part246)])

theorem kid08_part126_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (kid08_part126) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part127),(kid08_part128),(kid08_part129),(kid08_part130),(kid08_part131),(kid08_part156),(kid08_part157),(kid08_part158),(kid08_part159),(kid08_part160),(kid08_part161),(kid08_part186),(kid08_part187),(kid08_part188),(kid08_part189),(kid08_part190),(kid08_part191),(kid08_part216),(kid08_part217),(kid08_part218),(kid08_part219),(kid08_part220),(kid08_part221),(kid08_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part127_checked

  · exact kid08_part157_checked

  · exact kid08_part187_checked

  · exact kid08_part217_checked

  · exact kid08_part128_checked

  · exact kid08_part158_checked

  · exact kid08_part188_checked

  · exact kid08_part218_checked

  · exact kid08_part129_checked

  · exact kid08_part159_checked

  · exact kid08_part189_checked

  · exact kid08_part219_checked

  · exact kid08_part130_checked

  · exact kid08_part160_checked

  · exact kid08_part190_checked

  · exact kid08_part220_checked

  · exact kid08_part131_checked

  · exact kid08_part161_checked

  · exact kid08_part191_checked

  · exact kid08_part221_checked

  · exact kid08_part156_checked

  · exact kid08_part186_checked

  · exact kid08_part216_checked

  · exact kid08_part246_checked

def kid08_part247 : Audit := .cycle 21 1 false (7)
theorem kid08_part247_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,0⟩)) (kid08_part247) = true := by rfl

def kid08_part248 : Audit := .cycle 28 1 false (10)
theorem kid08_part248_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,1⟩)) (kid08_part248) = true := by rfl

def kid08_part249 : Audit := .cycle 21 1 false (7)
theorem kid08_part249_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,2⟩)) (kid08_part249) = true := by rfl

def kid08_part250 : Audit := .cycle 28 1 false (10)
theorem kid08_part250_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,3⟩)) (kid08_part250) = true := by rfl

def kid08_part252 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.cycle 34 1 false (8),
.split 23 (5,false) (byMove [
.cycle 0 48 true (0),
.cycle 43 1 false (9),
.cycle 31 1 false (3),
.cycle 0 25 true (0),
.cycle 34 1 false (8),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 0 47 true (0),
.cycle 0 50 true (0),
.cycle 3 21 true (0),
.cycle 22 2 true (5),
.cycle 23 1 true (5),
.cycle 0 36 true (0),
.cycle 20 8 true (4),
.cycle 0 26 true (0),
.cycle 17 31 true (3),
.cycle 18 12 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.last 25 (5,true),
.cycle 23 1 true (5)
]),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.cycle 0 33 true (0),
.cycle 0 46 true (0),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 47 true (0),
.cycle 0 50 true (0),
.cycle 3 21 true (0),
.cycle 22 2 true (6),
.last 26 (5,true),
.cycle 0 24 true (0),
.cycle 0 53 true (0),
.cycle 8 16 true (0),
.cycle 0 33 true (0),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 21 12 true (5),
.cycle 20 4 true (4),
.cycle 0 26 true (0),
.cycle 0 46 true (0),
.last 25 (5,true),
.last 26 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 17 28 true (3),
.cycle 17 38 true (3),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
]),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 4 19 true (0),
.cycle 0 29 true (0),
.split 23 (5,false) (byMove [
.cycle 20 5 true (4),
.cycle 0 27 true (0),
.cycle 31 1 false (3),
.cycle 0 50 true (0),
.cycle 0 29 true (0),
.last 24 (5,true),
.cycle 17 30 true (3),
.cycle 0 35 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 24 (5,true),
.cycle 25 5 true (5),
.cycle 0 27 true (0),
.cycle 17 7 true (3),
.cycle 5 19 true (0),
.cycle 0 29 true (0),
.last 24 (5,true),
.cycle 0 48 true (0),
.cycle 21 11 true (5),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 0 49 true (0),
.last 24 (5,true)
]),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 0 45 true (0),
.cycle 0 55 true (0),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 17 30 true (3),
.cycle 0 35 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 0 47 true (0),
.cycle 21 10 true (5),
.cycle 0 45 true (0),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 6 18 true (0),
.cycle 21 4 true (5),
.cycle 0 26 true (0),
.cycle 0 55 true (0),
.cycle 18 6 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
])
])
theorem kid08_part252_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part252) = true := by rfl

def kid08_part253 : Audit := .cycle 0 22 true (0)
theorem kid08_part253_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part253) = true := by rfl

def kid08_part254 : Audit := .cycle 20 1 false (4)
theorem kid08_part254_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part254) = true := by rfl

def kid08_part255 : Audit := .cycle 19 1 false (3)
theorem kid08_part255_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part255) = true := by rfl

def kid08_part256 : Audit := .split 19 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 37 1 false (9),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.split 20 (5,false) (byMove [
.cycle 0 32 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 19 2 true (2),
.last 23 (5,true),
.cycle 32 12 true (2),
.cycle 19 8 true (1),
.last 31 (5,true),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 37 1 false (9),
.last 60 (5,true),
.last 22 (5,true),
.last 23 (5,true)
]),
.cycle 0 31 true (0),
.cycle 17 28 true (3),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 22 1 true (4),
.split 20 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.cycle 20 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 25 1 false (9),
.cycle 0 22 true (0),
.cycle 22 2 true (4),
.last 21 (5,true),
.cycle 22 12 true (4),
.cycle 24 4 true (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 22 (5,true),
.cycle 20 1 false (4),
.cycle 0 57 true (0),
.cycle 1 31 true (0),
.cycle 17 28 true (3),
.cycle 0 22 true (0),
.cycle 23 2 true (3),
.last 21 (5,true)
]),
.cycle 0 24 true (0),
.cycle 28 3 true (4),
.cycle 0 35 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.split 20 (5,false) (byMove [
.last 31 (5,true),
.cycle 0 39 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.last 54 (5,true),
.cycle 0 24 true (0),
.cycle 26 3 true (3),
.cycle 0 35 true (0),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 33 5 true (3),
.last 25 (5,true),
.cycle 17 11 true (1),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.last 53 (5,true),
.cycle 0 24 true (0),
.last 27 (5,true),
.cycle 0 35 true (0),
.cycle 18 4 false (4),
.last 21 (5,true)
]),
.cycle 0 31 true (0),
.cycle 1 22 true (0),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.cycle 24 1 true (2),
.split 20 (5,false) (byMove [
.cycle 17 34 true (3),
.cycle 0 24 true (0),
.last 23 (5,true),
.cycle 0 35 true (0),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 0 49 true (0),
.cycle 32 25 true (6),
.cycle 21 10 true (5),
.cycle 0 22 true (0),
.cycle 22 2 true (4),
.last 21 (5,true),
.cycle 29 1 false (9),
.cycle 24 4 true (4),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 0 57 true (0),
.cycle 1 31 true (0),
.cycle 2 22 true (0),
.cycle 0 22 true (0),
.cycle 24 2 true (2),
.last 21 (5,true)
])
])
theorem kid08_part256_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part256) = true := by rfl

def kid08_part258 : Audit := .cycle 0 24 true (0)
theorem kid08_part258_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part258) = true := by rfl

def kid08_part259 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (9),
.cycle 30 1 false (6),
.cycle 29 1 false (5),
.cycle 28 1 false (6),
.cycle 38 1 false (8),
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.cycle 28 1 true (6),
.cycle 38 1 false (10),
.cycle 22 11 true (2),
.cycle 27 3 true (5),
.cycle 0 31 true (0),
.cycle 29 1 false (5),
.cycle 28 1 false (6),
.cycle 0 33 true (0),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (10),
.cycle 40 1 false (12),
.cycle 28 1 true (6),
.cycle 32 1 false (8)
])
theorem kid08_part259_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part259) = true := by rfl

def kid08_part260 : Audit := .cycle 21 1 false (3)
theorem kid08_part260_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part260) = true := by rfl

def kid08_part261 : Audit := .cycle 20 1 false (2)
theorem kid08_part261_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part261) = true := by rfl

def kid08_part262 : Audit := .split 20 (4,false) (byMove [
.cycle 0 31 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 25 1 true (3),
.cycle 19 2 true (2),
.cycle 33 11 true (2),
.last 32 (5,true),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 36 1 false (10),
.cycle 88 1 false (16),
.last 24 (5,true),
.cycle 18 4 false (4)
])
theorem kid08_part262_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part262) = true := by rfl

def kid08_part263 : Audit := .cycle 19 1 false (3)
theorem kid08_part263_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part263) = true := by rfl

def kid08_part264 : Audit := .split 30 (4,false) (byMove [
.cycle 0 31 true (0),
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.cycle 31 1 false (7),
.cycle 30 1 false (8),
.cycle 0 32 true (0),
.cycle 0 31 true (0),
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 31 1 false (9),
.cycle 30 1 true (8),
.cycle 0 32 true (0),
.cycle 20 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 31 1 false (7),
.cycle 30 1 false (8),
.cycle 41 1 false (13),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 38 1 false (12),
.cycle 42 1 false (14),
.cycle 30 1 true (8),
.cycle 0 32 true (0)
])
theorem kid08_part264_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part264) = true := by rfl

def kid08_part265 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (8),
.cycle 34 1 false (10),
.cycle 34 1 false (8),
.cycle 23 24 true (4),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.cycle 42 1 false (12),
.cycle 31 1 false (9),
.cycle 22 1 true (6),
.cycle 47 24 true (9),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.cycle 24 24 true (3),
.cycle 44 1 false (12),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 23 24 true (4),
.cycle 49 24 true (9),
.cycle 22 1 true (6),
.cycle 23 24 true (6)
])
theorem kid08_part265_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part265) = true := by rfl

def kid08_part266 : Audit := .cycle 0 22 true (0)
theorem kid08_part266_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part266) = true := by rfl

def kid08_part267 : Audit := .cycle 20 1 false (4)
theorem kid08_part267_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part267) = true := by rfl

def kid08_part268 : Audit := .split 20 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.cycle 19 2 true (3),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 24 1 false (8),
.cycle 0 22 true (0),
.cycle 23 1 true (5),
.last 21 (5,true),
.cycle 22 11 true (4),
.cycle 25 3 true (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.cycle 18 4 true (3),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 22 24 true (4),
.cycle 0 22 true (0),
.last 22 (5,true),
.last 21 (5,true)
])
theorem kid08_part268_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part268) = true := by rfl

def kid08_part269 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.last 22 (4,false),
.cycle 22 1 true (6),
.last 32 (4,false),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.last 22 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part269_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part269) = true := by rfl

def kid08_part270 : Audit := .cycle 0 24 true (0)
theorem kid08_part270_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part270) = true := by rfl

def kid08_part271 : Audit := .split 22 (4,false) (byMove [
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 32 1 false (6),
.cycle 40 1 false (10),
.cycle 18 6 false (4),
.cycle 19 8 true (2),
.cycle 0 57 true (0),
.cycle 7 16 true (0),
.cycle 41 14 true (6),
.cycle 0 24 true (0),
.cycle 27 1 true (5),
.last 23 (5,true),
.cycle 24 11 true (4),
.cycle 28 3 true (4),
.cycle 0 63 true (0),
.cycle 29 1 false (5),
.cycle 18 6 false (4),
.cycle 16 8 true (2),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 2, 64],[8, 8, 10, 8, 32, 64, 64],64⟩,
.cycle 0 24 true (0),
.last 24 (5,true),
.last 23 (5,true)
])
theorem kid08_part271_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part271) = true := by rfl

def kid08_part272 : Audit := .split 32 (4,false) (byMove [
.cycle 0 33 true (0),
.cycle 41 1 false (11),
.cycle 34 1 false (8),
.cycle 33 1 false (7),
.cycle 32 1 false (8),
.cycle 0 36 true (0),
.cycle 0 33 true (0),
.cycle 41 1 false (13),
.cycle 34 1 false (10),
.cycle 33 1 false (9),
.cycle 32 1 true (8),
.cycle 0 36 true (0),
.cycle 22 11 true (4),
.cycle 31 3 true (7),
.cycle 0 35 true (0),
.cycle 33 1 false (7),
.cycle 32 1 false (8),
.cycle 45 1 false (13),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 40 1 false (12),
.cycle 44 1 false (14),
.cycle 32 1 true (8),
.cycle 0 39 true (0)
])
theorem kid08_part272_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part272) = true := by rfl

def kid08_part273 : Audit := .cycle 20 1 false (2)
theorem kid08_part273_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part273) = true := by rfl

def kid08_part274 : Audit := .split 20 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 0 81 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (8),
.cycle 33 1 false (9),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 26 11 true (4),
.cycle 18 7 false (4),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 20 36 true (2),
.cycle 65 39 true (7),
.last 22 (5,true),
.last 21 (5,true)
])
theorem kid08_part274_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part274) = true := by rfl

def kid08_part275 : Audit := .cycle 19 1 false (3)
theorem kid08_part275_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part275) = true := by rfl

def kid08_part276 : Audit := .split 30 (4,false) (byMove [
.cycle 0 31 true (0),
.cycle 16 38 true (2),
.cycle 8 23 true (0),
.cycle 0 41 true (0),
.cycle 0 37 true (0),
.cycle 0 32 true (0),
.cycle 0 31 true (0),
.cycle 0 65 true (0),
.cycle 0 50 true (0),
.cycle 0 57 true (0),
.cycle 30 1 true (8),
.cycle 0 32 true (0),
.cycle 20 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 10 21 true (0),
.last 49 (5,true),
.cycle 28 26 true (6),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 0 87 true (0),
.cycle 16 49 true (2),
.cycle 30 1 true (8),
.cycle 0 32 true (0)
])
theorem kid08_part276_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part276) = true := by rfl

def kid08_part277 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.last 25 (5,true),
.cycle 1 23 true (0),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.cycle 1 33 true (0),
.cycle 1 46 true (0),
.cycle 22 1 true (6),
.cycle 1 23 true (0),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 4 19 true (0),
.last 25 (5,true),
.cycle 21 11 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 1 45 true (0),
.cycle 1 55 true (0),
.cycle 22 1 true (6),
.cycle 1 23 true (0)
])
theorem kid08_part277_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part277) = true := by rfl

def kid08_part278 : Audit := .cycle 0 22 true (0)
theorem kid08_part278_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part278) = true := by rfl

def kid08_part279 : Audit := .cycle 25 1 false (7)
theorem kid08_part279_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part279) = true := by rfl

def kid08_part280 : Audit := .split 20 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 33 1 false (7),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 0 48 true (0),
.cycle 50 32 true (8),
.cycle 8 15 true (0),
.cycle 0 22 true (0),
.cycle 23 1 true (5),
.last 21 (5,true),
.cycle 21 11 true (3),
.cycle 27 3 true (5),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 45 true (0),
.cycle 0 22 true (0),
.last 22 (5,true),
.last 21 (5,true)
])
theorem kid08_part280_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part280) = true := by rfl

def kid08_part281 : Audit := .split 21 (5,true) (byMove [
.last 48 (4,false),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 24 (4,false),
.cycle 24 1 true (2),
.cycle 0 22 true (0),
.cycle 55 1 true (11),
.last 30 (4,false),
.cycle 3 19 true (0),
.last 22 (4,false),
.cycle 22 1 true (6),
.cycle 34 1 true (6),
.last 24 (4,false),
.cycle 24 1 true (4),
.last 51 (4,false),
.last 24 (4,false),
.cycle 22 3 false (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part281_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part281) = true := by rfl

def kid08_part257 : Audit := .split 19 (5,false) (byMove [(kid08_part258),(kid08_part259),(kid08_part260),(kid08_part261),(kid08_part262),(kid08_part263),(kid08_part264),(kid08_part265),(kid08_part266),(kid08_part267),(kid08_part268),(kid08_part269),(kid08_part270),(kid08_part271),(kid08_part272),(kid08_part273),(kid08_part274),(kid08_part275),(kid08_part276),(kid08_part277),(kid08_part278),(kid08_part279),(kid08_part280),(kid08_part281)])

theorem kid08_part257_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part257) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part258),(kid08_part259),(kid08_part260),(kid08_part261),(kid08_part262),(kid08_part263),(kid08_part264),(kid08_part265),(kid08_part266),(kid08_part267),(kid08_part268),(kid08_part269),(kid08_part270),(kid08_part271),(kid08_part272),(kid08_part273),(kid08_part274),(kid08_part275),(kid08_part276),(kid08_part277),(kid08_part278),(kid08_part279),(kid08_part280),(kid08_part281)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part258_checked

  · exact kid08_part264_checked

  · exact kid08_part270_checked

  · exact kid08_part276_checked

  · exact kid08_part259_checked

  · exact kid08_part265_checked

  · exact kid08_part271_checked

  · exact kid08_part277_checked

  · exact kid08_part260_checked

  · exact kid08_part266_checked

  · exact kid08_part272_checked

  · exact kid08_part278_checked

  · exact kid08_part261_checked

  · exact kid08_part267_checked

  · exact kid08_part273_checked

  · exact kid08_part279_checked

  · exact kid08_part262_checked

  · exact kid08_part268_checked

  · exact kid08_part274_checked

  · exact kid08_part280_checked

  · exact kid08_part263_checked

  · exact kid08_part269_checked

  · exact kid08_part275_checked

  · exact kid08_part281_checked

def kid08_part282 : Audit := .cycle 28 1 false (10)
theorem kid08_part282_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part282) = true := by rfl

def kid08_part283 : Audit := .cycle 21 1 false (7)
theorem kid08_part283_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part283) = true := by rfl

def kid08_part284 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 20 2 true (5),
.cycle 21 1 true (5),
.cycle 19 12 true (4),
.cycle 19 8 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.last 23 (5,true),
.cycle 21 1 true (5)
]),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 20 2 true (6),
.cycle 21 1 false (7),
.cycle 0 22 true (0),
.cycle 30 1 false (12),
.cycle 23 1 false (9),
.cycle 22 1 false (8),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 22 1 false (6),
.last 23 (5,true),
.cycle 21 1 false (7),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (11),
.cycle 33 1 false (13),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.split 21 (5,false) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 24 1 false (8),
.last 22 (5,true),
.cycle 19 5 true (4),
.cycle 36 1 false (10),
.cycle 33 1 false (11),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 45 1 false (13),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 19 11 true (5),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 24 1 false (8),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 44 1 false (14),
.cycle 19 10 true (5),
.cycle 28 1 false (10),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 25 1 false (9),
.cycle 19 4 true (5),
.cycle 25 1 false (9),
.cycle 32 1 false (12),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part284_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part284) = true := by rfl

def kid08_part285 : Audit := .cycle 0 20 true (0)
theorem kid08_part285_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part285) = true := by rfl

def kid08_part286 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 20 2 true (5),
.cycle 21 1 true (5),
.cycle 20 12 true (4),
.cycle 20 8 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.last 23 (5,true),
.cycle 21 1 true (5)
]),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 20 2 true (6),
.cycle 21 1 false (7),
.cycle 0 22 true (0),
.cycle 30 1 false (12),
.cycle 23 1 false (9),
.cycle 22 1 false (8),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 22 1 false (6),
.last 23 (5,true),
.cycle 21 1 false (7),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (11),
.cycle 33 1 false (13),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.split 21 (5,false) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true),
.cycle 20 5 true (4),
.cycle 19 5 true (4),
.cycle 33 1 false (11),
.cycle 22 1 false (4),
.cycle 20 2 false (6),
.cycle 21 1 false (5),
.cycle 18 24 true (4),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.cycle 28 1 false (10),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 25 1 false (9),
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.cycle 32 1 false (12),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part286_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part286) = true := by rfl

def kid08_part288 : Audit := .cycle 0 20 true (0)
theorem kid08_part288_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part288) = true := by rfl

def kid08_part289 : Audit := .cycle 28 1 false (8)
theorem kid08_part289_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part289) = true := by rfl

def kid08_part290 : Audit := .cycle 21 1 false (5)
theorem kid08_part290_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part290) = true := by rfl

def kid08_part291 : Audit := .cycle 20 1 false (4)
theorem kid08_part291_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part291) = true := by rfl

def kid08_part292 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 true (4),
.last 21 (5,false),
.cycle 20 11 true (3),
.cycle 20 3 true (3),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 20 1 true (4),
.last 21 (5,false)
])
theorem kid08_part292_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part292) = true := by rfl

def kid08_part293 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 20 1 true (4),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.last 21 (4,false),
.cycle 20 1 true (4)
])
theorem kid08_part293_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part293) = true := by rfl

def kid08_part294 : Audit := .cycle 0 20 true (0)
theorem kid08_part294_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part294) = true := by rfl

def kid08_part295 : Audit := .cycle 28 1 false (10)
theorem kid08_part295_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part295) = true := by rfl

def kid08_part296 : Audit := .cycle 21 1 false (7)
theorem kid08_part296_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part296) = true := by rfl

def kid08_part297 : Audit := .cycle 20 1 false (6)
theorem kid08_part297_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part297) = true := by rfl

def kid08_part298 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part298_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part298) = true := by rfl

def kid08_part299 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part299_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part299) = true := by rfl

def kid08_part300 : Audit := .split 30 (4,false) (byMove [
.cycle 0 31 true (0),
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.cycle 31 1 false (7),
.cycle 30 1 false (8),
.last 31 (5,false),
.cycle 0 31 true (0),
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 31 1 false (9),
.cycle 30 1 true (8),
.last 31 (5,false),
.cycle 20 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 31 1 false (7),
.cycle 30 1 false (8),
.last 31 (5,false),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 38 1 false (12),
.cycle 42 1 false (14),
.cycle 30 1 true (8),
.last 31 (5,false)
])
theorem kid08_part300_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part300) = true := by rfl

def kid08_part301 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (8),
.cycle 34 1 false (10),
.last 25 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.last 33 (5,false),
.cycle 31 1 false (9),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.last 29 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.last 45 (5,false),
.last 55 (5,false),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part301_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part301) = true := by rfl

def kid08_part302 : Audit := .cycle 0 22 true (0)
theorem kid08_part302_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part302) = true := by rfl

def kid08_part303 : Audit := .cycle 20 1 false (4)
theorem kid08_part303_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part303) = true := by rfl

def kid08_part304 : Audit := .split 20 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 24 1 false (8),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 19 2 true (4),
.cycle 22 11 true (4),
.last 24 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.last 55 (5,false),
.cycle 1 30 true (0),
.last 45 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 18 4 true (4)
])
theorem kid08_part304_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part304) = true := by rfl

def kid08_part305 : Audit := .split 20 (5,false) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 19 2 true (4),
.last 24 (4,false),
.last 27 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 56 true (0),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 19 3 false (5)
])
theorem kid08_part305_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part305) = true := by rfl

def kid08_part306 : Audit := .cycle 0 20 true (0)
theorem kid08_part306_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part306) = true := by rfl

def kid08_part307 : Audit := .cycle 1 19 true (0)
theorem kid08_part307_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part307) = true := by rfl

def kid08_part308 : Audit := .cycle 27 1 false (9)
theorem kid08_part308_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part308) = true := by rfl

def kid08_part309 : Audit := .cycle 31 1 false (11)
theorem kid08_part309_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part309) = true := by rfl

def kid08_part310 : Audit := .split 20 (4,false) (byMove [
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 24 1 false (6),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.last 42 (5,false),
.cycle 31 1 false (11),
.cycle 27 1 false (9),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 24 1 false (8),
.cycle 22 3 true (6),
.last 23 (5,false),
.cycle 31 1 false (11),
.cycle 18 3 true (4),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part310_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part310) = true := by rfl

def kid08_part311 : Audit := .split 20 (5,false) (byMove [
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (4,false),
.cycle 27 1 false (9),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 24 1 false (8),
.last 23 (4,false),
.cycle 0 26 true (0),
.cycle 31 1 false (11),
.cycle 18 3 true (4),
.cycle 19 3 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part311_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part311) = true := by rfl

def kid08_part287 : Audit := .split 19 (5,true) (byMove [(kid08_part288),(kid08_part289),(kid08_part290),(kid08_part291),(kid08_part292),(kid08_part293),(kid08_part294),(kid08_part295),(kid08_part296),(kid08_part297),(kid08_part298),(kid08_part299),(kid08_part300),(kid08_part301),(kid08_part302),(kid08_part303),(kid08_part304),(kid08_part305),(kid08_part306),(kid08_part307),(kid08_part308),(kid08_part309),(kid08_part310),(kid08_part311)])

theorem kid08_part287_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part287) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part288),(kid08_part289),(kid08_part290),(kid08_part291),(kid08_part292),(kid08_part293),(kid08_part294),(kid08_part295),(kid08_part296),(kid08_part297),(kid08_part298),(kid08_part299),(kid08_part300),(kid08_part301),(kid08_part302),(kid08_part303),(kid08_part304),(kid08_part305),(kid08_part306),(kid08_part307),(kid08_part308),(kid08_part309),(kid08_part310),(kid08_part311)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part288_checked

  · exact kid08_part294_checked

  · exact kid08_part300_checked

  · exact kid08_part306_checked

  · exact kid08_part289_checked

  · exact kid08_part295_checked

  · exact kid08_part301_checked

  · exact kid08_part307_checked

  · exact kid08_part290_checked

  · exact kid08_part296_checked

  · exact kid08_part302_checked

  · exact kid08_part308_checked

  · exact kid08_part291_checked

  · exact kid08_part297_checked

  · exact kid08_part303_checked

  · exact kid08_part309_checked

  · exact kid08_part292_checked

  · exact kid08_part298_checked

  · exact kid08_part304_checked

  · exact kid08_part310_checked

  · exact kid08_part293_checked

  · exact kid08_part299_checked

  · exact kid08_part305_checked

  · exact kid08_part311_checked

def kid08_part312 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 16 68 true (2),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.cycle 36 1 false (6),
.split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 31 1 false (7),
.cycle 35 1 false (9),
.last 25 (5,true),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 16 29 true (2),
.cycle 47 1 false (11),
.cycle 33 1 false (7),
.cycle 22 2 true (5),
.cycle 23 1 true (5),
.cycle 20 12 true (4),
.cycle 20 8 true (4),
.cycle 0 26 true (0),
.cycle 29 1 false (7),
.last 25 (5,true),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 16 68 true (2),
.cycle 16 88 true (2),
.last 25 (5,true),
.cycle 23 1 true (5)
]),
.cycle 0 23 true (0),
.cycle 16 80 true (2),
.cycle 8 15 true (0),
.cycle 43 1 false (11),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 16 29 true (2),
.cycle 47 1 false (11),
.cycle 33 1 false (7),
.cycle 22 2 true (6),
.last 27 (5,true),
.cycle 0 24 true (0),
.cycle 16 35 true (2),
.cycle 16 56 true (2),
.cycle 9 15 true (0),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 20 12 true (4),
.cycle 21 4 true (5),
.cycle 0 26 true (0),
.cycle 44 1 false (10),
.last 25 (5,true),
.last 27 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 16 80 true (2),
.cycle 16 100 true (2),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
]),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.cycle 16 11 true (2),
.split 23 (5,false) (byMove [
.cycle 25 5 true (5),
.cycle 0 27 true (0),
.cycle 34 1 false (6),
.cycle 44 1 false (8),
.last 25 (5,true),
.last 25 (5,true),
.cycle 16 84 true (2),
.cycle 7 17 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 20 13 true (4),
.last 24 (5,true),
.cycle 19 5 true (3),
.cycle 20 15 true (4),
.cycle 16 88 true (2),
.cycle 31 1 false (5),
.last 25 (5,true),
.last 25 (5,true),
.cycle 20 36 true (4),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 6 19 true (0),
.last 24 (5,true)
]),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 16 27 true (2),
.cycle 16 37 true (2),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 16 84 true (2),
.cycle 7 17 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 20 13 true (4),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 20 35 true (4),
.cycle 20 10 true (4),
.cycle 16 27 true (2),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 16 60 true (2),
.cycle 20 4 true (4),
.cycle 20 14 true (4),
.cycle 16 37 true (2),
.cycle 18 6 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 16 32 true (2),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
])
])
theorem kid08_part312_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part312) = true := by rfl

def kid08_part313 : Audit := .split 24 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.cycle 29 1 false (5),
.split 25 (5,false) (byMove [
.cycle 17 30 true (3),
.cycle 45 1 false (9),
.cycle 33 1 false (3),
.cycle 0 27 true (0),
.cycle 29 2 false (5),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 17 29 true (3),
.cycle 17 32 true (3),
.cycle 3 23 true (0),
.cycle 24 2 true (5),
.cycle 25 1 true (5),
.cycle 45 1 false (9),
.cycle 22 8 true (4),
.cycle 20 6 true (4),
.cycle 17 35 true (3),
.cycle 18 16 true (3),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 17 36 true (3),
.last 27 (5,true),
.cycle 25 1 true (5)
]),
.cycle 0 25 true (0),
.cycle 17 32 true (3),
.cycle 20 13 true (4),
.cycle 17 28 true (3),
.cycle 24 1 true (6),
.split 25 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 17 29 true (3),
.cycle 17 32 true (3),
.cycle 3 23 true (0),
.cycle 24 2 true (6),
.last 28 (5,true),
.cycle 0 26 true (0),
.cycle 17 37 true (3),
.cycle 8 18 true (0),
.cycle 20 13 true (4),
.cycle 24 2 true (6),
.cycle 25 1 true (7),
.cycle 23 12 true (5),
.cycle 22 4 true (4),
.cycle 0 28 true (0),
.cycle 17 28 true (3),
.last 27 (5,true),
.last 28 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 17 32 true (3),
.cycle 17 44 true (3),
.cycle 24 2 true (6),
.cycle 25 1 true (7)
]),
.cycle 23 11 true (5),
.cycle 22 3 true (4),
.cycle 0 27 true (0),
.cycle 4 21 true (0),
.cycle 16 11 true (2),
.split 25 (5,false) (byMove [
.cycle 22 5 true (4),
.cycle 0 29 true (0),
.cycle 33 1 false (3),
.cycle 78 1 false (12),
.cycle 29 2 false (5),
.last 26 (5,true),
.cycle 17 34 true (3),
.cycle 20 15 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 21 5 true (4),
.last 26 (5,true),
.cycle 27 5 true (5),
.cycle 20 7 true (4),
.cycle 17 9 true (3),
.cycle 5 21 true (0),
.cycle 16 11 true (2),
.last 26 (5,true),
.cycle 17 30 true (3),
.cycle 23 11 true (5),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 23 5 true (5),
.last 26 (5,true)
]),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 17 27 true (3),
.cycle 17 39 true (3),
.cycle 24 1 true (6),
.split 25 (5,false) (byMove [
.cycle 17 34 true (3),
.cycle 20 15 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 21 5 true (4),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 17 29 true (3),
.cycle 23 10 true (5),
.cycle 17 27 true (3),
.cycle 24 2 true (6),
.cycle 25 1 true (7),
.cycle 6 20 true (0),
.cycle 23 4 true (5),
.cycle 20 6 true (4),
.cycle 17 39 true (3),
.cycle 18 8 true (3),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 17 36 true (3),
.cycle 24 2 true (6),
.cycle 25 1 true (7)
])
])
theorem kid08_part313_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part313) = true := by rfl

def kid08_part314 : Audit := .cycle 30 1 false (10)
theorem kid08_part314_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part314) = true := by rfl

def kid08_part315 : Audit := .cycle 19 1 false (3)
theorem kid08_part315_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part315) = true := by rfl

def kid08_part316 : Audit := .split 19 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.split 20 (5,false) (byMove [
.cycle 0 63 true (0),
.cycle 50 1 false (8),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 26 true (0),
.last 25 (5,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (2),
.last 22 (5,true),
.cycle 14 39 true (0),
.cycle 19 8 true (1),
.cycle 0 30 true (0),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 26 true (0),
.last 25 (5,true),
.cycle 0 57 true (0),
.cycle 39 1 false (11),
.last 22 (5,true),
.last 22 (5,true)
]),
.cycle 23 1 false (7),
.cycle 31 1 false (11),
.cycle 26 1 false (8),
.cycle 30 1 false (10),
.cycle 18 2 true (3),
.split 20 (5,true) (byMove [
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 22 (5,false),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 23 (5,false),
.cycle 0 22 true (0),
.last 25 (5,false),
.last 22 (5,false),
.last 25 (5,false),
.last 29 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 18 4 true (3),
.last 22 (5,false)
]),
.cycle 26 11 true (4),
.cycle 16 8 true (2),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.split 20 (5,false) (byMove [
.last 26 (5,true),
.cycle 0 51 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 35 1 false (11),
.cycle 32 1 false (8),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 15 12 true (1),
.last 25 (5,true),
.cycle 39 1 false (11),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 48 14 true (8),
.cycle 26 11 true (4),
.last 24 (5,true),
.cycle 5 16 true (0),
.cycle 18 4 false (4),
.last 21 (5,true)
]),
.cycle 0 58 true (0),
.cycle 1 22 true (0),
.cycle 17 27 true (3),
.cycle 37 39 true (3),
.cycle 18 3 false (4),
.split 20 (5,true) (byMove [
.last 25 (5,false),
.cycle 0 24 true (0),
.last 26 (5,false),
.last 33 (5,false),
.cycle 18 3 false (4),
.last 22 (5,false),
.last 48 (5,false),
.last 58 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.last 25 (5,false),
.last 22 (5,false),
.last 25 (5,false),
.last 29 (5,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.last 22 (5,false),
.cycle 0 57 true (0),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 18 5 false (5),
.last 22 (5,false)
])
])
theorem kid08_part316_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part316) = true := by rfl

def kid08_part318 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 4, 1, 64],[8, 8, 9, 8, 32, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 1, 64],[8, 8, 9, 8, 32, 64, 64],64⟩,
.last 45 (5,true),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 1, 64],[8, 8, 1, 8, 32, 64, 64],64⟩,
.cycle 0 29 true (0),
.cycle 21 40 true (3),
.cycle 26 15 true (4),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 1, 64],[8, 8, 9, 8, 32, 64, 64],64⟩,
.cycle 28 1 true (6),
.cycle 0 30 true (0),
.cycle 27 11 true (5),
.cycle 26 3 true (4),
.cycle 0 31 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 1, 64],[8, 8, 9, 8, 32, 64, 64],64⟩,
.cycle 33 17 true (3),
.cycle 24 5 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 21 33 true (3),
.cycle 21 49 true (3),
.cycle 28 1 true (6),
.cycle 21 42 true (3)
])
theorem kid08_part318_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part318) = true := by rfl

def kid08_part319 : Audit := .cycle 0 57 true (0)
theorem kid08_part319_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part319) = true := by rfl

def kid08_part320 : Audit := .cycle 21 1 false (3)
theorem kid08_part320_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part320) = true := by rfl

def kid08_part321 : Audit := .cycle 20 1 false (2)
theorem kid08_part321_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part321) = true := by rfl

def kid08_part322 : Audit := .split 20 (4,false) (byMove [
.cycle 0 63 true (0),
.cycle 49 1 false (9),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 7 24 true (0),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 18 4 true (2),
.cycle 19 2 true (2),
.cycle 14 39 true (0),
.last 29 (5,true),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.last 26 (5,true),
.cycle 0 57 true (0),
.cycle 38 1 false (12),
.last 23 (5,true),
.cycle 18 4 false (4)
])
theorem kid08_part322_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part322) = true := by rfl

def kid08_part323 : Audit := .cycle 19 1 false (3)
theorem kid08_part323_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part323) = true := by rfl

def kid08_part324 : Audit := .cycle 23 1 false (7)
theorem kid08_part324_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part324) = true := by rfl

def kid08_part325 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 32 1 false (10),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 22 1 true (6),
.cycle 32 1 false (12),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 26 1 false (8),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.cycle 22 1 true (6),
.cycle 50 1 false (14)
])
theorem kid08_part325_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part325) = true := by rfl

def kid08_part326 : Audit := .split 24 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 33 1 false (9),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 27 1 false (7),
.cycle 0 25 true (0),
.cycle 33 1 false (11),
.cycle 26 1 false (8),
.cycle 25 1 false (7),
.cycle 24 1 true (6),
.cycle 27 1 false (9),
.cycle 23 11 true (5),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 22 3 true (4),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 32 1 false (10),
.cycle 36 1 false (12),
.cycle 24 1 true (6),
.cycle 23 10 true (5)
])
theorem kid08_part326_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part326) = true := by rfl

def kid08_part327 : Audit := .cycle 30 1 false (10)
theorem kid08_part327_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part327) = true := by rfl

def kid08_part328 : Audit := .cycle 18 2 true (3)
theorem kid08_part328_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part328) = true := by rfl

def kid08_part329 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 24 1 true (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.cycle 22 1 true (6),
.last 24 (4,false),
.last 28 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 20 2 true (4),
.cycle 22 1 true (6)
])
theorem kid08_part329_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part329) = true := by rfl

def kid08_part330 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 16 34 true (2),
.cycle 8 30 true (0),
.cycle 3 26 true (0),
.last 32 (5,true),
.cycle 26 12 true (4),
.cycle 0 29 true (0),
.cycle 16 46 true (2),
.cycle 8 21 true (0),
.cycle 21 14 true (3),
.cycle 28 1 true (6),
.cycle 26 12 true (4),
.cycle 26 11 true (4),
.cycle 27 3 true (5),
.cycle 0 31 true (0),
.cycle 10 26 true (0),
.last 32 (5,true),
.cycle 24 5 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 16 39 true (2),
.cycle 16 55 true (2),
.cycle 28 1 true (6),
.cycle 16 30 true (2)
])
theorem kid08_part330_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part330) = true := by rfl

def kid08_part331 : Audit := .cycle 16 8 true (2)
theorem kid08_part331_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part331) = true := by rfl

def kid08_part332 : Audit := .cycle 25 1 false (7)
theorem kid08_part332_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part332) = true := by rfl

def kid08_part333 : Audit := .cycle 20 1 false (2)
theorem kid08_part333_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part333) = true := by rfl

def kid08_part334 : Audit := .split 20 (4,false) (byMove [
.last 27 (5,true),
.cycle 33 40 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 37 1 false (11),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.last 21 (5,true),
.cycle 15 12 true (1),
.cycle 18 7 false (4),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.cycle 18 6 false (4),
.cycle 5 16 true (0),
.last 22 (5,true),
.last 21 (5,true)
])
theorem kid08_part334_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part334) = true := by rfl

def kid08_part335 : Audit := .cycle 19 1 false (3)
theorem kid08_part335_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part335) = true := by rfl

def kid08_part336 : Audit := .split 57 (4,false) (byMove [
.cycle 0 58 true (0),
.cycle 28 51 true (4),
.cycle 22 36 true (3),
.cycle 66 1 false (12),
.cycle 31 30 true (6),
.cycle 0 59 true (0),
.cycle 0 58 true (0),
.cycle 49 32 true (7),
.cycle 41 17 true (6),
.cycle 9 49 true (0),
.cycle 57 1 true (13),
.cycle 0 59 true (0),
.cycle 54 11 true (10),
.cycle 56 3 true (12),
.cycle 0 60 true (0),
.cycle 24 34 true (3),
.cycle 15 48 true (1),
.cycle 32 26 true (6),
.cycle 0 58 true (0),
.cycle 1 57 true (0),
.cycle 15 64 true (1),
.cycle 28 62 true (4),
.cycle 57 1 true (13),
.cycle 0 59 true (0)
])
theorem kid08_part336_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part336) = true := by rfl

def kid08_part337 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 16 68 true (2),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.cycle 36 1 false (6),
.cycle 1 23 true (0),
.cycle 0 23 true (0),
.cycle 16 80 true (2),
.cycle 8 15 true (0),
.cycle 43 1 false (11),
.cycle 22 1 true (6),
.cycle 1 23 true (0),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.cycle 16 11 true (2),
.cycle 20 11 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 16 27 true (2),
.cycle 16 37 true (2),
.cycle 22 1 true (6),
.cycle 1 23 true (0)
])
theorem kid08_part337_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part337) = true := by rfl

def kid08_part338 : Audit := .split 24 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.last 27 (5,true),
.cycle 2 24 true (0),
.cycle 0 25 true (0),
.cycle 17 32 true (3),
.cycle 20 13 true (4),
.cycle 17 28 true (3),
.cycle 24 1 true (6),
.cycle 17 32 true (3),
.cycle 23 11 true (5),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 4 21 true (0),
.last 27 (5,true),
.cycle 22 3 true (4),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 17 27 true (3),
.cycle 17 39 true (3),
.cycle 24 1 true (6),
.cycle 2 24 true (0)
])
theorem kid08_part338_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part338) = true := by rfl

def kid08_part339 : Audit := .split 47 (4,false) (byMove [
.cycle 0 48 true (0),
.cycle 0 77 true (0),
.cycle 8 40 true (0),
.cycle 0 59 true (0),
.cycle 0 55 true (0),
.cycle 5 77 true (0),
.cycle 0 48 true (0),
.cycle 5 73 true (0),
.cycle 29 19 true (3),
.cycle 5 55 true (0),
.cycle 47 1 true (11),
.cycle 0 91 true (0),
.cycle 43 11 true (7),
.cycle 46 3 true (10),
.cycle 0 50 true (0),
.cycle 10 38 true (0),
.cycle 14 40 true (0),
.cycle 0 50 true (0),
.cycle 0 48 true (0),
.cycle 1 47 true (0),
.cycle 14 56 true (0),
.cycle 37 39 true (3),
.cycle 47 1 true (11),
.cycle 20 30 true (3)
])
theorem kid08_part339_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part339) = true := by rfl

def kid08_part340 : Audit := .split 21 (5,true) (byMove [
.last 32 (4,false),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 25 1 false (7),
.last 24 (4,false),
.last 28 (4,false),
.cycle 32 1 false (10),
.cycle 18 4 true (3),
.last 25 (4,false),
.last 32 (4,false),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 19 3 false (4),
.last 63 (4,false),
.last 24 (4,false),
.last 28 (4,false),
.last 51 (4,false),
.cycle 20 2 true (3),
.last 25 (4,false)
])
theorem kid08_part340_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part340) = true := by rfl

def kid08_part341 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.last 22 (4,false),
.last 32 (4,false),
.cycle 18 3 false (4),
.cycle 29 1 true (1),
.last 47 (4,false),
.last 57 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.cycle 22 1 true (6),
.last 24 (4,false),
.last 28 (4,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.cycle 19 3 false (4),
.cycle 0 57 true (0),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 20 2 true (4),
.cycle 22 1 true (6)
])
theorem kid08_part341_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part341) = true := by rfl

def kid08_part317 : Audit := .split 19 (5,false) (byMove [(kid08_part318),(kid08_part319),(kid08_part320),(kid08_part321),(kid08_part322),(kid08_part323),(kid08_part324),(kid08_part325),(kid08_part326),(kid08_part327),(kid08_part328),(kid08_part329),(kid08_part330),(kid08_part331),(kid08_part332),(kid08_part333),(kid08_part334),(kid08_part335),(kid08_part336),(kid08_part337),(kid08_part338),(kid08_part339),(kid08_part340),(kid08_part341)])

theorem kid08_part317_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part317) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part318),(kid08_part319),(kid08_part320),(kid08_part321),(kid08_part322),(kid08_part323),(kid08_part324),(kid08_part325),(kid08_part326),(kid08_part327),(kid08_part328),(kid08_part329),(kid08_part330),(kid08_part331),(kid08_part332),(kid08_part333),(kid08_part334),(kid08_part335),(kid08_part336),(kid08_part337),(kid08_part338),(kid08_part339),(kid08_part340),(kid08_part341)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part318_checked

  · exact kid08_part324_checked

  · exact kid08_part330_checked

  · exact kid08_part336_checked

  · exact kid08_part319_checked

  · exact kid08_part325_checked

  · exact kid08_part331_checked

  · exact kid08_part337_checked

  · exact kid08_part320_checked

  · exact kid08_part326_checked

  · exact kid08_part332_checked

  · exact kid08_part338_checked

  · exact kid08_part321_checked

  · exact kid08_part327_checked

  · exact kid08_part333_checked

  · exact kid08_part339_checked

  · exact kid08_part322_checked

  · exact kid08_part328_checked

  · exact kid08_part334_checked

  · exact kid08_part340_checked

  · exact kid08_part323_checked

  · exact kid08_part329_checked

  · exact kid08_part335_checked

  · exact kid08_part341_checked

def kid08_part342 : Audit := .cycle 0 51 true (0)
theorem kid08_part342_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part342) = true := by rfl

def kid08_part343 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.split 29 (5,false) (byMove [
.cycle 0 30 true (0),
.cycle 38 1 false (10),
.cycle 31 1 false (7),
.cycle 30 1 false (6),
.cycle 28 2 false (8),
.cycle 29 1 false (7),
.cycle 0 30 true (0),
.cycle 38 1 false (12),
.cycle 31 1 false (9),
.cycle 30 1 false (8),
.cycle 28 2 true (7),
.cycle 29 1 true (7),
.cycle 19 12 true (4),
.cycle 26 8 true (6),
.cycle 0 32 true (0),
.cycle 30 1 false (6),
.cycle 28 2 false (8),
.cycle 29 1 false (7),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 37 1 false (11),
.cycle 41 1 false (13),
.last 31 (5,true),
.cycle 29 1 true (7)
]),
.cycle 0 29 true (0),
.cycle 37 1 false (13),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.cycle 28 1 true (8),
.split 29 (5,false) (byMove [
.cycle 0 30 true (0),
.cycle 38 1 false (12),
.cycle 31 1 false (9),
.cycle 30 1 false (8),
.cycle 28 2 true (8),
.cycle 29 1 false (9),
.cycle 0 30 true (0),
.cycle 38 1 false (14),
.cycle 31 1 false (11),
.cycle 30 1 false (10),
.cycle 28 2 true (8),
.cycle 29 1 true (9),
.cycle 19 12 true (4),
.cycle 27 4 true (7),
.cycle 0 32 true (0),
.cycle 30 1 false (8),
.last 31 (5,true),
.cycle 29 1 false (9),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 37 1 false (13),
.cycle 41 1 false (15),
.cycle 28 2 true (8),
.cycle 29 1 true (9)
]),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.split 29 (5,false) (byMove [
.cycle 31 5 true (7),
.cycle 0 33 true (0),
.cycle 31 1 false (7),
.cycle 30 1 false (6),
.cycle 28 2 false (8),
.cycle 29 1 false (7),
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 30 (5,true),
.cycle 26 5 true (6),
.cycle 1 32 true (0),
.cycle 41 1 false (13),
.cycle 30 1 false (6),
.cycle 28 2 false (8),
.cycle 29 1 false (7),
.cycle 26 24 true (6),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 30 (5,true)
]),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (12),
.cycle 40 1 false (14),
.cycle 28 1 true (8),
.split 29 (5,false) (byMove [
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 30 (5,true),
.cycle 0 30 true (0),
.cycle 26 23 true (6),
.cycle 20 10 true (4),
.cycle 36 1 false (12),
.cycle 28 2 true (8),
.cycle 29 1 true (9),
.cycle 33 1 false (11),
.cycle 26 4 true (6),
.cycle 1 31 true (0),
.cycle 40 1 false (14),
.cycle 18 12 true (4),
.last 30 (5,true),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 1 55 true (0),
.cycle 28 2 true (8),
.cycle 29 1 true (9)
])
])
theorem kid08_part343_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part343) = true := by rfl

def kid08_part344 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 30 1 false (8),
.split 21 (5,false) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 30 1 false (8),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 23 20 true (4),
.cycle 33 1 false (9),
.cycle 28 1 false (8),
.cycle 20 2 true (5),
.cycle 21 1 true (5),
.cycle 25 1 false (7),
.cycle 19 8 true (4),
.cycle 31 1 false (9),
.cycle 32 1 false (10),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.last 23 (5,true),
.cycle 21 1 true (5)
]),
.cycle 0 21 true (0),
.cycle 17 24 true (3),
.cycle 38 1 false (12),
.cycle 29 1 false (9),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 23 20 true (4),
.cycle 33 1 false (9),
.cycle 28 1 false (8),
.cycle 20 2 true (6),
.last 24 (5,true),
.cycle 0 22 true (0),
.cycle 43 20 true (9),
.cycle 8 14 true (0),
.cycle 38 1 false (12),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 30 1 false (8),
.last 23 (5,true),
.last 24 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 24 true (3),
.cycle 17 32 true (3),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.cycle 22 20 true (4),
.split 21 (5,false) (byMove [
.cycle 19 5 true (4),
.cycle 0 25 true (0),
.cycle 26 1 false (4),
.cycle 35 1 false (7),
.cycle 0 25 true (0),
.last 22 (5,true),
.cycle 17 26 true (3),
.cycle 40 1 false (12),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 22 20 true (4),
.last 22 (5,true),
.cycle 23 5 true (5),
.cycle 32 1 false (10),
.cycle 17 5 true (3),
.cycle 26 1 false (8),
.cycle 22 20 true (4),
.last 22 (5,true),
.cycle 24 20 true (5),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 2 21 true (0),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 21 20 true (4),
.cycle 45 20 true (9),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 17 26 true (3),
.cycle 40 1 false (12),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 22 20 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 23 20 true (6),
.cycle 19 10 true (5),
.cycle 22 20 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 6 16 true (0),
.cycle 19 4 true (5),
.cycle 17 26 true (3),
.cycle 45 20 true (9),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part344_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part344) = true := by rfl

def kid08_part345 : Audit := .cycle 0 20 true (0)
theorem kid08_part345_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part345) = true := by rfl

def kid08_part346 : Audit := .split 20 (4,false) (byMove [
.cycle 18 23 true (4),
.cycle 39 1 false (11),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.split 21 (5,true) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.last 24 (5,false),
.cycle 0 23 true (0),
.last 26 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.last 31 (5,false),
.cycle 28 1 false (8),
.last 23 (5,false),
.last 22 (5,false),
.cycle 25 1 false (7),
.last 25 (5,false),
.cycle 0 28 true (0),
.cycle 32 1 false (10),
.cycle 18 4 true (4),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (5),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 18 22 true (4),
.cycle 18 26 true (4),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (6),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 18 25 true (4),
.cycle 19 12 true (5),
.cycle 18 26 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 18 22 true (4),
.cycle 18 30 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 37 1 false (11),
.cycle 22 3 true (6),
.cycle 19 3 true (5),
.cycle 18 26 true (4),
.cycle 18 3 true (4),
.split 21 (5,true) (byMove [
.last 26 (5,false),
.cycle 0 25 true (0),
.last 24 (5,false),
.last 34 (5,false),
.last 26 (5,false),
.last 23 (5,false),
.cycle 18 26 true (4),
.cycle 37 1 false (11),
.last 24 (5,false),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 23 (5,false),
.last 26 (5,false),
.cycle 23 5 true (5),
.cycle 17 5 true (3),
.cycle 26 1 false (8),
.cycle 18 5 true (4),
.last 23 (5,false),
.cycle 18 24 true (4),
.last 32 (5,false),
.last 24 (5,false),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 18 24 true (4),
.cycle 18 30 true (4),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.cycle 3 19 true (0),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 14 true (5),
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.cycle 18 27 true (4),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part346_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part346) = true := by rfl

def kid08_part348 : Audit := .cycle 29 1 false (9)
theorem kid08_part348_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part348) = true := by rfl

def kid08_part349 : Audit := .cycle 22 1 false (6)
theorem kid08_part349_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part349) = true := by rfl

def kid08_part350 : Audit := .split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 true (5),
.last 22 (5,false),
.cycle 20 11 true (4),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.cycle 21 1 true (5),
.last 22 (5,false)
])
theorem kid08_part350_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part350) = true := by rfl

def kid08_part351 : Audit := .cycle 0 21 true (0)
theorem kid08_part351_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part351) = true := by rfl

def kid08_part352 : Audit := .split 21 (5,false) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 20 2 true (4),
.last 23 (4,false),
.cycle 0 22 true (0),
.cycle 20 34 true (4),
.last 30 (4,false),
.cycle 28 1 false (8),
.last 22 (4,false),
.cycle 21 1 true (5),
.cycle 25 1 false (7),
.last 24 (4,false),
.cycle 20 3 true (4),
.cycle 32 1 false (10),
.cycle 18 4 true (4),
.last 23 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 21 1 true (5)
])
theorem kid08_part352_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part352) = true := by rfl

def kid08_part353 : Audit := .split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 21 1 true (3),
.last 32 (4,false),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 22 (4,false),
.cycle 21 1 true (3)
])
theorem kid08_part353_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part353) = true := by rfl

def kid08_part354 : Audit := .cycle 0 20 true (0)
theorem kid08_part354_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part354) = true := by rfl

def kid08_part355 : Audit := .split 51 (5,false) (byMove [
.cycle 61 1 false (17),
.cycle 54 1 false (14),
.last 53 (4,false),
.cycle 0 53 true (0),
.cycle 50 2 true (12),
.cycle 61 1 false (17),
.cycle 0 52 true (0),
.cycle 20 32 true (4),
.last 60 (4,false),
.cycle 58 1 false (16),
.last 52 (4,false),
.cycle 51 1 true (13),
.cycle 55 1 false (15),
.last 54 (4,false),
.cycle 49 3 true (11),
.cycle 62 1 false (18),
.cycle 18 34 true (4),
.cycle 55 1 false (15),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.last 78 (4,false),
.last 52 (4,false),
.cycle 51 1 true (13)
])
theorem kid08_part355_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part355) = true := by rfl

def kid08_part356 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.last 29 (5,false),
.cycle 0 29 true (0),
.cycle 37 1 false (13),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.cycle 28 1 true (8),
.last 29 (5,false),
.cycle 20 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.last 29 (5,false),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (12),
.cycle 40 1 false (14),
.cycle 28 1 true (8),
.last 29 (5,false)
])
theorem kid08_part356_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part356) = true := by rfl

def kid08_part357 : Audit := .cycle 26 1 false (8)
theorem kid08_part357_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part357) = true := by rfl

def kid08_part358 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 18 24 true (4),
.last 31 (5,false),
.cycle 29 1 false (9),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.last 25 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 41 (5,false),
.last 49 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part358_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part358) = true := by rfl

def kid08_part359 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.last 21 (4,false),
.cycle 23 1 false (5),
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8521760, 16777216, 2, 128, 256, 32768, 524290, 16777216, 8192, 128, 256, 2097152, 4, 16777216, 524288, 128, 256, 8, 16, 16777216, 2, 16777216],[2, 4, 16, 1, 2048, 32, 8192, 16384, 65536, 4096, 2048, 131072, 524288, 1048576, 4194304, 262144, 2048, 8388608, 2, 4, 16, 1, 2048, 32, 16777216],23151632⟩,
.last 40 (4,false),
.last 28 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.last 21 (4,false),
.cycle 25 1 false (7),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8521760, 16777216, 256, 128, 256, 32768, 524290, 16777216, 256, 128, 256, 2097152, 4, 16777216, 256, 128, 256, 8, 16, 16777216, 256, 16777216],[2, 4, 16, 1, 2048, 32, 8192, 16384, 65536, 4096, 2048, 131072, 524288, 1048576, 4194304, 262144, 2048, 8388608, 2, 4, 16, 1, 2048, 32, 16777216],23151632⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8521760, 16777216, 512, 128, 256, 32768, 524290, 16777216, 512, 128, 256, 2097152, 4, 16777216, 512, 128, 256, 8, 16, 16777216, 512, 16777216],[2, 4, 16, 1, 2048, 32, 8192, 16384, 65536, 4096, 2048, 131072, 524288, 1048576, 4194304, 262144, 2048, 8388608, 2, 4, 16, 1, 2048, 32, 16777216],23151632⟩,
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part359_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part359) = true := by rfl

def kid08_part360 : Audit := .cycle 23 1 false (7)
theorem kid08_part360_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part360) = true := by rfl

def kid08_part361 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part361_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part361) = true := by rfl

def kid08_part362 : Audit := .split 22 (5,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 21 2 true (5),
.cycle 0 26 true (0),
.cycle 0 23 true (0),
.cycle 17 26 true (3),
.last 31 (4,false),
.cycle 29 1 false (9),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 26 1 false (8),
.last 25 (4,false),
.cycle 20 3 true (4),
.cycle 33 1 false (11),
.cycle 18 5 true (4),
.cycle 35 1 false (11),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 33 true (3),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part362_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part362) = true := by rfl

def kid08_part363 : Audit := .cycle 30 1 false (10)
theorem kid08_part363_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part363) = true := by rfl

def kid08_part364 : Audit := .cycle 18 2 true (4)
theorem kid08_part364_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part364) = true := by rfl

def kid08_part365 : Audit := .split 21 (5,false) (byMove [
.cycle 23 43 true (3),
.cycle 32 26 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 1 false (3),
.cycle 25 1 false (7),
.last 24 (4,false),
.last 33 (4,false),
.cycle 32 1 false (10),
.cycle 18 4 true (3),
.cycle 20 2 true (3),
.cycle 16 29 true (2),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 1 false (3),
.cycle 0 35 true (0),
.last 24 (4,false),
.cycle 2 23 true (0),
.last 51 (4,false),
.cycle 19 5 false (5),
.cycle 19 3 false (5)
])
theorem kid08_part365_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part365) = true := by rfl

def kid08_part366 : Audit := .cycle 0 20 true (0)
theorem kid08_part366_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part366) = true := by rfl

def kid08_part367 : Audit := .cycle 1 19 true (0)
theorem kid08_part367_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part367) = true := by rfl

def kid08_part368 : Audit := .cycle 2 18 true (0)
theorem kid08_part368_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part368) = true := by rfl

def kid08_part369 : Audit := .cycle 21 23 true (4)
theorem kid08_part369_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part369) = true := by rfl

def kid08_part370 : Audit := .split 20 (4,false) (byMove [
.last 43 (5,false),
.cycle 39 1 false (11),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.last 42 (5,false),
.cycle 18 26 true (4),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 33 (5,false),
.cycle 22 3 true (6),
.last 23 (5,false),
.cycle 18 26 true (4),
.cycle 18 3 true (4),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part370_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part370) = true := by rfl

def kid08_part371 : Audit := .split 20 (5,false) (byMove [
.cycle 19 23 true (4),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 20 2 true (5),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (4,false),
.cycle 3 18 true (0),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 37 1 false (11),
.last 23 (4,false),
.cycle 20 3 true (5),
.cycle 19 26 true (4),
.cycle 18 3 true (4),
.cycle 19 3 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part371_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part371) = true := by rfl

def kid08_part347 : Audit := .split 19 (5,true) (byMove [(kid08_part348),(kid08_part349),(kid08_part350),(kid08_part351),(kid08_part352),(kid08_part353),(kid08_part354),(kid08_part355),(kid08_part356),(kid08_part357),(kid08_part358),(kid08_part359),(kid08_part360),(kid08_part361),(kid08_part362),(kid08_part363),(kid08_part364),(kid08_part365),(kid08_part366),(kid08_part367),(kid08_part368),(kid08_part369),(kid08_part370),(kid08_part371)])

theorem kid08_part347_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part347) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part348),(kid08_part349),(kid08_part350),(kid08_part351),(kid08_part352),(kid08_part353),(kid08_part354),(kid08_part355),(kid08_part356),(kid08_part357),(kid08_part358),(kid08_part359),(kid08_part360),(kid08_part361),(kid08_part362),(kid08_part363),(kid08_part364),(kid08_part365),(kid08_part366),(kid08_part367),(kid08_part368),(kid08_part369),(kid08_part370),(kid08_part371)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part348_checked

  · exact kid08_part354_checked

  · exact kid08_part360_checked

  · exact kid08_part366_checked

  · exact kid08_part349_checked

  · exact kid08_part355_checked

  · exact kid08_part361_checked

  · exact kid08_part367_checked

  · exact kid08_part350_checked

  · exact kid08_part356_checked

  · exact kid08_part362_checked

  · exact kid08_part368_checked

  · exact kid08_part351_checked

  · exact kid08_part357_checked

  · exact kid08_part363_checked

  · exact kid08_part369_checked

  · exact kid08_part352_checked

  · exact kid08_part358_checked

  · exact kid08_part364_checked

  · exact kid08_part370_checked

  · exact kid08_part353_checked

  · exact kid08_part359_checked

  · exact kid08_part365_checked

  · exact kid08_part371_checked

def kid08_part251 : Audit := .split 18 (4,true) (byMove [(kid08_part252),(kid08_part253),(kid08_part254),(kid08_part255),(kid08_part256),(kid08_part257),(kid08_part282),(kid08_part283),(kid08_part284),(kid08_part285),(kid08_part286),(kid08_part287),(kid08_part312),(kid08_part313),(kid08_part314),(kid08_part315),(kid08_part316),(kid08_part317),(kid08_part342),(kid08_part343),(kid08_part344),(kid08_part345),(kid08_part346),(kid08_part347)])

theorem kid08_part251_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (kid08_part251) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part252),(kid08_part253),(kid08_part254),(kid08_part255),(kid08_part256),(kid08_part257),(kid08_part282),(kid08_part283),(kid08_part284),(kid08_part285),(kid08_part286),(kid08_part287),(kid08_part312),(kid08_part313),(kid08_part314),(kid08_part315),(kid08_part316),(kid08_part317),(kid08_part342),(kid08_part343),(kid08_part344),(kid08_part345),(kid08_part346),(kid08_part347)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part252_checked

  · exact kid08_part282_checked

  · exact kid08_part312_checked

  · exact kid08_part342_checked

  · exact kid08_part253_checked

  · exact kid08_part283_checked

  · exact kid08_part313_checked

  · exact kid08_part343_checked

  · exact kid08_part254_checked

  · exact kid08_part284_checked

  · exact kid08_part314_checked

  · exact kid08_part344_checked

  · exact kid08_part255_checked

  · exact kid08_part285_checked

  · exact kid08_part315_checked

  · exact kid08_part345_checked

  · exact kid08_part256_checked

  · exact kid08_part286_checked

  · exact kid08_part316_checked

  · exact kid08_part346_checked

  · exact kid08_part257_checked

  · exact kid08_part287_checked

  · exact kid08_part317_checked

  · exact kid08_part347_checked

def kid08_part373 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.split 23 (4,false) (byMove [
.cycle 0 48 true (0),
.cycle 43 1 false (9),
.cycle 31 1 false (3),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 34 1 false (8),
.cycle 0 24 true (0),
.cycle 0 47 true (0),
.cycle 0 50 true (0),
.cycle 3 21 true (0),
.cycle 23 1 true (5),
.cycle 22 2 true (5),
.cycle 0 36 true (0),
.cycle 20 8 true (4),
.cycle 0 26 true (0),
.cycle 17 31 true (3),
.last 24 (4,true),
.cycle 18 12 true (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 23 1 true (5),
.last 25 (4,true)
]),
.cycle 34 1 false (8),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.cycle 0 33 true (0),
.cycle 0 46 true (0),
.split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 47 true (0),
.cycle 0 50 true (0),
.cycle 3 21 true (0),
.last 26 (4,true),
.cycle 22 2 true (6),
.cycle 0 24 true (0),
.cycle 0 53 true (0),
.cycle 8 16 true (0),
.cycle 0 33 true (0),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 21 12 true (5),
.cycle 20 4 true (4),
.cycle 0 26 true (0),
.cycle 0 46 true (0),
.last 26 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 17 28 true (3),
.cycle 17 38 true (3),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 4 19 true (0),
.split 23 (4,false) (byMove [
.cycle 20 5 true (4),
.cycle 0 27 true (0),
.cycle 31 1 false (3),
.cycle 0 50 true (0),
.last 24 (4,true),
.cycle 0 29 true (0),
.cycle 17 30 true (3),
.cycle 0 35 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 0 25 true (0),
.cycle 25 5 true (5),
.cycle 0 27 true (0),
.cycle 17 7 true (3),
.cycle 5 19 true (0),
.last 24 (4,true),
.cycle 0 29 true (0),
.cycle 0 48 true (0),
.cycle 21 11 true (5),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 0 49 true (0)
]),
.cycle 0 29 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 0 45 true (0),
.cycle 0 55 true (0),
.split 23 (4,false) (byMove [
.cycle 17 30 true (3),
.cycle 0 35 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 0 47 true (0),
.cycle 21 10 true (5),
.cycle 0 45 true (0),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 6 18 true (0),
.cycle 21 4 true (5),
.cycle 0 26 true (0),
.cycle 0 55 true (0),
.last 24 (4,true),
.cycle 18 6 true (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6)
])
theorem kid08_part373_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part373) = true := by rfl

def kid08_part374 : Audit := .cycle 0 22 true (0)
theorem kid08_part374_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part374) = true := by rfl

def kid08_part375 : Audit := .cycle 20 1 false (4)
theorem kid08_part375_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part375) = true := by rfl

def kid08_part376 : Audit := .cycle 19 1 false (3)
theorem kid08_part376_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part376) = true := by rfl

def kid08_part378 : Audit := .cycle 0 24 true (0)
theorem kid08_part378_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part378) = true := by rfl

def kid08_part379 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (9),
.cycle 30 1 false (6),
.cycle 29 1 false (5),
.cycle 38 1 false (8),
.cycle 28 1 false (6),
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.cycle 38 1 false (10),
.cycle 28 1 true (6),
.cycle 22 11 true (2),
.cycle 27 3 true (5),
.cycle 0 31 true (0),
.cycle 29 1 false (5),
.cycle 0 33 true (0),
.cycle 28 1 false (6),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (10),
.cycle 40 1 false (12),
.cycle 32 1 false (8),
.cycle 28 1 true (6)
])
theorem kid08_part379_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part379) = true := by rfl

def kid08_part380 : Audit := .cycle 21 1 false (3)
theorem kid08_part380_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part380) = true := by rfl

def kid08_part381 : Audit := .cycle 20 1 false (2)
theorem kid08_part381_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part381) = true := by rfl

def kid08_part382 : Audit := .cycle 19 1 false (3)
theorem kid08_part382_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part382) = true := by rfl

def kid08_part383 : Audit := .split 20 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 19 2 true (2),
.cycle 25 1 true (3),
.cycle 33 11 true (2),
.last 32 (4,true),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 36 1 false (10),
.cycle 88 1 false (16),
.cycle 18 4 false (4),
.last 24 (4,true)
])
theorem kid08_part383_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part383) = true := by rfl

def kid08_part384 : Audit := .split 30 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.cycle 31 1 false (7),
.cycle 0 32 true (0),
.cycle 30 1 false (8),
.cycle 0 31 true (0),
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 31 1 false (9),
.cycle 0 32 true (0),
.cycle 30 1 true (8),
.cycle 20 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 31 1 false (7),
.cycle 41 1 false (13),
.cycle 30 1 false (8),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 38 1 false (12),
.cycle 42 1 false (14),
.cycle 0 32 true (0),
.cycle 30 1 true (8)
])
theorem kid08_part384_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part384) = true := by rfl

def kid08_part385 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (8),
.cycle 34 1 false (10),
.cycle 23 24 true (4),
.cycle 34 1 false (8),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.cycle 42 1 false (12),
.cycle 31 1 false (9),
.cycle 47 24 true (9),
.cycle 22 1 true (6),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.cycle 44 1 false (12),
.cycle 24 24 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 23 24 true (4),
.cycle 49 24 true (9),
.cycle 23 24 true (6),
.cycle 22 1 true (6)
])
theorem kid08_part385_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part385) = true := by rfl

def kid08_part386 : Audit := .cycle 0 22 true (0)
theorem kid08_part386_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part386) = true := by rfl

def kid08_part387 : Audit := .cycle 20 1 false (4)
theorem kid08_part387_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part387) = true := by rfl

def kid08_part388 : Audit := .split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 22 1 true (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 22 1 true (6),
.last 22 (5,false),
.last 32 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 20 2 true (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.cycle 22 1 true (6),
.last 22 (5,false)
])
theorem kid08_part388_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part388) = true := by rfl

def kid08_part389 : Audit := .split 20 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.cycle 20 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 24 1 false (8),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 23 1 true (5),
.cycle 22 11 true (4),
.cycle 25 3 true (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 18 4 true (3),
.cycle 20 1 false (4),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 22 24 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid08_part389_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part389) = true := by rfl

def kid08_part390 : Audit := .cycle 0 24 true (0)
theorem kid08_part390_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part390) = true := by rfl

def kid08_part391 : Audit := .split 22 (5,false) (byMove [
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 32 1 false (6),
.cycle 40 1 false (10),
.cycle 19 8 true (2),
.cycle 18 6 false (4),
.cycle 0 57 true (0),
.cycle 7 16 true (0),
.cycle 41 14 true (6),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 27 1 true (5),
.cycle 24 11 true (4),
.cycle 28 3 true (4),
.cycle 0 63 true (0),
.cycle 29 1 false (5),
.cycle 16 8 true (2),
.cycle 18 6 false (4),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 2, 8, 64],[8, 8, 10, 8, 64, 16, 64],64⟩,
.cycle 0 24 true (0),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid08_part391_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part391) = true := by rfl

def kid08_part392 : Audit := .split 32 (5,false) (byMove [
.cycle 0 33 true (0),
.cycle 41 1 false (11),
.cycle 34 1 false (8),
.cycle 33 1 false (7),
.cycle 0 36 true (0),
.cycle 32 1 false (8),
.cycle 0 33 true (0),
.cycle 41 1 false (13),
.cycle 34 1 false (10),
.cycle 33 1 false (9),
.cycle 0 36 true (0),
.cycle 32 1 true (8),
.cycle 22 11 true (4),
.cycle 31 3 true (7),
.cycle 0 35 true (0),
.cycle 33 1 false (7),
.cycle 45 1 false (13),
.cycle 32 1 false (8),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 40 1 false (12),
.cycle 44 1 false (14),
.cycle 0 39 true (0),
.cycle 32 1 true (8)
])
theorem kid08_part392_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part392) = true := by rfl

def kid08_part393 : Audit := .cycle 20 1 false (2)
theorem kid08_part393_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part393) = true := by rfl

def kid08_part394 : Audit := .cycle 19 1 false (3)
theorem kid08_part394_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part394) = true := by rfl

def kid08_part395 : Audit := .split 20 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 0 81 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (8),
.cycle 33 1 false (9),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 26 11 true (4),
.cycle 18 7 false (4),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 20 36 true (2),
.cycle 65 39 true (7),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid08_part395_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part395) = true := by rfl

def kid08_part396 : Audit := .split 30 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 16 38 true (2),
.cycle 8 23 true (0),
.cycle 0 41 true (0),
.cycle 0 32 true (0),
.cycle 0 37 true (0),
.cycle 0 31 true (0),
.cycle 0 65 true (0),
.cycle 0 50 true (0),
.cycle 0 57 true (0),
.cycle 0 32 true (0),
.cycle 30 1 true (8),
.cycle 20 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 10 21 true (0),
.cycle 28 26 true (6),
.last 49 (4,true),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 0 87 true (0),
.cycle 16 49 true (2),
.cycle 0 32 true (0),
.cycle 30 1 true (8)
])
theorem kid08_part396_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part396) = true := by rfl

def kid08_part397 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.cycle 1 23 true (0),
.last 25 (4,true),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.cycle 1 33 true (0),
.cycle 1 46 true (0),
.cycle 1 23 true (0),
.cycle 22 1 true (6),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 4 19 true (0),
.cycle 21 11 true (5),
.last 25 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 1 45 true (0),
.cycle 1 55 true (0),
.cycle 1 23 true (0),
.cycle 22 1 true (6)
])
theorem kid08_part397_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part397) = true := by rfl

def kid08_part398 : Audit := .cycle 0 22 true (0)
theorem kid08_part398_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part398) = true := by rfl

def kid08_part399 : Audit := .cycle 25 1 false (7)
theorem kid08_part399_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part399) = true := by rfl

def kid08_part400 : Audit := .split 21 (4,true) (byMove [
.last 48 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 24 1 true (2),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 55 1 true (11),
.last 30 (5,false),
.cycle 3 19 true (0),
.cycle 22 1 true (6),
.last 22 (5,false),
.cycle 34 1 true (6),
.last 24 (5,false),
.cycle 24 1 true (4),
.last 51 (5,false),
.cycle 22 3 false (4),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 22 1 true (6),
.last 22 (5,false)
])
theorem kid08_part400_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part400) = true := by rfl

def kid08_part401 : Audit := .split 20 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 33 1 false (7),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 0 48 true (0),
.cycle 50 32 true (8),
.cycle 8 15 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 23 1 true (5),
.cycle 21 11 true (3),
.cycle 27 3 true (5),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 45 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid08_part401_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part401) = true := by rfl

def kid08_part377 : Audit := .split 19 (4,false) (byMove [(kid08_part378),(kid08_part379),(kid08_part380),(kid08_part381),(kid08_part382),(kid08_part383),(kid08_part384),(kid08_part385),(kid08_part386),(kid08_part387),(kid08_part388),(kid08_part389),(kid08_part390),(kid08_part391),(kid08_part392),(kid08_part393),(kid08_part394),(kid08_part395),(kid08_part396),(kid08_part397),(kid08_part398),(kid08_part399),(kid08_part400),(kid08_part401)])

theorem kid08_part377_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part377) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part378),(kid08_part379),(kid08_part380),(kid08_part381),(kid08_part382),(kid08_part383),(kid08_part384),(kid08_part385),(kid08_part386),(kid08_part387),(kid08_part388),(kid08_part389),(kid08_part390),(kid08_part391),(kid08_part392),(kid08_part393),(kid08_part394),(kid08_part395),(kid08_part396),(kid08_part397),(kid08_part398),(kid08_part399),(kid08_part400),(kid08_part401)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part378_checked

  · exact kid08_part384_checked

  · exact kid08_part390_checked

  · exact kid08_part396_checked

  · exact kid08_part379_checked

  · exact kid08_part385_checked

  · exact kid08_part391_checked

  · exact kid08_part397_checked

  · exact kid08_part380_checked

  · exact kid08_part386_checked

  · exact kid08_part392_checked

  · exact kid08_part398_checked

  · exact kid08_part381_checked

  · exact kid08_part387_checked

  · exact kid08_part393_checked

  · exact kid08_part399_checked

  · exact kid08_part382_checked

  · exact kid08_part388_checked

  · exact kid08_part394_checked

  · exact kid08_part400_checked

  · exact kid08_part383_checked

  · exact kid08_part389_checked

  · exact kid08_part395_checked

  · exact kid08_part401_checked

def kid08_part402 : Audit := .split 19 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 37 1 false (9),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.cycle 0 32 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 23 (4,true),
.cycle 19 2 true (2),
.cycle 32 12 true (2),
.cycle 19 8 true (1),
.last 31 (4,true),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 37 1 false (9),
.last 60 (4,true),
.last 23 (4,true),
.last 22 (4,true)
]),
.cycle 19 1 false (3),
.cycle 0 31 true (0),
.cycle 17 28 true (3),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.split 20 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.cycle 19 2 true (3),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 25 1 false (9),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (4),
.cycle 22 12 true (4),
.cycle 24 4 true (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 22 (4,true),
.cycle 0 57 true (0),
.cycle 1 31 true (0),
.cycle 17 28 true (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 23 2 true (3)
]),
.cycle 22 1 true (4),
.cycle 0 24 true (0),
.cycle 28 3 true (4),
.cycle 0 35 true (0),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.last 31 (4,true),
.cycle 0 39 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.last 54 (4,true),
.cycle 0 24 true (0),
.cycle 26 3 true (3),
.cycle 0 35 true (0),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 33 5 true (3),
.last 25 (4,true),
.cycle 17 11 true (1),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.last 53 (4,true),
.cycle 0 24 true (0),
.last 27 (4,true),
.cycle 0 35 true (0),
.last 21 (4,true),
.cycle 18 4 false (4)
]),
.cycle 19 1 false (3),
.cycle 0 31 true (0),
.cycle 1 22 true (0),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.split 20 (4,false) (byMove [
.cycle 17 34 true (3),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 0 35 true (0),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 0 49 true (0),
.cycle 32 25 true (6),
.cycle 21 10 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 22 2 true (4),
.cycle 29 1 false (9),
.cycle 24 4 true (4),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 0 57 true (0),
.cycle 1 31 true (0),
.cycle 2 22 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 24 2 true (2)
]),
.cycle 24 1 true (2)
])
theorem kid08_part402_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part402) = true := by rfl

def kid08_part403 : Audit := .cycle 28 1 false (10)
theorem kid08_part403_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part403) = true := by rfl

def kid08_part404 : Audit := .cycle 21 1 false (7)
theorem kid08_part404_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part404) = true := by rfl

def kid08_part405 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 true (5),
.cycle 20 2 true (5),
.cycle 19 12 true (4),
.cycle 19 8 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.cycle 21 1 true (5),
.last 23 (4,true)
]),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 false (7),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 30 1 false (12),
.cycle 23 1 false (9),
.cycle 22 1 false (8),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 22 1 false (6),
.cycle 21 1 false (7),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (11),
.cycle 33 1 false (13),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.split 21 (4,false) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 24 1 false (8),
.cycle 19 5 true (4),
.cycle 36 1 false (10),
.cycle 33 1 false (11),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 45 1 false (13),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 11 true (5)
]),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.split 21 (4,false) (byMove [
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 24 1 false (8),
.cycle 0 22 true (0),
.cycle 44 1 false (14),
.cycle 19 10 true (5),
.cycle 28 1 false (10),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 25 1 false (9),
.cycle 19 4 true (5),
.cycle 25 1 false (9),
.cycle 32 1 false (12),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part405_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part405) = true := by rfl

def kid08_part406 : Audit := .cycle 0 20 true (0)
theorem kid08_part406_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part406) = true := by rfl

def kid08_part408 : Audit := .cycle 0 20 true (0)
theorem kid08_part408_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part408) = true := by rfl

def kid08_part409 : Audit := .cycle 28 1 false (8)
theorem kid08_part409_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part409) = true := by rfl

def kid08_part410 : Audit := .cycle 21 1 false (5)
theorem kid08_part410_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part410) = true := by rfl

def kid08_part411 : Audit := .cycle 20 1 false (4)
theorem kid08_part411_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part411) = true := by rfl

def kid08_part412 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 true (4),
.last 21 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 20 1 true (4),
.last 21 (5,false)
])
theorem kid08_part412_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part412) = true := by rfl

def kid08_part413 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 20 1 true (4),
.cycle 20 11 true (3),
.cycle 20 3 true (3),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.last 21 (4,false),
.cycle 20 1 true (4)
])
theorem kid08_part413_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part413) = true := by rfl

def kid08_part414 : Audit := .cycle 0 20 true (0)
theorem kid08_part414_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part414) = true := by rfl

def kid08_part415 : Audit := .cycle 28 1 false (10)
theorem kid08_part415_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part415) = true := by rfl

def kid08_part416 : Audit := .cycle 21 1 false (7)
theorem kid08_part416_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part416) = true := by rfl

def kid08_part417 : Audit := .cycle 20 1 false (6)
theorem kid08_part417_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part417) = true := by rfl

def kid08_part418 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part418_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part418) = true := by rfl

def kid08_part419 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part419_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part419) = true := by rfl

def kid08_part420 : Audit := .split 30 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.cycle 31 1 false (7),
.last 31 (4,false),
.cycle 30 1 false (8),
.cycle 0 31 true (0),
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 31 1 false (9),
.last 31 (4,false),
.cycle 30 1 true (8),
.cycle 20 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 31 1 false (7),
.last 31 (4,false),
.cycle 30 1 false (8),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 38 1 false (12),
.cycle 42 1 false (14),
.last 31 (4,false),
.cycle 30 1 true (8)
])
theorem kid08_part420_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part420) = true := by rfl

def kid08_part421 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (8),
.cycle 34 1 false (10),
.last 23 (4,false),
.last 25 (4,false),
.cycle 0 23 true (0),
.cycle 17 28 true (3),
.last 33 (4,false),
.cycle 31 1 false (9),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 21 11 true (5),
.cycle 20 3 true (4),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.last 23 (4,false),
.last 29 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.last 45 (4,false),
.last 55 (4,false),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part421_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part421) = true := by rfl

def kid08_part422 : Audit := .cycle 0 22 true (0)
theorem kid08_part422_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part422) = true := by rfl

def kid08_part423 : Audit := .cycle 20 1 false (4)
theorem kid08_part423_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part423) = true := by rfl

def kid08_part424 : Audit := .split 20 (4,false) (byMove [
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 2 true (4),
.last 23 (5,false),
.last 24 (5,false),
.last 27 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 56 true (0),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 3 false (5),
.last 23 (5,false)
])
theorem kid08_part424_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part424) = true := by rfl

def kid08_part425 : Audit := .split 20 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 24 1 false (8),
.cycle 0 22 true (0),
.cycle 19 2 true (4),
.last 22 (4,false),
.cycle 22 11 true (4),
.last 24 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.last 55 (4,false),
.cycle 1 30 true (0),
.last 45 (4,false),
.cycle 0 22 true (0),
.cycle 18 4 true (4),
.last 22 (4,false)
])
theorem kid08_part425_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part425) = true := by rfl

def kid08_part426 : Audit := .cycle 0 20 true (0)
theorem kid08_part426_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part426) = true := by rfl

def kid08_part427 : Audit := .cycle 1 19 true (0)
theorem kid08_part427_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part427) = true := by rfl

def kid08_part428 : Audit := .cycle 27 1 false (9)
theorem kid08_part428_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part428) = true := by rfl

def kid08_part429 : Audit := .cycle 31 1 false (11)
theorem kid08_part429_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part429) = true := by rfl

def kid08_part430 : Audit := .split 20 (4,false) (byMove [
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (5,false),
.cycle 27 1 false (9),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 24 1 false (8),
.last 23 (5,false),
.cycle 0 26 true (0),
.cycle 31 1 false (11),
.cycle 19 3 true (5),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part430_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part430) = true := by rfl

def kid08_part431 : Audit := .split 20 (5,false) (byMove [
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 24 1 false (6),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 22 (4,false),
.cycle 0 21 true (0),
.last 42 (4,false),
.cycle 31 1 false (11),
.cycle 27 1 false (9),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 24 1 false (8),
.cycle 22 3 true (6),
.last 23 (4,false),
.cycle 31 1 false (11),
.last 23 (4,false),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part431_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part431) = true := by rfl

def kid08_part407 : Audit := .split 19 (4,true) (byMove [(kid08_part408),(kid08_part409),(kid08_part410),(kid08_part411),(kid08_part412),(kid08_part413),(kid08_part414),(kid08_part415),(kid08_part416),(kid08_part417),(kid08_part418),(kid08_part419),(kid08_part420),(kid08_part421),(kid08_part422),(kid08_part423),(kid08_part424),(kid08_part425),(kid08_part426),(kid08_part427),(kid08_part428),(kid08_part429),(kid08_part430),(kid08_part431)])

theorem kid08_part407_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part407) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part408),(kid08_part409),(kid08_part410),(kid08_part411),(kid08_part412),(kid08_part413),(kid08_part414),(kid08_part415),(kid08_part416),(kid08_part417),(kid08_part418),(kid08_part419),(kid08_part420),(kid08_part421),(kid08_part422),(kid08_part423),(kid08_part424),(kid08_part425),(kid08_part426),(kid08_part427),(kid08_part428),(kid08_part429),(kid08_part430),(kid08_part431)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part408_checked

  · exact kid08_part414_checked

  · exact kid08_part420_checked

  · exact kid08_part426_checked

  · exact kid08_part409_checked

  · exact kid08_part415_checked

  · exact kid08_part421_checked

  · exact kid08_part427_checked

  · exact kid08_part410_checked

  · exact kid08_part416_checked

  · exact kid08_part422_checked

  · exact kid08_part428_checked

  · exact kid08_part411_checked

  · exact kid08_part417_checked

  · exact kid08_part423_checked

  · exact kid08_part429_checked

  · exact kid08_part412_checked

  · exact kid08_part418_checked

  · exact kid08_part424_checked

  · exact kid08_part430_checked

  · exact kid08_part413_checked

  · exact kid08_part419_checked

  · exact kid08_part425_checked

  · exact kid08_part431_checked

def kid08_part432 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 true (5),
.cycle 20 2 true (5),
.cycle 20 12 true (4),
.cycle 20 8 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.cycle 21 1 true (5),
.last 23 (4,true)
]),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 false (7),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 30 1 false (12),
.cycle 23 1 false (9),
.cycle 22 1 false (8),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 22 1 false (6),
.cycle 21 1 false (7),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (11),
.cycle 33 1 false (13),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.split 21 (4,false) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5),
.cycle 20 5 true (4),
.cycle 19 5 true (4),
.cycle 33 1 false (11),
.cycle 22 1 false (4),
.cycle 21 1 false (5),
.cycle 20 2 false (6),
.cycle 18 24 true (4),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5)
]),
.cycle 20 1 false (6),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.split 21 (4,false) (byMove [
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.cycle 28 1 false (10),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 25 1 false (9),
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.cycle 32 1 false (12),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part432_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part432) = true := by rfl

def kid08_part433 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 16 68 true (2),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 31 1 false (7),
.cycle 35 1 false (9),
.last 25 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 16 29 true (2),
.cycle 47 1 false (11),
.cycle 33 1 false (7),
.cycle 23 1 true (5),
.cycle 22 2 true (5),
.cycle 20 12 true (4),
.cycle 20 8 true (4),
.cycle 0 26 true (0),
.cycle 29 1 false (7),
.last 25 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 16 68 true (2),
.cycle 16 88 true (2),
.cycle 23 1 true (5),
.last 25 (4,true)
]),
.cycle 36 1 false (6),
.cycle 0 23 true (0),
.cycle 16 80 true (2),
.cycle 8 15 true (0),
.cycle 43 1 false (11),
.split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 16 29 true (2),
.cycle 47 1 false (11),
.cycle 33 1 false (7),
.last 27 (4,true),
.cycle 22 2 true (6),
.cycle 0 24 true (0),
.cycle 16 35 true (2),
.cycle 16 56 true (2),
.cycle 9 15 true (0),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 20 12 true (4),
.cycle 21 4 true (5),
.cycle 0 26 true (0),
.cycle 44 1 false (10),
.last 27 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 16 80 true (2),
.cycle 16 100 true (2),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.split 23 (4,false) (byMove [
.cycle 25 5 true (5),
.cycle 0 27 true (0),
.cycle 34 1 false (6),
.cycle 44 1 false (8),
.last 25 (4,true),
.last 25 (4,true),
.cycle 16 84 true (2),
.cycle 7 17 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 20 13 true (4),
.cycle 19 5 true (3),
.cycle 20 15 true (4),
.cycle 16 88 true (2),
.cycle 31 1 false (5),
.last 25 (4,true),
.last 25 (4,true),
.cycle 20 36 true (4),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 6 19 true (0)
]),
.cycle 16 11 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 16 27 true (2),
.cycle 16 37 true (2),
.split 23 (4,false) (byMove [
.cycle 16 84 true (2),
.cycle 7 17 true (0),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 20 13 true (4),
.cycle 0 24 true (0),
.cycle 20 35 true (4),
.cycle 20 10 true (4),
.cycle 16 27 true (2),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 16 60 true (2),
.cycle 20 4 true (4),
.cycle 20 14 true (4),
.cycle 16 37 true (2),
.last 24 (4,true),
.cycle 18 6 true (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 16 32 true (2),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6)
])
theorem kid08_part433_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part433) = true := by rfl

def kid08_part434 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.split 25 (4,false) (byMove [
.cycle 17 30 true (3),
.cycle 45 1 false (9),
.cycle 33 1 false (3),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 29 2 false (5),
.cycle 0 26 true (0),
.cycle 17 29 true (3),
.cycle 17 32 true (3),
.cycle 3 23 true (0),
.cycle 25 1 true (5),
.cycle 24 2 true (5),
.cycle 45 1 false (9),
.cycle 22 8 true (4),
.cycle 20 6 true (4),
.cycle 17 35 true (3),
.last 26 (4,true),
.cycle 18 16 true (3),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 17 36 true (3),
.cycle 25 1 true (5),
.last 27 (4,true)
]),
.cycle 29 1 false (5),
.cycle 0 25 true (0),
.cycle 17 32 true (3),
.cycle 20 13 true (4),
.cycle 17 28 true (3),
.split 25 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 17 29 true (3),
.cycle 17 32 true (3),
.cycle 3 23 true (0),
.last 28 (4,true),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.cycle 17 37 true (3),
.cycle 8 18 true (0),
.cycle 20 13 true (4),
.cycle 25 1 true (7),
.cycle 24 2 true (6),
.cycle 23 12 true (5),
.cycle 22 4 true (4),
.cycle 0 28 true (0),
.cycle 17 28 true (3),
.last 28 (4,true),
.last 27 (4,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 17 32 true (3),
.cycle 17 44 true (3),
.cycle 25 1 true (7),
.cycle 24 2 true (6)
]),
.cycle 24 1 true (6),
.cycle 23 11 true (5),
.cycle 22 3 true (4),
.cycle 0 27 true (0),
.cycle 4 21 true (0),
.split 25 (4,false) (byMove [
.cycle 22 5 true (4),
.cycle 0 29 true (0),
.cycle 33 1 false (3),
.cycle 78 1 false (12),
.last 26 (4,true),
.cycle 29 2 false (5),
.cycle 17 34 true (3),
.cycle 20 15 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 21 5 true (4),
.cycle 27 5 true (5),
.cycle 20 7 true (4),
.cycle 17 9 true (3),
.cycle 5 21 true (0),
.last 26 (4,true),
.cycle 16 11 true (2),
.cycle 17 30 true (3),
.cycle 23 11 true (5),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 23 5 true (5)
]),
.cycle 16 11 true (2),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 17 27 true (3),
.cycle 17 39 true (3),
.split 25 (4,false) (byMove [
.cycle 17 34 true (3),
.cycle 20 15 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 21 5 true (4),
.cycle 0 26 true (0),
.cycle 17 29 true (3),
.cycle 23 10 true (5),
.cycle 17 27 true (3),
.cycle 25 1 true (7),
.cycle 24 2 true (6),
.cycle 6 20 true (0),
.cycle 23 4 true (5),
.cycle 20 6 true (4),
.cycle 17 39 true (3),
.last 26 (4,true),
.cycle 18 8 true (3),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 17 36 true (3),
.cycle 25 1 true (7),
.cycle 24 2 true (6)
]),
.cycle 24 1 true (6)
])
theorem kid08_part434_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part434) = true := by rfl

def kid08_part435 : Audit := .cycle 30 1 false (10)
theorem kid08_part435_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part435) = true := by rfl

def kid08_part436 : Audit := .cycle 19 1 false (3)
theorem kid08_part436_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part436) = true := by rfl

def kid08_part438 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 4, 64],[8, 8, 9, 8, 64, 16, 64],64⟩,
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 8, 9, 8, 64, 16, 64],64⟩,
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 16, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.last 45 (4,true),
.cycle 0 29 true (0),
.cycle 21 40 true (3),
.cycle 26 15 true (4),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 8, 9, 8, 64, 16, 64],64⟩,
.cycle 0 30 true (0),
.cycle 28 1 true (6),
.cycle 27 11 true (5),
.cycle 26 3 true (4),
.cycle 0 31 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 8, 9, 8, 64, 16, 64],64⟩,
.cycle 24 5 true (3),
.cycle 33 17 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 21 33 true (3),
.cycle 21 49 true (3),
.cycle 21 42 true (3),
.cycle 28 1 true (6)
])
theorem kid08_part438_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part438) = true := by rfl

def kid08_part439 : Audit := .cycle 0 57 true (0)
theorem kid08_part439_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part439) = true := by rfl

def kid08_part440 : Audit := .cycle 21 1 false (3)
theorem kid08_part440_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part440) = true := by rfl

def kid08_part441 : Audit := .cycle 20 1 false (2)
theorem kid08_part441_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part441) = true := by rfl

def kid08_part442 : Audit := .cycle 19 1 false (3)
theorem kid08_part442_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part442) = true := by rfl

def kid08_part443 : Audit := .split 20 (5,false) (byMove [
.cycle 0 63 true (0),
.cycle 49 1 false (9),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 7 24 true (0),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (2),
.cycle 18 4 true (2),
.cycle 14 39 true (0),
.last 29 (4,true),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.last 26 (4,true),
.cycle 0 57 true (0),
.cycle 38 1 false (12),
.cycle 18 4 false (4),
.last 23 (4,true)
])
theorem kid08_part443_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part443) = true := by rfl

def kid08_part444 : Audit := .cycle 23 1 false (7)
theorem kid08_part444_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part444) = true := by rfl

def kid08_part445 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 32 1 false (10),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 32 1 false (12),
.cycle 22 1 true (6),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 26 1 false (8),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.cycle 50 1 false (14),
.cycle 22 1 true (6)
])
theorem kid08_part445_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part445) = true := by rfl

def kid08_part446 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 33 1 false (9),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 27 1 false (7),
.cycle 24 1 false (6),
.cycle 0 25 true (0),
.cycle 33 1 false (11),
.cycle 26 1 false (8),
.cycle 25 1 false (7),
.cycle 27 1 false (9),
.cycle 24 1 true (6),
.cycle 23 11 true (5),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.cycle 22 3 true (4),
.cycle 24 1 false (6),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 32 1 false (10),
.cycle 36 1 false (12),
.cycle 23 10 true (5),
.cycle 24 1 true (6)
])
theorem kid08_part446_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part446) = true := by rfl

def kid08_part447 : Audit := .cycle 30 1 false (10)
theorem kid08_part447_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part447) = true := by rfl

def kid08_part448 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 24 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.cycle 20 2 true (4)
])
theorem kid08_part448_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part448) = true := by rfl

def kid08_part449 : Audit := .cycle 18 2 true (3)
theorem kid08_part449_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part449) = true := by rfl

def kid08_part450 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 16 34 true (2),
.cycle 8 30 true (0),
.cycle 3 26 true (0),
.cycle 26 12 true (4),
.last 32 (4,true),
.cycle 0 29 true (0),
.cycle 16 46 true (2),
.cycle 8 21 true (0),
.cycle 21 14 true (3),
.cycle 26 12 true (4),
.cycle 28 1 true (6),
.cycle 26 11 true (4),
.cycle 27 3 true (5),
.cycle 0 31 true (0),
.cycle 10 26 true (0),
.cycle 24 5 true (3),
.last 32 (4,true),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 16 39 true (2),
.cycle 16 55 true (2),
.cycle 16 30 true (2),
.cycle 28 1 true (6)
])
theorem kid08_part450_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part450) = true := by rfl

def kid08_part451 : Audit := .cycle 16 8 true (2)
theorem kid08_part451_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part451) = true := by rfl

def kid08_part452 : Audit := .cycle 25 1 false (7)
theorem kid08_part452_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part452) = true := by rfl

def kid08_part453 : Audit := .cycle 20 1 false (2)
theorem kid08_part453_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part453) = true := by rfl

def kid08_part454 : Audit := .cycle 19 1 false (3)
theorem kid08_part454_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part454) = true := by rfl

def kid08_part455 : Audit := .split 20 (5,false) (byMove [
.last 27 (4,true),
.cycle 33 40 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 37 1 false (11),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 15 12 true (1),
.cycle 18 7 false (4),
.cycle 0 29 true (0),
.cycle 21 1 false (1),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.cycle 18 6 false (4),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid08_part455_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part455) = true := by rfl

def kid08_part456 : Audit := .split 57 (5,false) (byMove [
.cycle 0 58 true (0),
.cycle 28 51 true (4),
.cycle 22 36 true (3),
.cycle 66 1 false (12),
.cycle 0 59 true (0),
.cycle 31 30 true (6),
.cycle 0 58 true (0),
.cycle 49 32 true (7),
.cycle 41 17 true (6),
.cycle 9 49 true (0),
.cycle 0 59 true (0),
.cycle 57 1 true (13),
.cycle 54 11 true (10),
.cycle 56 3 true (12),
.cycle 0 60 true (0),
.cycle 24 34 true (3),
.cycle 32 26 true (6),
.cycle 15 48 true (1),
.cycle 0 58 true (0),
.cycle 1 57 true (0),
.cycle 15 64 true (1),
.cycle 28 62 true (4),
.cycle 0 59 true (0),
.cycle 57 1 true (13)
])
theorem kid08_part456_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part456) = true := by rfl

def kid08_part457 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 16 68 true (2),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.cycle 1 23 true (0),
.cycle 36 1 false (6),
.cycle 0 23 true (0),
.cycle 16 80 true (2),
.cycle 8 15 true (0),
.cycle 43 1 false (11),
.cycle 1 23 true (0),
.cycle 22 1 true (6),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.cycle 20 11 true (4),
.cycle 16 11 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 16 27 true (2),
.cycle 16 37 true (2),
.cycle 1 23 true (0),
.cycle 22 1 true (6)
])
theorem kid08_part457_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part457) = true := by rfl

def kid08_part458 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.cycle 2 24 true (0),
.last 27 (4,true),
.cycle 0 25 true (0),
.cycle 17 32 true (3),
.cycle 20 13 true (4),
.cycle 17 28 true (3),
.cycle 17 32 true (3),
.cycle 24 1 true (6),
.cycle 23 11 true (5),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 4 21 true (0),
.cycle 22 3 true (4),
.last 27 (4,true),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 17 27 true (3),
.cycle 17 39 true (3),
.cycle 2 24 true (0),
.cycle 24 1 true (6)
])
theorem kid08_part458_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part458) = true := by rfl

def kid08_part459 : Audit := .split 47 (5,false) (byMove [
.cycle 0 48 true (0),
.cycle 0 77 true (0),
.cycle 8 40 true (0),
.cycle 0 59 true (0),
.cycle 5 77 true (0),
.cycle 0 55 true (0),
.cycle 0 48 true (0),
.cycle 5 73 true (0),
.cycle 29 19 true (3),
.cycle 5 55 true (0),
.cycle 0 91 true (0),
.cycle 47 1 true (11),
.cycle 43 11 true (7),
.cycle 46 3 true (10),
.cycle 0 50 true (0),
.cycle 10 38 true (0),
.cycle 0 50 true (0),
.cycle 14 40 true (0),
.cycle 0 48 true (0),
.cycle 1 47 true (0),
.cycle 14 56 true (0),
.cycle 37 39 true (3),
.cycle 20 30 true (3),
.cycle 47 1 true (11)
])
theorem kid08_part459_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part459) = true := by rfl

def kid08_part460 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,false),
.cycle 0 24 true (0),
.last 22 (5,false),
.last 32 (5,false),
.cycle 29 1 true (1),
.cycle 18 3 false (4),
.last 47 (5,false),
.last 57 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 24 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 19 3 false (4),
.cycle 18 3 false (4),
.cycle 0 57 true (0),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.cycle 20 2 true (4)
])
theorem kid08_part460_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part460) = true := by rfl

def kid08_part461 : Audit := .split 21 (4,true) (byMove [
.last 32 (5,false),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 25 1 false (7),
.last 24 (5,false),
.last 28 (5,false),
.cycle 32 1 false (10),
.last 25 (5,false),
.cycle 18 4 true (3),
.last 32 (5,false),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 19 3 false (4),
.last 22 (5,false),
.last 63 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.last 51 (5,false),
.last 25 (5,false),
.cycle 20 2 true (3)
])
theorem kid08_part461_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part461) = true := by rfl

def kid08_part437 : Audit := .split 19 (4,false) (byMove [(kid08_part438),(kid08_part439),(kid08_part440),(kid08_part441),(kid08_part442),(kid08_part443),(kid08_part444),(kid08_part445),(kid08_part446),(kid08_part447),(kid08_part448),(kid08_part449),(kid08_part450),(kid08_part451),(kid08_part452),(kid08_part453),(kid08_part454),(kid08_part455),(kid08_part456),(kid08_part457),(kid08_part458),(kid08_part459),(kid08_part460),(kid08_part461)])

theorem kid08_part437_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part437) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part438),(kid08_part439),(kid08_part440),(kid08_part441),(kid08_part442),(kid08_part443),(kid08_part444),(kid08_part445),(kid08_part446),(kid08_part447),(kid08_part448),(kid08_part449),(kid08_part450),(kid08_part451),(kid08_part452),(kid08_part453),(kid08_part454),(kid08_part455),(kid08_part456),(kid08_part457),(kid08_part458),(kid08_part459),(kid08_part460),(kid08_part461)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part438_checked

  · exact kid08_part444_checked

  · exact kid08_part450_checked

  · exact kid08_part456_checked

  · exact kid08_part439_checked

  · exact kid08_part445_checked

  · exact kid08_part451_checked

  · exact kid08_part457_checked

  · exact kid08_part440_checked

  · exact kid08_part446_checked

  · exact kid08_part452_checked

  · exact kid08_part458_checked

  · exact kid08_part441_checked

  · exact kid08_part447_checked

  · exact kid08_part453_checked

  · exact kid08_part459_checked

  · exact kid08_part442_checked

  · exact kid08_part448_checked

  · exact kid08_part454_checked

  · exact kid08_part460_checked

  · exact kid08_part443_checked

  · exact kid08_part449_checked

  · exact kid08_part455_checked

  · exact kid08_part461_checked

def kid08_part462 : Audit := .split 19 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.cycle 0 63 true (0),
.cycle 50 1 false (8),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 22 (4,true),
.cycle 19 2 true (2),
.cycle 14 39 true (0),
.cycle 19 8 true (1),
.cycle 0 30 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 0 57 true (0),
.cycle 39 1 false (11),
.last 22 (4,true),
.last 22 (4,true)
]),
.cycle 19 1 false (3),
.cycle 23 1 false (7),
.cycle 31 1 false (11),
.cycle 26 1 false (8),
.cycle 30 1 false (10),
.split 20 (4,true) (byMove [
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 22 (4,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 25 (4,false),
.last 25 (4,false),
.last 29 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.cycle 18 4 true (3)
]),
.cycle 18 2 true (3),
.cycle 26 11 true (4),
.cycle 16 8 true (2),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.last 26 (4,true),
.cycle 0 51 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 35 1 false (11),
.cycle 32 1 false (8),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 18 3 false (4),
.cycle 15 12 true (1),
.last 25 (4,true),
.cycle 39 1 false (11),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 19 2 false (3),
.cycle 48 14 true (8),
.cycle 26 11 true (4),
.last 24 (4,true),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 18 4 false (4)
]),
.cycle 19 1 false (3),
.cycle 0 58 true (0),
.cycle 1 22 true (0),
.cycle 17 27 true (3),
.cycle 37 39 true (3),
.split 20 (4,true) (byMove [
.last 25 (4,false),
.cycle 0 24 true (0),
.last 26 (4,false),
.last 33 (4,false),
.last 22 (4,false),
.cycle 18 3 false (4),
.last 48 (4,false),
.last 58 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 25 (4,false),
.last 25 (4,false),
.last 29 (4,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 22 (4,false),
.cycle 18 3 false (4),
.cycle 0 57 true (0),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.cycle 18 5 false (5)
]),
.cycle 18 3 false (4)
])
theorem kid08_part462_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part462) = true := by rfl

def kid08_part463 : Audit := .cycle 0 51 true (0)
theorem kid08_part463_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part463) = true := by rfl

def kid08_part464 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.split 29 (4,false) (byMove [
.cycle 0 30 true (0),
.cycle 38 1 false (10),
.cycle 31 1 false (7),
.cycle 30 1 false (6),
.cycle 29 1 false (7),
.cycle 28 2 false (8),
.cycle 0 30 true (0),
.cycle 38 1 false (12),
.cycle 31 1 false (9),
.cycle 30 1 false (8),
.cycle 29 1 true (7),
.cycle 28 2 true (7),
.cycle 19 12 true (4),
.cycle 26 8 true (6),
.cycle 0 32 true (0),
.cycle 30 1 false (6),
.cycle 29 1 false (7),
.cycle 28 2 false (8),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 37 1 false (11),
.cycle 41 1 false (13),
.cycle 29 1 true (7),
.last 31 (4,true)
]),
.cycle 28 1 false (8),
.cycle 0 29 true (0),
.cycle 37 1 false (13),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.split 29 (4,false) (byMove [
.cycle 0 30 true (0),
.cycle 38 1 false (12),
.cycle 31 1 false (9),
.cycle 30 1 false (8),
.cycle 29 1 false (9),
.cycle 28 2 true (8),
.cycle 0 30 true (0),
.cycle 38 1 false (14),
.cycle 31 1 false (11),
.cycle 30 1 false (10),
.cycle 29 1 true (9),
.cycle 28 2 true (8),
.cycle 19 12 true (4),
.cycle 27 4 true (7),
.cycle 0 32 true (0),
.cycle 30 1 false (8),
.cycle 29 1 false (9),
.last 31 (4,true),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 37 1 false (13),
.cycle 41 1 false (15),
.cycle 29 1 true (9),
.cycle 28 2 true (8)
]),
.cycle 28 1 true (8),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 29 1 false (7),
.split 29 (4,false) (byMove [
.cycle 31 5 true (7),
.cycle 0 33 true (0),
.cycle 31 1 false (7),
.cycle 30 1 false (6),
.cycle 29 1 false (7),
.cycle 28 2 false (8),
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.last 30 (4,true),
.cycle 1 30 true (0),
.cycle 26 5 true (6),
.cycle 1 32 true (0),
.cycle 41 1 false (13),
.cycle 30 1 false (6),
.cycle 29 1 false (7),
.cycle 28 2 false (8),
.cycle 26 24 true (6),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.last 30 (4,true),
.cycle 1 30 true (0)
]),
.cycle 28 1 false (8),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (12),
.cycle 40 1 false (14),
.split 29 (4,false) (byMove [
.cycle 39 1 false (13),
.cycle 32 1 false (10),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.last 30 (4,true),
.cycle 1 30 true (0),
.cycle 0 30 true (0),
.cycle 26 23 true (6),
.cycle 20 10 true (4),
.cycle 36 1 false (12),
.cycle 29 1 true (9),
.cycle 28 2 true (8),
.cycle 33 1 false (11),
.cycle 26 4 true (6),
.cycle 1 31 true (0),
.cycle 40 1 false (14),
.last 30 (4,true),
.cycle 18 12 true (4),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 1 55 true (0),
.cycle 29 1 true (9),
.cycle 28 2 true (8)
]),
.cycle 28 1 true (8)
])
theorem kid08_part464_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part464) = true := by rfl

def kid08_part465 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.split 21 (4,false) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.cycle 23 20 true (4),
.cycle 33 1 false (9),
.cycle 28 1 false (8),
.cycle 21 1 true (5),
.cycle 20 2 true (5),
.cycle 25 1 false (7),
.cycle 19 8 true (4),
.cycle 31 1 false (9),
.cycle 32 1 false (10),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 21 1 true (5),
.last 23 (4,true)
]),
.cycle 30 1 false (8),
.cycle 0 21 true (0),
.cycle 17 24 true (3),
.cycle 38 1 false (12),
.cycle 29 1 false (9),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 23 20 true (4),
.cycle 33 1 false (9),
.cycle 28 1 false (8),
.last 24 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 43 20 true (9),
.cycle 8 14 true (0),
.cycle 38 1 false (12),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 30 1 false (8),
.last 24 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 24 true (3),
.cycle 17 32 true (3),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.split 21 (4,false) (byMove [
.cycle 19 5 true (4),
.cycle 0 25 true (0),
.cycle 26 1 false (4),
.cycle 35 1 false (7),
.last 22 (4,true),
.cycle 0 25 true (0),
.cycle 17 26 true (3),
.cycle 40 1 false (12),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 22 20 true (4),
.cycle 23 5 true (5),
.cycle 32 1 false (10),
.cycle 17 5 true (3),
.cycle 26 1 false (8),
.last 22 (4,true),
.cycle 22 20 true (4),
.cycle 24 20 true (5),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 2 21 true (0)
]),
.cycle 22 20 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 21 20 true (4),
.cycle 45 20 true (9),
.split 21 (4,false) (byMove [
.cycle 17 26 true (3),
.cycle 40 1 false (12),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 22 20 true (4),
.cycle 0 22 true (0),
.cycle 23 20 true (6),
.cycle 19 10 true (5),
.cycle 22 20 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 6 16 true (0),
.cycle 19 4 true (5),
.cycle 17 26 true (3),
.cycle 45 20 true (9),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part465_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part465) = true := by rfl

def kid08_part466 : Audit := .cycle 0 20 true (0)
theorem kid08_part466_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part466) = true := by rfl

def kid08_part468 : Audit := .cycle 29 1 false (9)
theorem kid08_part468_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part468) = true := by rfl

def kid08_part469 : Audit := .cycle 22 1 false (6)
theorem kid08_part469_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part469) = true := by rfl

def kid08_part470 : Audit := .split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.last 22 (4,false),
.cycle 21 1 true (5),
.cycle 20 11 true (4),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.last 22 (4,false),
.cycle 21 1 true (5)
])
theorem kid08_part470_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part470) = true := by rfl

def kid08_part471 : Audit := .cycle 0 21 true (0)
theorem kid08_part471_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part471) = true := by rfl

def kid08_part472 : Audit := .split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 true (3),
.last 22 (5,false),
.last 32 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.cycle 21 1 true (3),
.last 22 (5,false)
])
theorem kid08_part472_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part472) = true := by rfl

def kid08_part473 : Audit := .split 21 (4,false) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.last 23 (5,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 20 34 true (4),
.last 30 (5,false),
.cycle 28 1 false (8),
.cycle 21 1 true (5),
.last 22 (5,false),
.cycle 25 1 false (7),
.last 24 (5,false),
.cycle 20 3 true (4),
.cycle 32 1 false (10),
.last 23 (5,false),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 21 1 true (5),
.last 22 (5,false)
])
theorem kid08_part473_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part473) = true := by rfl

def kid08_part474 : Audit := .cycle 0 20 true (0)
theorem kid08_part474_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part474) = true := by rfl

def kid08_part475 : Audit := .split 51 (4,false) (byMove [
.cycle 61 1 false (17),
.cycle 54 1 false (14),
.last 53 (5,false),
.cycle 0 53 true (0),
.cycle 61 1 false (17),
.cycle 50 2 true (12),
.cycle 0 52 true (0),
.cycle 20 32 true (4),
.last 60 (5,false),
.cycle 58 1 false (16),
.cycle 51 1 true (13),
.last 52 (5,false),
.cycle 55 1 false (15),
.last 54 (5,false),
.cycle 49 3 true (11),
.cycle 62 1 false (18),
.cycle 55 1 false (15),
.cycle 18 34 true (4),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.last 78 (5,false),
.cycle 51 1 true (13),
.last 52 (5,false)
])
theorem kid08_part475_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part475) = true := by rfl

def kid08_part476 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.last 29 (4,false),
.cycle 28 1 false (8),
.cycle 0 29 true (0),
.cycle 37 1 false (13),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.last 29 (4,false),
.cycle 28 1 true (8),
.cycle 20 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 29 1 false (7),
.last 29 (4,false),
.cycle 28 1 false (8),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (12),
.cycle 40 1 false (14),
.last 29 (4,false),
.cycle 28 1 true (8)
])
theorem kid08_part476_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part476) = true := by rfl

def kid08_part477 : Audit := .cycle 26 1 false (8)
theorem kid08_part477_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part477) = true := by rfl

def kid08_part478 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 23 1 false (5),
.last 21 (5,false),
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4260880, 2, 16777216, 128, 256, 32768, 524290, 8192, 16777216, 128, 256, 2097152, 4, 524288, 16777216, 128, 256, 8, 32, 2, 16777216, 16777216],[2, 4, 32, 1, 16, 1024, 8192, 16384, 131072, 4096, 65536, 1024, 524288, 1048576, 8388608, 262144, 4194304, 1024, 2, 4, 32, 1, 16, 1024, 16777216],27412512⟩,
.last 40 (5,false),
.last 28 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.cycle 25 1 false (7),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4260880, 256, 16777216, 128, 256, 32768, 524290, 256, 16777216, 128, 256, 2097152, 4, 256, 16777216, 128, 256, 8, 32, 256, 16777216, 16777216],[2, 4, 32, 1, 16, 1024, 8192, 16384, 131072, 4096, 65536, 1024, 524288, 1048576, 8388608, 262144, 4194304, 1024, 2, 4, 32, 1, 16, 1024, 16777216],27412512⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4260880, 512, 16777216, 128, 256, 32768, 524290, 512, 16777216, 128, 256, 2097152, 4, 512, 16777216, 128, 256, 8, 32, 512, 16777216, 16777216],[2, 4, 32, 1, 16, 1024, 8192, 16384, 131072, 4096, 65536, 1024, 524288, 1048576, 8388608, 262144, 4194304, 1024, 2, 4, 32, 1, 16, 1024, 16777216],27412512⟩,
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part478_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part478) = true := by rfl

def kid08_part479 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.last 21 (4,false),
.last 23 (4,false),
.cycle 0 21 true (0),
.cycle 18 24 true (4),
.last 31 (4,false),
.cycle 29 1 false (9),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.last 21 (4,false),
.last 25 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 41 (4,false),
.last 49 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part479_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part479) = true := by rfl

def kid08_part480 : Audit := .cycle 23 1 false (7)
theorem kid08_part480_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part480) = true := by rfl

def kid08_part481 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.last 23 (4,false),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 20 11 true (4),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.last 23 (4,false),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part481_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part481) = true := by rfl

def kid08_part482 : Audit := .split 22 (4,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 17 26 true (3),
.last 31 (5,false),
.cycle 29 1 false (9),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 26 1 false (8),
.last 25 (5,false),
.cycle 20 3 true (4),
.cycle 33 1 false (11),
.cycle 35 1 false (11),
.cycle 18 5 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 33 true (3),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part482_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part482) = true := by rfl

def kid08_part483 : Audit := .cycle 30 1 false (10)
theorem kid08_part483_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part483) = true := by rfl

def kid08_part484 : Audit := .split 21 (4,false) (byMove [
.cycle 23 43 true (3),
.cycle 32 26 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 22 (5,false),
.cycle 25 1 false (7),
.last 24 (5,false),
.last 33 (5,false),
.cycle 32 1 false (10),
.cycle 20 2 true (3),
.cycle 18 4 true (3),
.cycle 16 29 true (2),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 22 (5,false),
.cycle 0 35 true (0),
.last 24 (5,false),
.cycle 2 23 true (0),
.last 51 (5,false),
.cycle 19 3 false (5),
.cycle 19 5 false (5)
])
theorem kid08_part484_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part484) = true := by rfl

def kid08_part485 : Audit := .cycle 18 2 true (4)
theorem kid08_part485_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part485) = true := by rfl

def kid08_part486 : Audit := .cycle 0 20 true (0)
theorem kid08_part486_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part486) = true := by rfl

def kid08_part487 : Audit := .cycle 1 19 true (0)
theorem kid08_part487_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part487) = true := by rfl

def kid08_part488 : Audit := .cycle 2 18 true (0)
theorem kid08_part488_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part488) = true := by rfl

def kid08_part489 : Audit := .cycle 21 23 true (4)
theorem kid08_part489_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part489) = true := by rfl

def kid08_part490 : Audit := .split 20 (4,false) (byMove [
.cycle 19 23 true (4),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 20 2 true (5),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (5,false),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 37 1 false (11),
.last 23 (5,false),
.cycle 20 3 true (5),
.cycle 19 26 true (4),
.cycle 19 3 true (5),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part490_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part490) = true := by rfl

def kid08_part491 : Audit := .split 20 (5,false) (byMove [
.last 43 (4,false),
.cycle 39 1 false (11),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 22 (4,false),
.cycle 0 21 true (0),
.last 42 (4,false),
.cycle 18 26 true (4),
.cycle 3 18 true (0),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 33 (4,false),
.cycle 22 3 true (6),
.last 23 (4,false),
.cycle 18 26 true (4),
.last 23 (4,false),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part491_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part491) = true := by rfl

def kid08_part467 : Audit := .split 19 (4,true) (byMove [(kid08_part468),(kid08_part469),(kid08_part470),(kid08_part471),(kid08_part472),(kid08_part473),(kid08_part474),(kid08_part475),(kid08_part476),(kid08_part477),(kid08_part478),(kid08_part479),(kid08_part480),(kid08_part481),(kid08_part482),(kid08_part483),(kid08_part484),(kid08_part485),(kid08_part486),(kid08_part487),(kid08_part488),(kid08_part489),(kid08_part490),(kid08_part491)])

theorem kid08_part467_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part467) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part468),(kid08_part469),(kid08_part470),(kid08_part471),(kid08_part472),(kid08_part473),(kid08_part474),(kid08_part475),(kid08_part476),(kid08_part477),(kid08_part478),(kid08_part479),(kid08_part480),(kid08_part481),(kid08_part482),(kid08_part483),(kid08_part484),(kid08_part485),(kid08_part486),(kid08_part487),(kid08_part488),(kid08_part489),(kid08_part490),(kid08_part491)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part468_checked

  · exact kid08_part474_checked

  · exact kid08_part480_checked

  · exact kid08_part486_checked

  · exact kid08_part469_checked

  · exact kid08_part475_checked

  · exact kid08_part481_checked

  · exact kid08_part487_checked

  · exact kid08_part470_checked

  · exact kid08_part476_checked

  · exact kid08_part482_checked

  · exact kid08_part488_checked

  · exact kid08_part471_checked

  · exact kid08_part477_checked

  · exact kid08_part483_checked

  · exact kid08_part489_checked

  · exact kid08_part472_checked

  · exact kid08_part478_checked

  · exact kid08_part484_checked

  · exact kid08_part490_checked

  · exact kid08_part473_checked

  · exact kid08_part479_checked

  · exact kid08_part485_checked

  · exact kid08_part491_checked

def kid08_part492 : Audit := .split 20 (5,false) (byMove [
.cycle 18 23 true (4),
.cycle 39 1 false (11),
.cycle 30 1 false (8),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 26 (4,false),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.last 31 (4,false),
.cycle 28 1 false (8),
.last 22 (4,false),
.last 23 (4,false),
.cycle 25 1 false (7),
.last 25 (4,false),
.cycle 0 28 true (0),
.cycle 32 1 false (10),
.last 23 (4,false),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.last 22 (4,false),
.cycle 20 2 true (5)
]),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 18 22 true (4),
.cycle 18 26 true (4),
.cycle 3 18 true (0),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.last 23 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 18 25 true (4),
.cycle 19 12 true (5),
.cycle 18 26 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 18 22 true (4),
.cycle 18 30 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 37 1 false (11),
.cycle 22 3 true (6),
.cycle 19 3 true (5),
.cycle 18 26 true (4),
.split 21 (4,true) (byMove [
.last 26 (4,false),
.cycle 0 25 true (0),
.last 24 (4,false),
.last 34 (4,false),
.last 23 (4,false),
.last 26 (4,false),
.cycle 18 26 true (4),
.cycle 37 1 false (11),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 19 3 true (5),
.last 26 (4,false),
.cycle 23 5 true (5),
.cycle 17 5 true (3),
.cycle 26 1 false (8),
.last 23 (4,false),
.cycle 18 5 true (4),
.cycle 18 24 true (4),
.last 32 (4,false),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 19 3 true (5)
]),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.split 21 (4,false) (byMove [
.cycle 18 24 true (4),
.cycle 18 30 true (4),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.cycle 3 19 true (0),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 14 true (5),
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.cycle 18 27 true (4),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part492_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part492) = true := by rfl

def kid08_part372 : Audit := .split 18 (5,true) (byMove [(kid08_part373),(kid08_part374),(kid08_part375),(kid08_part376),(kid08_part377),(kid08_part402),(kid08_part403),(kid08_part404),(kid08_part405),(kid08_part406),(kid08_part407),(kid08_part432),(kid08_part433),(kid08_part434),(kid08_part435),(kid08_part436),(kid08_part437),(kid08_part462),(kid08_part463),(kid08_part464),(kid08_part465),(kid08_part466),(kid08_part467),(kid08_part492)])

theorem kid08_part372_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (kid08_part372) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part373),(kid08_part374),(kid08_part375),(kid08_part376),(kid08_part377),(kid08_part402),(kid08_part403),(kid08_part404),(kid08_part405),(kid08_part406),(kid08_part407),(kid08_part432),(kid08_part433),(kid08_part434),(kid08_part435),(kid08_part436),(kid08_part437),(kid08_part462),(kid08_part463),(kid08_part464),(kid08_part465),(kid08_part466),(kid08_part467),(kid08_part492)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part373_checked

  · exact kid08_part403_checked

  · exact kid08_part433_checked

  · exact kid08_part463_checked

  · exact kid08_part374_checked

  · exact kid08_part404_checked

  · exact kid08_part434_checked

  · exact kid08_part464_checked

  · exact kid08_part375_checked

  · exact kid08_part405_checked

  · exact kid08_part435_checked

  · exact kid08_part465_checked

  · exact kid08_part376_checked

  · exact kid08_part406_checked

  · exact kid08_part436_checked

  · exact kid08_part466_checked

  · exact kid08_part377_checked

  · exact kid08_part407_checked

  · exact kid08_part437_checked

  · exact kid08_part467_checked

  · exact kid08_part402_checked

  · exact kid08_part432_checked

  · exact kid08_part462_checked

  · exact kid08_part492_checked

def kid08_part493 : Audit := .cycle 22 10 true (4)
theorem kid08_part493_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,0⟩)) (kid08_part493) = true := by rfl

def kid08_part494 : Audit := .cycle 16 4 true (2)
theorem kid08_part494_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,1⟩)) (kid08_part494) = true := by rfl

def kid08_part495 : Audit := .cycle 23 1 false (7)
theorem kid08_part495_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,2⟩)) (kid08_part495) = true := by rfl

def kid08_part496 : Audit := .cycle 18 1 false (2)
theorem kid08_part496_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,3⟩)) (kid08_part496) = true := by rfl

def kid08_part498 : Audit := .split 22 (4,true) (byMove [
.cycle 19 8 true (1),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.cycle 32 1 false (2),
.cycle 12 32 true (-1),
.split 23 (5,true) (byMove [
.cycle 0 64 true (0),
.cycle 12 14 true (0),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 12 32 true (-1),
.last 24 (5,false),
.last 32 (5,false),
.last 27 (5,false),
.cycle 29 1 false (7),
.cycle 24 1 false (2),
.cycle 18 6 true (1),
.last 24 (5,false),
.cycle 0 123 true (0),
.last 27 (5,false),
.last 34 (5,false),
.cycle 24 1 false (0),
.cycle 18 6 false (3),
.last 24 (5,false),
.last 32 (5,false),
.cycle 20 4 true (1),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.last 29 (5,false),
.last 24 (5,false)
]),
.cycle 15 41 true (1),
.cycle 23 22 true (2),
.cycle 17 12 true (1),
.cycle 0 52 true (0),
.cycle 0 27 true (0),
.split 23 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 31 1 false (3),
.cycle 0 75 true (0),
.last 24 (5,false),
.cycle 0 52 true (0),
.cycle 16 41 true (1),
.cycle 24 22 true (2),
.cycle 14 39 true (0),
.cycle 0 27 true (0),
.last 26 (5,false),
.cycle 38 16 true (4),
.cycle 20 4 true (2),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.cycle 18 12 true (1),
.last 24 (5,false),
.cycle 0 75 true (0),
.cycle 1 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 64, 64],[2, 4, 4, 1, 32, 4, 64],96⟩,
.cycle 0 101 true (0),
.cycle 22 31 true (2),
.last 26 (5,false)
]),
.cycle 15 8 true (1),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.cycle 18 6 false (3),
.split 23 (5,true) (byMove [
.cycle 19 5 false (3),
.cycle 68 34 true (4),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 86 38 true (4),
.last 24 (5,false),
.cycle 45 1 false (7),
.cycle 16 8 true (1),
.cycle 17 7 false (3),
.cycle 44 1 false (10),
.last 25 (5,false),
.last 28 (5,false),
.last 32 (5,false),
.last 27 (5,false),
.cycle 51 1 false (7),
.cycle 24 1 false (0),
.cycle 18 6 false (3),
.last 24 (5,false),
.cycle 24 26 true (2),
.last 31 (5,false),
.last 26 (5,false),
.cycle 14 47 true (0),
.cycle 22 2 true (1),
.last 28 (5,false)
]),
.cycle 55 16 true (7),
.cycle 34 14 true (4),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.cycle 22 29 true (2),
.split 23 (5,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 64, 64],[2, 4, 4, 1, 32, 4, 64],96⟩,
.cycle 14 43 true (0),
.cycle 17 10 false (3),
.cycle 0 35 true (0),
.last 25 (5,false),
.last 26 (5,false),
.cycle 6 18 true (0),
.cycle 56 16 true (7),
.cycle 34 14 true (4),
.cycle 0 63 true (0),
.cycle 0 27 true (0),
.last 26 (5,false),
.cycle 24 26 true (2),
.cycle 16 16 true (1),
.cycle 17 10 false (3),
.cycle 14 47 true (0),
.cycle 22 2 true (2),
.last 26 (5,false),
.cycle 0 75 true (0),
.cycle 1 31 true (0),
.cycle 2 28 true (0),
.cycle 24 38 true (3),
.last 55 (5,false),
.last 26 (5,false)
])
])
theorem kid08_part498_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part498) = true := by rfl

def kid08_part499 : Audit := .cycle 0 46 true (0)
theorem kid08_part499_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part499) = true := by rfl

def kid08_part500 : Audit := .cycle 20 1 false (2)
theorem kid08_part500_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part500) = true := by rfl

def kid08_part501 : Audit := .cycle 19 1 false (1)
theorem kid08_part501_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part501) = true := by rfl

def kid08_part502 : Audit := .cycle 18 1 false (2)
theorem kid08_part502_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part502) = true := by rfl

def kid08_part504 : Audit := .cycle 0 52 true (0)
theorem kid08_part504_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part504) = true := by rfl

def kid08_part505 : Audit := .cycle 12 10 true (0)
theorem kid08_part505_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part505) = true := by rfl

def kid08_part506 : Audit := .cycle 21 1 false (1)
theorem kid08_part506_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part506) = true := by rfl

def kid08_part507 : Audit := .cycle 20 1 false (0)
theorem kid08_part507_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part507) = true := by rfl

def kid08_part508 : Audit := .cycle 18 2 false (2)
theorem kid08_part508_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part508) = true := by rfl

def kid08_part509 : Audit := .cycle 19 1 false (1)
theorem kid08_part509_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part509) = true := by rfl

def kid08_part510 : Audit := .split 24 (5,true) (byMove [
.cycle 0 75 true (0),
.cycle 42 12 true (2),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 0 81 true (0),
.last 29 (4,true),
.cycle 30 12 true (4),
.last 27 (4,true),
.cycle 36 1 false (10),
.cycle 25 1 false (3),
.cycle 32 12 true (3),
.cycle 29 1 false (7),
.cycle 14 47 true (0),
.last 27 (4,true),
.cycle 34 12 true (4),
.cycle 25 1 false (1),
.cycle 14 51 true (0),
.last 29 (4,true),
.cycle 30 12 true (4),
.last 27 (4,true),
.cycle 0 69 true (0),
.cycle 25 12 true (2),
.cycle 23 2 true (2),
.cycle 6 20 true (0)
])
theorem kid08_part510_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part510) = true := by rfl

def kid08_part511 : Audit := .split 22 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 58 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 0 64 true (0),
.cycle 19 4 true (1),
.cycle 40 1 false (10),
.cycle 39 1 false (7),
.cycle 17 6 true (1),
.cycle 27 1 false (7),
.cycle 36 1 false (10),
.last 23 (5,true),
.last 27 (5,true),
.cycle 20 3 false (3),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.cycle 18 5 false (3),
.cycle 16 8 true (1),
.cycle 55 16 true (7),
.last 26 (5,true),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.last 27 (5,true),
.last 23 (5,true)
])
theorem kid08_part511_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part511) = true := by rfl

def kid08_part512 : Audit := .cycle 25 1 false (7)
theorem kid08_part512_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part512) = true := by rfl

def kid08_part513 : Audit := .cycle 20 1 false (2)
theorem kid08_part513_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part513) = true := by rfl

def kid08_part514 : Audit := .cycle 18 2 true (1)
theorem kid08_part514_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part514) = true := by rfl

def kid08_part515 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 33 1 true (3),
.cycle 28 1 true (4),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.last 22 (4,true),
.cycle 24 1 true (6),
.cycle 14 51 true (0),
.last 24 (4,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 18 4 true (1),
.cycle 20 2 true (2),
.cycle 0 67 true (0),
.last 28 (4,true),
.last 23 (4,true),
.cycle 5 87 true (0),
.last 22 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part515_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part515) = true := by rfl

def kid08_part516 : Audit := .cycle 0 99 true (0)
theorem kid08_part516_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part516) = true := by rfl

def kid08_part517 : Audit := .split 22 (4,true) (byMove [
.cycle 20 8 true (-1),
.last 30 (5,true),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 48 1 false (10),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.last 28 (5,true),
.cycle 18 6 true (0),
.last 23 (5,true),
.last 27 (5,true),
.cycle 20 3 false (1),
.cycle 56 1 false (10),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 128 20 true (6),
.cycle 0 111 true (0),
.cycle 21 2 true (0),
.last 28 (5,true),
.last 25 (5,true),
.last 23 (5,true)
])
theorem kid08_part517_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part517) = true := by rfl

def kid08_part518 : Audit := .split 26 (5,true) (byMove [
.cycle 0 81 true (0),
.cycle 46 14 true (2),
.cycle 28 1 false (2),
.cycle 27 1 false (1),
.last 189 (4,true),
.last 33 (4,true),
.cycle 32 14 true (4),
.last 29 (4,true),
.cycle 38 1 false (10),
.cycle 27 1 false (3),
.cycle 36 14 true (2),
.cycle 33 1 false (7),
.cycle 14 51 true (0),
.last 29 (4,true),
.cycle 34 14 true (2),
.cycle 27 1 false (1),
.cycle 14 59 true (-1),
.last 33 (4,true),
.cycle 32 14 true (4),
.last 29 (4,true),
.cycle 0 75 true (0),
.cycle 27 14 true (2),
.cycle 25 2 true (2),
.cycle 17 11 false (4)
])
theorem kid08_part518_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part518) = true := by rfl

def kid08_part519 : Audit := .cycle 20 1 false (0)
theorem kid08_part519_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part519) = true := by rfl

def kid08_part520 : Audit := .cycle 18 2 false (2)
theorem kid08_part520_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part520) = true := by rfl

def kid08_part521 : Audit := .cycle 19 1 false (1)
theorem kid08_part521_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part521) = true := by rfl

def kid08_part522 : Audit := .split 24 (5,true) (byMove [
.cycle 0 75 true (0),
.cycle 27 1 false (3),
.cycle 49 1 false (-1),
.last 29 (4,true),
.last 25 (4,true),
.cycle 0 81 true (0),
.cycle 30 12 true (4),
.last 27 (4,true),
.cycle 14 43 true (0),
.cycle 38 12 true (2),
.cycle 32 12 true (3),
.cycle 72 12 true (10),
.cycle 38 1 false (10),
.cycle 14 55 true (0),
.cycle 17 8 false (4),
.last 29 (4,true),
.last 25 (4,true),
.cycle 0 127 true (0),
.cycle 30 12 true (4),
.last 27 (4,true),
.cycle 0 69 true (0),
.cycle 25 12 true (2),
.cycle 23 2 true (2),
.cycle 72 12 true (10)
])
theorem kid08_part522_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part522) = true := by rfl

def kid08_part523 : Audit := .split 22 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.last 28 (5,true),
.last 41 (5,true),
.last 23 (5,true),
.cycle 15 41 true (1),
.cycle 23 22 true (2),
.last 25 (5,true),
.cycle 0 52 true (0),
.cycle 1 27 true (0),
.last 23 (5,true),
.cycle 15 8 true (1),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.cycle 18 6 false (3),
.last 23 (5,true),
.cycle 55 16 true (7),
.last 26 (5,true),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.last 27 (5,true),
.last 23 (5,true)
])
theorem kid08_part523_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part523) = true := by rfl

def kid08_part524 : Audit := .cycle 0 46 true (0)
theorem kid08_part524_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part524) = true := by rfl

def kid08_part525 : Audit := .cycle 39 1 false (7)
theorem kid08_part525_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part525) = true := by rfl

def kid08_part526 : Audit := .split 21 (5,true) (byMove [
.cycle 0 58 true (0),
.cycle 12 12 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.cycle 19 3 false (2),
.cycle 30 14 true (3),
.last 24 (4,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 18 4 true (1),
.last 23 (4,true),
.cycle 0 111 true (0),
.last 24 (4,true),
.cycle 34 16 true (2),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.last 23 (4,true),
.cycle 30 14 true (3),
.last 24 (4,true),
.cycle 0 52 true (0),
.cycle 45 1 false (7),
.cycle 20 2 true (1),
.last 23 (4,true)
])
theorem kid08_part526_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part526) = true := by rfl

def kid08_part527 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 14 39 true (0),
.last 23 (4,true),
.cycle 0 34 true (0),
.last 22 (4,true),
.cycle 46 1 true (-2),
.cycle 6 16 true (0),
.cycle 50 14 true (7),
.cycle 14 43 true (0),
.cycle 0 57 true (0),
.last 22 (4,true),
.cycle 24 1 true (6),
.cycle 22 22 true (2),
.last 28 (4,true),
.last 23 (4,true),
.cycle 14 41 true (0),
.last 22 (4,true),
.cycle 22 3 false (2),
.cycle 0 67 true (0),
.last 28 (4,true),
.last 23 (4,true),
.cycle 22 34 true (3),
.last 22 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part527_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part527) = true := by rfl

def kid08_part503 : Audit := .split 19 (5,false) (byMove [(kid08_part504),(kid08_part505),(kid08_part506),(kid08_part507),(kid08_part508),(kid08_part509),(kid08_part510),(kid08_part511),(kid08_part512),(kid08_part513),(kid08_part514),(kid08_part515),(kid08_part516),(kid08_part517),(kid08_part518),(kid08_part519),(kid08_part520),(kid08_part521),(kid08_part522),(kid08_part523),(kid08_part524),(kid08_part525),(kid08_part526),(kid08_part527)])

theorem kid08_part503_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part503) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part504),(kid08_part505),(kid08_part506),(kid08_part507),(kid08_part508),(kid08_part509),(kid08_part510),(kid08_part511),(kid08_part512),(kid08_part513),(kid08_part514),(kid08_part515),(kid08_part516),(kid08_part517),(kid08_part518),(kid08_part519),(kid08_part520),(kid08_part521),(kid08_part522),(kid08_part523),(kid08_part524),(kid08_part525),(kid08_part526),(kid08_part527)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part504_checked

  · exact kid08_part510_checked

  · exact kid08_part516_checked

  · exact kid08_part522_checked

  · exact kid08_part505_checked

  · exact kid08_part511_checked

  · exact kid08_part517_checked

  · exact kid08_part523_checked

  · exact kid08_part506_checked

  · exact kid08_part512_checked

  · exact kid08_part518_checked

  · exact kid08_part524_checked

  · exact kid08_part507_checked

  · exact kid08_part513_checked

  · exact kid08_part519_checked

  · exact kid08_part525_checked

  · exact kid08_part508_checked

  · exact kid08_part514_checked

  · exact kid08_part520_checked

  · exact kid08_part526_checked

  · exact kid08_part509_checked

  · exact kid08_part515_checked

  · exact kid08_part521_checked

  · exact kid08_part527_checked

def kid08_part528 : Audit := .cycle 32 1 false (10)
theorem kid08_part528_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part528) = true := by rfl

def kid08_part529 : Audit := .cycle 27 1 false (7)
theorem kid08_part529_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part529) = true := by rfl

def kid08_part530 : Audit := .cycle 17 2 true (2)
theorem kid08_part530_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part530) = true := by rfl

def kid08_part531 : Audit := .cycle 23 1 false (7)
theorem kid08_part531_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part531) = true := by rfl

def kid08_part532 : Audit := .split 19 (4,true) (byMove [
.cycle 19 8 true (2),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 26 1 true (4),
.split 20 (5,false) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 31 1 true (3),
.cycle 20 1 false (2),
.cycle 0 27 true (0),
.cycle 19 4 true (2),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 27 1 true (5),
.last 22 (5,true),
.cycle 14 39 true (0),
.cycle 19 4 false (3),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 20 1 false (2),
.cycle 0 27 true (0),
.last 24 (5,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 27 1 true (5),
.last 22 (5,true)
]),
.cycle 23 1 false (7),
.cycle 32 1 false (10),
.cycle 27 1 false (7),
.cycle 30 1 false (10),
.cycle 22 1 true (6),
.split 20 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 24 (5,false),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 24 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 26 (5,false),
.cycle 19 4 true (3),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 26 (5,false),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 32 (5,false),
.cycle 31 1 false (9),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false)
]),
.cycle 26 12 true (4),
.cycle 19 3 false (3),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.split 20 (5,false) (byMove [
.last 25 (5,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 4 true (1),
.cycle 20 1 false (2),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (2),
.last 21 (5,true),
.cycle 15 12 true (1),
.cycle 19 4 false (3),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 20 1 false (2),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 19 3 false (3),
.cycle 5 16 true (0),
.last 22 (5,true),
.last 21 (5,true)
]),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 19 2 true (3),
.cycle 5 77 true (0),
.cycle 22 1 true (6),
.split 20 (5,true) (byMove [
.cycle 35 1 false (9),
.cycle 0 24 true (0),
.last 24 (5,false),
.last 34 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 49 (5,false),
.last 59 (5,false),
.last 24 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 26 (5,false),
.last 30 (5,false),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (3),
.last 22 (5,false),
.cycle 0 57 true (0),
.last 32 (5,false),
.cycle 2 22 true (0),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false)
])
])
theorem kid08_part532_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part532) = true := by rfl

def kid08_part534 : Audit := .split 23 (4,true) (byMove [
.cycle 20 8 true (2),
.cycle 36 1 false (10),
.cycle 0 81 true (0),
.cycle 0 30 true (0),
.last 26 (5,false),
.cycle 0 75 true (0),
.cycle 6 18 true (0),
.cycle 0 28 true (0),
.cycle 0 34 true (0),
.cycle 0 63 true (0),
.last 27 (5,false),
.cycle 0 30 true (0),
.cycle 0 38 true (0),
.cycle 16 8 true (2),
.cycle 17 7 false (4),
.cycle 0 30 true (0),
.cycle 18 7 false (4),
.cycle 19 5 false (4),
.cycle 0 71 true (0),
.cycle 0 28 true (0),
.cycle 22 2 true (3),
.cycle 0 57 true (0),
.last 27 (5,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 64, 64],[2, 4, 4, 1, 32, 4, 64],112⟩
])
theorem kid08_part534_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part534) = true := by rfl

def kid08_part535 : Audit := .cycle 0 57 true (0)
theorem kid08_part535_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part535) = true := by rfl

def kid08_part536 : Audit := .cycle 21 1 false (3)
theorem kid08_part536_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part536) = true := by rfl

def kid08_part537 : Audit := .cycle 20 1 false (2)
theorem kid08_part537_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part537) = true := by rfl

def kid08_part538 : Audit := .split 21 (5,false) (byMove [
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 21 1 false (3),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.last 22 (4,true),
.cycle 27 1 true (5),
.cycle 30 14 true (4),
.last 24 (4,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 18 4 true (2),
.cycle 21 1 false (3),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.last 23 (4,true),
.cycle 5 87 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid08_part538_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part538) = true := by rfl

def kid08_part539 : Audit := .split 20 (5,false) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 2 true (1),
.cycle 20 1 false (2),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 26 2 true (4),
.cycle 26 1 true (4),
.cycle 14 39 true (0),
.last 23 (4,true),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 20 1 false (2),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 26 2 true (4),
.cycle 34 1 true (0)
])
theorem kid08_part539_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part539) = true := by rfl

def kid08_part540 : Audit := .cycle 23 1 false (7)
theorem kid08_part540_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part540) = true := by rfl

def kid08_part541 : Audit := .cycle 32 1 false (10)
theorem kid08_part541_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part541) = true := by rfl

def kid08_part542 : Audit := .cycle 27 1 false (7)
theorem kid08_part542_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part542) = true := by rfl

def kid08_part543 : Audit := .cycle 30 1 false (10)
theorem kid08_part543_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part543) = true := by rfl

def kid08_part544 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 22 (5,false),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 25 (5,false),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false),
.last 27 (5,false),
.cycle 20 3 false (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 27 (5,false),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 33 (5,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false)
])
theorem kid08_part544_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part544) = true := by rfl

def kid08_part545 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 22 2 true (5),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 22 2 true (6),
.cycle 22 1 true (6),
.cycle 21 13 true (5),
.last 25 (4,true),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 21 3 true (5),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.cycle 22 2 true (6),
.cycle 22 1 true (6)
])
theorem kid08_part545_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part545) = true := by rfl

def kid08_part546 : Audit := .cycle 26 12 true (4)
theorem kid08_part546_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part546) = true := by rfl

def kid08_part547 : Audit := .split 22 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 58 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 24 (5,false),
.last 23 (5,false),
.cycle 40 1 false (10),
.cycle 39 1 false (7),
.cycle 17 6 true (2),
.cycle 27 1 false (7),
.last 27 (5,false),
.cycle 19 4 true (2),
.cycle 15 16 true (1),
.cycle 20 3 false (3),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.cycle 18 5 false (3),
.last 23 (5,false),
.cycle 55 16 true (7),
.cycle 30 14 true (4),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.last 27 (5,false),
.cycle 16 8 true (2)
])
theorem kid08_part547_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part547) = true := by rfl

def kid08_part548 : Audit := .cycle 25 1 false (7)
theorem kid08_part548_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part548) = true := by rfl

def kid08_part549 : Audit := .cycle 20 1 false (2)
theorem kid08_part549_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part549) = true := by rfl

def kid08_part550 : Audit := .cycle 18 2 true (2)
theorem kid08_part550_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part550) = true := by rfl

def kid08_part551 : Audit := .split 20 (5,false) (byMove [
.last 24 (4,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 2 true (1),
.cycle 20 1 false (2),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 19 2 true (2),
.cycle 15 12 true (1),
.last 23 (4,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 20 1 false (2),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 22 (4,true),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 19 3 false (3)
])
theorem kid08_part551_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part551) = true := by rfl

def kid08_part552 : Audit := .cycle 0 59 true (0)
theorem kid08_part552_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part552) = true := by rfl

def kid08_part553 : Audit := .cycle 1 23 true (0)
theorem kid08_part553_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part553) = true := by rfl

def kid08_part554 : Audit := .split 21 (4,true) (byMove [
.cycle 20 8 true (2),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 25 1 false (7),
.cycle 33 1 false (9),
.cycle 37 1 false (9),
.cycle 32 1 false (10),
.last 25 (5,false),
.cycle 33 1 false (9),
.cycle 16 40 true (2),
.cycle 20 3 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 18 4 true (2),
.last 22 (5,false),
.cycle 30 57 true (4),
.cycle 16 78 true (2),
.cycle 20 2 true (3),
.cycle 0 85 true (0),
.last 25 (5,false),
.cycle 2 24 true (0)
])
theorem kid08_part554_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part554) = true := by rfl

def kid08_part555 : Audit := .cycle 5 77 true (0)
theorem kid08_part555_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part555) = true := by rfl

def kid08_part556 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.last 27 (5,false),
.last 35 (5,false),
.last 23 (5,false),
.last 25 (5,false),
.last 50 (5,false),
.last 60 (5,false),
.last 25 (5,false),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false),
.last 27 (5,false),
.last 31 (5,false),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 18 4 true (2),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 33 (5,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false)
])
theorem kid08_part556_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part556) = true := by rfl

def kid08_part557 : Audit := .split 22 (5,false) (byMove [
.cycle 19 25 true (3),
.cycle 19 30 true (3),
.last 24 (4,true),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 19 24 true (3),
.cycle 21 11 true (5),
.cycle 3 20 true (0),
.cycle 22 2 true (6),
.cycle 22 1 true (6),
.cycle 20 15 true (4),
.cycle 21 5 true (5),
.last 24 (4,true),
.cycle 19 28 true (3),
.last 23 (4,true),
.cycle 20 3 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 19 29 true (3),
.cycle 22 2 true (6),
.cycle 22 1 true (6)
])
theorem kid08_part557_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part557) = true := by rfl

def kid08_part533 : Audit := .split 19 (5,true) (byMove [(kid08_part534),(kid08_part535),(kid08_part536),(kid08_part537),(kid08_part538),(kid08_part539),(kid08_part540),(kid08_part541),(kid08_part542),(kid08_part543),(kid08_part544),(kid08_part545),(kid08_part546),(kid08_part547),(kid08_part548),(kid08_part549),(kid08_part550),(kid08_part551),(kid08_part552),(kid08_part553),(kid08_part554),(kid08_part555),(kid08_part556),(kid08_part557)])

theorem kid08_part533_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part533) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part534),(kid08_part535),(kid08_part536),(kid08_part537),(kid08_part538),(kid08_part539),(kid08_part540),(kid08_part541),(kid08_part542),(kid08_part543),(kid08_part544),(kid08_part545),(kid08_part546),(kid08_part547),(kid08_part548),(kid08_part549),(kid08_part550),(kid08_part551),(kid08_part552),(kid08_part553),(kid08_part554),(kid08_part555),(kid08_part556),(kid08_part557)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part534_checked

  · exact kid08_part540_checked

  · exact kid08_part546_checked

  · exact kid08_part552_checked

  · exact kid08_part535_checked

  · exact kid08_part541_checked

  · exact kid08_part547_checked

  · exact kid08_part553_checked

  · exact kid08_part536_checked

  · exact kid08_part542_checked

  · exact kid08_part548_checked

  · exact kid08_part554_checked

  · exact kid08_part537_checked

  · exact kid08_part543_checked

  · exact kid08_part549_checked

  · exact kid08_part555_checked

  · exact kid08_part538_checked

  · exact kid08_part544_checked

  · exact kid08_part550_checked

  · exact kid08_part556_checked

  · exact kid08_part539_checked

  · exact kid08_part545_checked

  · exact kid08_part551_checked

  · exact kid08_part557_checked

def kid08_part558 : Audit := .cycle 15 8 true (1)
theorem kid08_part558_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part558) = true := by rfl

def kid08_part559 : Audit := .split 21 (4,true) (byMove [
.cycle 19 8 true (0),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.split 22 (5,false) (byMove [
.cycle 78 34 true (4),
.cycle 12 13 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 16 11 false (3),
.cycle 19 4 true (0),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.last 24 (5,true),
.cycle 14 67 true (-1),
.cycle 19 4 false (2),
.cycle 16 13 false (3),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 16 14 false (3),
.last 26 (5,true),
.cycle 62 30 true (4),
.cycle 13 10 true (0),
.cycle 16 8 false (3),
.last 24 (5,true)
]),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.cycle 24 5 true (4),
.split 22 (5,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 58 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.last 23 (5,false),
.cycle 40 1 false (10),
.cycle 39 1 false (7),
.cycle 17 6 true (1),
.cycle 27 1 false (7),
.last 26 (5,false),
.last 26 (5,false),
.cycle 16 11 false (3),
.cycle 19 4 true (1),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.cycle 18 5 false (2),
.last 23 (5,false),
.cycle 55 16 true (7),
.cycle 16 10 true (1),
.cycle 39 1 false (9),
.cycle 5 18 true (0),
.last 26 (5,false),
.last 26 (5,false)
]),
.cycle 16 10 false (3),
.cycle 19 3 false (2),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.split 22 (5,false) (byMove [
.last 27 (5,true),
.cycle 14 54 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.cycle 15 8 true (0),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.cycle 21 2 true (0),
.last 23 (5,true),
.cycle 16 11 false (3),
.cycle 19 4 false (2),
.cycle 14 10 true (-1),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 22 1 false (0),
.last 30 (5,true),
.cycle 16 10 false (3),
.cycle 20 3 false (2),
.cycle 5 36 true (0),
.last 24 (5,true),
.last 23 (5,true)
]),
.cycle 22 22 true (2),
.cycle 16 9 false (3),
.cycle 20 2 true (1),
.cycle 14 41 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 16, 64, 64],[2, 4, 16, 1, 16, 64, 64],96⟩,
.split 22 (5,true) (byMove [
.cycle 47 1 false (9),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.cycle 16 12 true (1),
.last 24 (5,false),
.last 24 (5,false),
.cycle 15 41 true (1),
.cycle 23 22 true (2),
.cycle 16 9 false (3),
.cycle 0 52 true (0),
.last 26 (5,false),
.last 26 (5,false),
.cycle 15 8 true (1),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.cycle 21 2 true (1),
.last 24 (5,false),
.cycle 55 16 true (7),
.cycle 16 13 false (4),
.cycle 2 30 true (0),
.cycle 5 18 true (0),
.last 26 (5,false),
.last 26 (5,false)
])
])
theorem kid08_part559_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part559) = true := by rfl

def kid08_part560 : Audit := .cycle 36 1 false (10)
theorem kid08_part560_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part560) = true := by rfl

def kid08_part561 : Audit := .cycle 19 1 false (1)
theorem kid08_part561_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part561) = true := by rfl

def kid08_part562 : Audit := .cycle 18 1 false (2)
theorem kid08_part562_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part562) = true := by rfl

def kid08_part564 : Audit := .split 23 (4,true) (byMove [
.cycle 20 8 true (0),
.cycle 48 1 false (10),
.cycle 17 7 false (3),
.last 29 (5,true),
.cycle 18 7 false (2),
.last 24 (5,true),
.cycle 6 36 true (0),
.cycle 16 16 true (0),
.last 26 (5,true),
.cycle 62 30 true (4),
.cycle 26 7 true (4),
.last 24 (5,true),
.cycle 15 9 false (3),
.cycle 16 8 false (3),
.cycle 17 7 false (3),
.cycle 14 10 true (0),
.cycle 18 7 false (2),
.last 24 (5,true),
.cycle 30 26 true (2),
.last 27 (5,true),
.cycle 22 2 true (1),
.cycle 14 47 true (0),
.last 29 (5,true),
.last 24 (5,true)
])
theorem kid08_part564_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part564) = true := by rfl

def kid08_part565 : Audit := .cycle 56 26 true (4)
theorem kid08_part565_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part565) = true := by rfl

def kid08_part566 : Audit := .cycle 21 1 false (1)
theorem kid08_part566_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part566) = true := by rfl

def kid08_part567 : Audit := .cycle 20 1 false (0)
theorem kid08_part567_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part567) = true := by rfl

def kid08_part568 : Audit := .cycle 18 2 false (2)
theorem kid08_part568_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part568) = true := by rfl

def kid08_part569 : Audit := .cycle 19 1 false (1)
theorem kid08_part569_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part569) = true := by rfl

def kid08_part570 : Audit := .cycle 33 1 false (7)
theorem kid08_part570_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part570) = true := by rfl

def kid08_part571 : Audit := .cycle 16 4 true (1)
theorem kid08_part571_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part571) = true := by rfl

def kid08_part572 : Audit := .cycle 17 3 false (3)
theorem kid08_part572_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part572) = true := by rfl

def kid08_part573 : Audit := .cycle 36 1 false (10)
theorem kid08_part573_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part573) = true := by rfl

def kid08_part574 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 18 4 true (1),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (1),
.cycle 25 1 false (7),
.cycle 23 3 true (5),
.last 21 (5,true),
.last 25 (5,true),
.cycle 20 3 false (2),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 19 2 true (1),
.cycle 49 14 true (7),
.last 24 (5,true),
.cycle 20 2 true (2),
.cycle 5 16 true (0),
.last 25 (5,true),
.last 21 (5,true)
])
theorem kid08_part574_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part574) = true := by rfl

def kid08_part575 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 30 1 true (4),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (1),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 24 1 true (6),
.cycle 20 5 false (3),
.last 23 (4,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (2),
.cycle 19 2 true (1),
.cycle 49 14 true (7),
.cycle 20 4 true (2),
.last 22 (4,true),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part575_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part575) = true := by rfl

def kid08_part576 : Audit := .split 24 (5,true) (byMove [
.last 28 (4,true),
.cycle 14 62 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 18 7 false (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 4, 6, 16384, 128, 256, 32768, 2, 5, 4, 128, 256, 8, 4, 4, 16384, 262144],[2, 4, 4, 1, 262144, 8, 8192, 16384, 262144, 4096, 262144, 12, 2, 4, 6, 1, 262144, 8, 262144],262144⟩,
.cycle 15 10 true (0),
.cycle 16 9 false (3),
.cycle 17 8 false (3),
.cycle 51 1 false (7),
.last 25 (4,true),
.cycle 26 21 true (2),
.cycle 20 5 false (2),
.last 27 (4,true),
.cycle 14 12 true (-1),
.cycle 25 1 false (-1),
.cycle 18 7 false (2),
.cycle 19 6 false (2),
.cycle 15 15 false (3),
.cycle 21 4 true (0),
.last 26 (4,true),
.cycle 5 42 true (0),
.last 25 (4,true),
.cycle 25 23 true (1)
])
theorem kid08_part576_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part576) = true := by rfl

def kid08_part577 : Audit := .split 22 (4,true) (byMove [
.cycle 20 8 true (-1),
.cycle 14 54 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 15 8 true (0),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.cycle 25 7 true (3),
.last 23 (5,true),
.last 27 (5,true),
.cycle 20 3 false (1),
.cycle 14 10 true (-1),
.cycle 23 1 false (-1),
.cycle 18 5 false (2),
.cycle 19 4 false (1),
.cycle 16 12 false (3),
.last 26 (5,true),
.cycle 21 2 true (0),
.cycle 5 36 true (0),
.last 29 (5,true),
.last 23 (5,true)
])
theorem kid08_part577_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part577) = true := by rfl

def kid08_part578 : Audit := .cycle 39 1 false (7)
theorem kid08_part578_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part578) = true := by rfl

def kid08_part579 : Audit := .cycle 20 1 false (0)
theorem kid08_part579_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part579) = true := by rfl

def kid08_part580 : Audit := .cycle 18 2 false (2)
theorem kid08_part580_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part580) = true := by rfl

def kid08_part581 : Audit := .cycle 19 1 false (1)
theorem kid08_part581_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part581) = true := by rfl

def kid08_part582 : Audit := .cycle 20 18 true (2)
theorem kid08_part582_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part582) = true := by rfl

def kid08_part583 : Audit := .split 23 (5,true) (byMove [
.last 27 (4,true),
.cycle 68 34 true (4),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 14 75 true (-1),
.last 27 (4,true),
.cycle 45 1 false (7),
.cycle 16 8 true (1),
.cycle 17 7 false (3),
.cycle 44 1 false (10),
.last 24 (4,true),
.cycle 1 28 true (0),
.cycle 20 5 false (3),
.last 26 (4,true),
.cycle 51 1 false (7),
.cycle 24 1 false (0),
.cycle 18 6 false (3),
.cycle 19 5 false (3),
.cycle 24 26 true (2),
.cycle 20 4 true (1),
.last 25 (4,true),
.cycle 14 47 true (0),
.last 24 (4,true),
.cycle 1 28 true (0)
])
theorem kid08_part583_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part583) = true := by rfl

def kid08_part584 : Audit := .split 21 (4,true) (byMove [
.cycle 20 8 true (0),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.cycle 62 30 true (4),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.cycle 24 5 true (4),
.last 22 (5,true),
.last 26 (5,true),
.cycle 20 3 false (2),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 18 4 false (2),
.cycle 19 3 false (2),
.cycle 22 22 true (2),
.last 25 (5,true),
.cycle 20 2 true (1),
.cycle 14 41 true (0),
.last 27 (5,true),
.last 22 (5,true)
])
theorem kid08_part584_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part584) = true := by rfl

def kid08_part585 : Audit := .cycle 14 35 true (0)
theorem kid08_part585_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part585) = true := by rfl

def kid08_part586 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 27 1 false (7),
.cycle 17 4 false (3),
.last 26 (5,true),
.cycle 18 4 false (2),
.last 21 (5,true),
.cycle 15 35 true (1),
.cycle 21 18 true (2),
.last 23 (5,true),
.cycle 0 46 true (0),
.cycle 23 3 true (5),
.last 21 (5,true),
.cycle 15 6 true (1),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.cycle 39 1 false (7),
.cycle 18 4 false (2),
.last 21 (5,true),
.cycle 49 14 true (7),
.last 24 (5,true),
.cycle 20 2 true (2),
.cycle 5 16 true (0),
.last 25 (5,true),
.last 21 (5,true)
])
theorem kid08_part586_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part586) = true := by rfl

def kid08_part587 : Audit := .split 20 (5,true) (byMove [
.last 24 (4,true),
.cycle 27 1 false (7),
.cycle 17 4 false (3),
.cycle 27 1 false (1),
.last 21 (4,true),
.cycle 55 1 true (-3),
.cycle 15 35 true (1),
.cycle 21 18 true (2),
.cycle 17 7 false (3),
.cycle 0 46 true (0),
.last 21 (4,true),
.cycle 24 1 true (6),
.cycle 15 6 true (1),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.cycle 39 1 false (7),
.last 21 (4,true),
.cycle 19 3 false (2),
.cycle 49 14 true (7),
.cycle 20 4 true (2),
.last 22 (4,true),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 24 1 true (6)
])
theorem kid08_part587_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part587) = true := by rfl

def kid08_part563 : Audit := .split 19 (5,false) (byMove [(kid08_part564),(kid08_part565),(kid08_part566),(kid08_part567),(kid08_part568),(kid08_part569),(kid08_part570),(kid08_part571),(kid08_part572),(kid08_part573),(kid08_part574),(kid08_part575),(kid08_part576),(kid08_part577),(kid08_part578),(kid08_part579),(kid08_part580),(kid08_part581),(kid08_part582),(kid08_part583),(kid08_part584),(kid08_part585),(kid08_part586),(kid08_part587)])

theorem kid08_part563_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part563) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 19 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part564),(kid08_part565),(kid08_part566),(kid08_part567),(kid08_part568),(kid08_part569),(kid08_part570),(kid08_part571),(kid08_part572),(kid08_part573),(kid08_part574),(kid08_part575),(kid08_part576),(kid08_part577),(kid08_part578),(kid08_part579),(kid08_part580),(kid08_part581),(kid08_part582),(kid08_part583),(kid08_part584),(kid08_part585),(kid08_part586),(kid08_part587)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part564_checked

  · exact kid08_part570_checked

  · exact kid08_part576_checked

  · exact kid08_part582_checked

  · exact kid08_part565_checked

  · exact kid08_part571_checked

  · exact kid08_part577_checked

  · exact kid08_part583_checked

  · exact kid08_part566_checked

  · exact kid08_part572_checked

  · exact kid08_part578_checked

  · exact kid08_part584_checked

  · exact kid08_part567_checked

  · exact kid08_part573_checked

  · exact kid08_part579_checked

  · exact kid08_part585_checked

  · exact kid08_part568_checked

  · exact kid08_part574_checked

  · exact kid08_part580_checked

  · exact kid08_part586_checked

  · exact kid08_part569_checked

  · exact kid08_part575_checked

  · exact kid08_part581_checked

  · exact kid08_part587_checked

def kid08_part588 : Audit := .cycle 43 12 true (7)
theorem kid08_part588_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part588) = true := by rfl

def kid08_part589 : Audit := .cycle 22 10 true (4)
theorem kid08_part589_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part589) = true := by rfl

def kid08_part590 : Audit := .split 20 (4,true) (byMove [
.cycle 19 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 0 52 true (0),
.split 21 (5,false) (byMove [
.cycle 0 58 true (0),
.cycle 12 12 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 12 12 true (0),
.cycle 21 1 false (1),
.last 28 (5,true),
.cycle 19 4 true (1),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 18 4 true (1),
.last 23 (5,true),
.cycle 0 111 true (0),
.cycle 19 4 false (3),
.last 30 (5,true),
.cycle 22 1 false (0),
.cycle 18 4 false (3),
.cycle 21 1 false (1),
.last 28 (5,true),
.last 25 (5,true),
.cycle 0 52 true (0),
.cycle 45 1 false (7),
.last 25 (5,true),
.last 23 (5,true)
]),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.split 21 (5,true) (byMove [
.cycle 0 32 true (0),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 0 63 true (0),
.last 22 (5,false),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.cycle 32 1 false (10),
.last 24 (5,false),
.cycle 30 14 true (4),
.cycle 19 4 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 18 4 true (2),
.last 22 (5,false),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.cycle 35 1 false (9),
.cycle 5 87 true (0),
.cycle 2 23 true (0),
.last 24 (5,false)
]),
.cycle 15 12 true (1),
.cycle 19 3 false (3),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.split 21 (5,false) (byMove [
.last 26 (5,true),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 62 30 true (4),
.cycle 21 1 false (1),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.cycle 20 2 true (1),
.last 22 (5,true),
.last 28 (5,true),
.cycle 19 4 false (3),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 18 4 false (3),
.cycle 21 1 false (1),
.cycle 22 22 true (2),
.last 27 (5,true),
.cycle 19 3 false (3),
.cycle 14 41 true (0),
.last 23 (5,true),
.last 22 (5,true)
]),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 19 2 true (2),
.cycle 5 16 true (0),
.cycle 2 23 true (0),
.split 21 (5,true) (byMove [
.cycle 41 1 false (9),
.cycle 34 1 false (10),
.cycle 17 5 false (3),
.cycle 0 31 true (0),
.last 23 (5,false),
.last 23 (5,false),
.cycle 6 16 true (0),
.cycle 50 14 true (8),
.cycle 27 12 true (4),
.cycle 0 57 true (0),
.last 49 (5,false),
.last 24 (5,false),
.cycle 39 1 false (7),
.cycle 16 6 true (2),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.cycle 20 2 true (2),
.last 23 (5,false),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.cycle 22 34 true (3),
.cycle 2 23 true (0),
.last 24 (5,false)
])
])
theorem kid08_part590_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part590) = true := by rfl

def kid08_part591 : Audit := .cycle 5 14 true (0)
theorem kid08_part591_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part591) = true := by rfl

def kid08_part592 : Audit := .split 19 (4,true) (byMove [
.cycle 19 8 true (2),
.cycle 32 1 false (10),
.cycle 17 3 false (3),
.cycle 0 27 true (0),
.cycle 39 1 true (-1),
.split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 39 1 true (-1),
.last 21 (5,false),
.cycle 0 27 true (0),
.last 24 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 27 1 true (5),
.last 21 (5,false),
.cycle 14 39 true (0),
.last 24 (5,false),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.last 21 (5,false),
.cycle 0 27 true (0),
.cycle 19 4 true (2),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 27 1 true (5),
.last 21 (5,false)
]),
.cycle 6 14 true (0),
.cycle 44 12 true (8),
.cycle 23 10 true (4),
.cycle 0 51 true (0),
.cycle 22 1 true (6),
.split 20 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.last 30 (5,false),
.cycle 28 1 false (4),
.last 24 (5,false),
.last 21 (5,false),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.last 24 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 26 (5,false),
.cycle 19 4 true (3),
.cycle 0 57 true (0),
.last 28 (5,false),
.last 26 (5,false),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 32 (5,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 1024, 16777216, 128, 256, 32768, 524290, 1024, 16777216, 128, 256, 2097152, 4, 1024, 16777216, 128, 256, 8, 131072, 1024, 16777216, 16777216],[2, 4, 131072, 1, 32, 256, 8192, 16384, 256, 4096, 131072, 256, 524288, 1048576, 131072, 262144, 8388608, 256, 2, 4, 131072, 1, 32, 256, 16777216],27412512⟩,
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false)
]),
.cycle 33 1 false (7),
.cycle 16 4 true (2),
.cycle 17 3 false (3),
.cycle 36 1 false (10),
.cycle 18 3 false (3),
.split 20 (5,true) (byMove [
.cycle 19 5 false (3),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 26 (5,false),
.last 21 (5,false),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 22 (5,false),
.last 24 (5,false),
.cycle 15 12 true (1),
.last 24 (5,false),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.last 21 (5,false),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 23 (5,false),
.cycle 5 16 true (0),
.cycle 19 2 true (2),
.last 24 (5,false)
]),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 19 2 true (3),
.cycle 20 30 true (3),
.cycle 22 1 true (6),
.split 20 (5,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 1024, 16777216, 128, 256, 32768, 524290, 1024, 16777216, 128, 256, 2097152, 4, 1024, 16777216, 128, 256, 8, 2048, 1024, 16777216, 16777216],[2, 4, 2048, 1, 2048, 256, 8192, 16384, 256, 4096, 2048, 256, 524288, 1048576, 2048, 262144, 2048, 256, 2, 4, 2048, 1, 2048, 256, 16777216],27412512⟩,
.cycle 0 24 true (0),
.last 27 (5,false),
.last 34 (5,false),
.last 22 (5,false),
.last 23 (5,false),
.last 49 (5,false),
.last 59 (5,false),
.last 24 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 26 (5,false),
.last 30 (5,false),
.cycle 17 7 false (4),
.cycle 5 16 true (0),
.cycle 19 2 true (3),
.last 23 (5,false),
.cycle 0 57 true (0),
.last 32 (5,false),
.cycle 2 22 true (0),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false)
])
])
theorem kid08_part592_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part592) = true := by rfl

def kid08_part594 : Audit := .split 23 (4,true) (byMove [
.cycle 20 8 true (2),
.cycle 0 69 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.last 25 (5,false),
.last 24 (5,false),
.cycle 27 1 false (7),
.cycle 37 1 false (9),
.cycle 43 1 false (9),
.cycle 34 1 false (10),
.last 27 (5,false),
.cycle 0 30 true (0),
.cycle 16 48 true (2),
.cycle 21 3 false (4),
.cycle 29 1 false (7),
.cycle 24 1 false (2),
.cycle 18 6 true (2),
.last 24 (5,false),
.cycle 32 65 true (4),
.cycle 16 92 true (2),
.cycle 22 2 true (3),
.cycle 0 95 true (0),
.last 27 (5,false),
.cycle 39 1 false (9)
])
theorem kid08_part594_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part594) = true := by rfl

def kid08_part595 : Audit := .cycle 32 1 false (10)
theorem kid08_part595_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part595) = true := by rfl

def kid08_part596 : Audit := .cycle 17 3 false (3)
theorem kid08_part596_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part596) = true := by rfl

def kid08_part597 : Audit := .cycle 0 27 true (0)
theorem kid08_part597_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part597) = true := by rfl

def kid08_part598 : Audit := .split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 0 27 true (0),
.cycle 37 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 28 (5,false),
.last 21 (5,false),
.cycle 14 39 true (0),
.cycle 20 3 false (2),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.last 21 (5,false),
.cycle 0 27 true (0),
.cycle 1 28 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 28 (5,false),
.last 21 (5,false)
])
theorem kid08_part598_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part598) = true := by rfl

def kid08_part599 : Audit := .split 21 (5,false) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.last 24 (4,true),
.cycle 21 1 false (1),
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 24 (4,true),
.cycle 28 1 true (4),
.cycle 11 14 true (0),
.last 24 (4,true),
.last 27 (4,true),
.cycle 22 1 false (0),
.cycle 18 4 false (3),
.cycle 21 1 false (1),
.last 25 (4,true),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.last 27 (4,true),
.last 24 (4,true),
.cycle 39 1 true (-1)
])
theorem kid08_part599_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part599) = true := by rfl

def kid08_part600 : Audit := .cycle 6 14 true (0)
theorem kid08_part600_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part600) = true := by rfl

def kid08_part601 : Audit := .cycle 44 12 true (8)
theorem kid08_part601_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part601) = true := by rfl

def kid08_part602 : Audit := .cycle 23 10 true (4)
theorem kid08_part602_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part602) = true := by rfl

def kid08_part603 : Audit := .cycle 0 51 true (0)
theorem kid08_part603_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part603) = true := by rfl

def kid08_part604 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.last 31 (5,false),
.cycle 27 1 false (3),
.last 22 (5,false),
.last 21 (5,false),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.last 25 (5,false),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false),
.last 27 (5,false),
.cycle 16 8 true (2),
.cycle 0 57 true (0),
.last 29 (5,false),
.last 27 (5,false),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 33 (5,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false)
])
theorem kid08_part604_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part604) = true := by rfl

def kid08_part605 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 8, 128, 256, 8, 2, 2048, 8, 4096],[2, 4, 32, 1, 4096, 32, 2, 4, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 54 1 false (10),
.cycle 44 1 false (10),
.last 25 (4,true),
.cycle 27 1 false (3),
.cycle 0 23 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 2, 128, 256, 8, 2, 2048, 2, 4096],[2, 4, 32, 1, 4096, 32, 2, 4, 4096, 1, 4096, 32, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 32, 1, 4096, 32, 2, 4, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 9 14 true (0),
.cycle 22 2 true (6),
.cycle 22 1 true (6),
.cycle 21 13 true (5),
.last 25 (4,true),
.cycle 0 25 true (0),
.cycle 48 1 false (10),
.cycle 21 3 true (5),
.cycle 31 1 false (7),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 256, 128, 256, 8, 2, 2048, 256, 4096],[2, 4, 32, 1, 4096, 32, 2, 4, 4096, 1, 4096, 32, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 512, 128, 256, 8, 2, 2048, 512, 4096],[2, 4, 32, 1, 4096, 32, 2, 4, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 22 2 true (6),
.cycle 22 1 true (6)
])
theorem kid08_part605_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part605) = true := by rfl

def kid08_part606 : Audit := .cycle 33 1 false (7)
theorem kid08_part606_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part606) = true := by rfl

def kid08_part607 : Audit := .cycle 16 4 true (2)
theorem kid08_part607_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part607) = true := by rfl

def kid08_part608 : Audit := .cycle 17 3 false (3)
theorem kid08_part608_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part608) = true := by rfl

def kid08_part609 : Audit := .cycle 36 1 false (10)
theorem kid08_part609_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part609) = true := by rfl

def kid08_part610 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 25 (5,false),
.cycle 18 4 true (2),
.cycle 15 12 true (1),
.cycle 20 3 false (2),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.last 21 (5,false),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 20 2 true (2),
.cycle 5 16 true (0),
.last 25 (5,false),
.cycle 19 2 true (2)
])
theorem kid08_part610_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part610) = true := by rfl

def kid08_part611 : Audit := .split 21 (5,false) (byMove [
.last 25 (4,true),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.last 24 (4,true),
.cycle 21 1 false (1),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.last 22 (4,true),
.cycle 20 2 true (1),
.cycle 19 8 false (3),
.last 24 (4,true),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 18 4 false (3),
.cycle 21 1 false (1),
.cycle 22 22 true (2),
.cycle 19 7 false (3),
.last 23 (4,true),
.cycle 14 41 true (0),
.last 22 (4,true),
.cycle 19 3 false (3)
])
theorem kid08_part611_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part611) = true := by rfl

def kid08_part612 : Audit := .cycle 0 59 true (0)
theorem kid08_part612_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part612) = true := by rfl

def kid08_part613 : Audit := .cycle 1 23 true (0)
theorem kid08_part613_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part613) = true := by rfl

def kid08_part614 : Audit := .split 21 (4,true) (byMove [
.cycle 20 8 true (2),
.cycle 34 1 false (10),
.cycle 0 69 true (0),
.cycle 2 26 true (0),
.last 24 (5,false),
.cycle 0 63 true (0),
.cycle 6 16 true (0),
.cycle 2 24 true (0),
.cycle 2 28 true (0),
.cycle 0 57 true (0),
.last 25 (5,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 64, 64],[2, 4, 4, 1, 32, 4, 64],112⟩,
.cycle 2 32 true (0),
.cycle 16 6 true (2),
.cycle 17 5 false (4),
.cycle 2 26 true (0),
.cycle 18 5 false (4),
.last 25 (5,false),
.cycle 2 63 true (0),
.cycle 2 24 true (0),
.cycle 20 2 true (3),
.cycle 2 51 true (0),
.last 25 (5,false),
.cycle 2 24 true (0)
])
theorem kid08_part614_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part614) = true := by rfl

def kid08_part615 : Audit := .cycle 20 30 true (3)
theorem kid08_part615_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part615) = true := by rfl

def kid08_part616 : Audit := .split 20 (4,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.last 35 (5,false),
.last 24 (5,false),
.last 25 (5,false),
.last 50 (5,false),
.last 60 (5,false),
.last 25 (5,false),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false),
.last 27 (5,false),
.last 31 (5,false),
.last 31 (5,false),
.cycle 5 16 true (0),
.cycle 18 5 false (4),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 33 (5,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (5,false),
.last 23 (5,false)
])
theorem kid08_part616_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part616) = true := by rfl

def kid08_part617 : Audit := .split 22 (5,false) (byMove [
.cycle 19 25 true (3),
.cycle 21 12 true (4),
.last 24 (4,true),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 19 24 true (3),
.cycle 21 11 true (5),
.cycle 3 20 true (0),
.cycle 22 2 true (6),
.cycle 22 1 true (6),
.cycle 20 15 true (4),
.cycle 21 5 true (5),
.last 24 (4,true),
.cycle 19 28 true (3),
.last 23 (4,true),
.cycle 20 3 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 19 29 true (3),
.cycle 22 2 true (6),
.cycle 22 1 true (6)
])
theorem kid08_part617_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part617) = true := by rfl

def kid08_part593 : Audit := .split 19 (5,true) (byMove [(kid08_part594),(kid08_part595),(kid08_part596),(kid08_part597),(kid08_part598),(kid08_part599),(kid08_part600),(kid08_part601),(kid08_part602),(kid08_part603),(kid08_part604),(kid08_part605),(kid08_part606),(kid08_part607),(kid08_part608),(kid08_part609),(kid08_part610),(kid08_part611),(kid08_part612),(kid08_part613),(kid08_part614),(kid08_part615),(kid08_part616),(kid08_part617)])

theorem kid08_part593_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part593) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part594),(kid08_part595),(kid08_part596),(kid08_part597),(kid08_part598),(kid08_part599),(kid08_part600),(kid08_part601),(kid08_part602),(kid08_part603),(kid08_part604),(kid08_part605),(kid08_part606),(kid08_part607),(kid08_part608),(kid08_part609),(kid08_part610),(kid08_part611),(kid08_part612),(kid08_part613),(kid08_part614),(kid08_part615),(kid08_part616),(kid08_part617)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part594_checked

  · exact kid08_part600_checked

  · exact kid08_part606_checked

  · exact kid08_part612_checked

  · exact kid08_part595_checked

  · exact kid08_part601_checked

  · exact kid08_part607_checked

  · exact kid08_part613_checked

  · exact kid08_part596_checked

  · exact kid08_part602_checked

  · exact kid08_part608_checked

  · exact kid08_part614_checked

  · exact kid08_part597_checked

  · exact kid08_part603_checked

  · exact kid08_part609_checked

  · exact kid08_part615_checked

  · exact kid08_part598_checked

  · exact kid08_part604_checked

  · exact kid08_part610_checked

  · exact kid08_part616_checked

  · exact kid08_part599_checked

  · exact kid08_part605_checked

  · exact kid08_part611_checked

  · exact kid08_part617_checked

def kid08_part497 : Audit := .split 18 (4,false) (byMove [(kid08_part498),(kid08_part499),(kid08_part500),(kid08_part501),(kid08_part502),(kid08_part503),(kid08_part528),(kid08_part529),(kid08_part530),(kid08_part531),(kid08_part532),(kid08_part533),(kid08_part558),(kid08_part559),(kid08_part560),(kid08_part561),(kid08_part562),(kid08_part563),(kid08_part588),(kid08_part589),(kid08_part590),(kid08_part591),(kid08_part592),(kid08_part593)])

theorem kid08_part497_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (kid08_part497) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) 18 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part498),(kid08_part499),(kid08_part500),(kid08_part501),(kid08_part502),(kid08_part503),(kid08_part528),(kid08_part529),(kid08_part530),(kid08_part531),(kid08_part532),(kid08_part533),(kid08_part558),(kid08_part559),(kid08_part560),(kid08_part561),(kid08_part562),(kid08_part563),(kid08_part588),(kid08_part589),(kid08_part590),(kid08_part591),(kid08_part592),(kid08_part593)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part498_checked

  · exact kid08_part528_checked

  · exact kid08_part558_checked

  · exact kid08_part588_checked

  · exact kid08_part499_checked

  · exact kid08_part529_checked

  · exact kid08_part559_checked

  · exact kid08_part589_checked

  · exact kid08_part500_checked

  · exact kid08_part530_checked

  · exact kid08_part560_checked

  · exact kid08_part590_checked

  · exact kid08_part501_checked

  · exact kid08_part531_checked

  · exact kid08_part561_checked

  · exact kid08_part591_checked

  · exact kid08_part502_checked

  · exact kid08_part532_checked

  · exact kid08_part562_checked

  · exact kid08_part592_checked

  · exact kid08_part503_checked

  · exact kid08_part533_checked

  · exact kid08_part563_checked

  · exact kid08_part593_checked

def kid08_part619 : Audit := .split 22 (5,true) (byMove [
.cycle 19 8 true (1),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.cycle 32 1 false (2),
.split 23 (4,true) (byMove [
.cycle 0 64 true (0),
.cycle 12 14 true (0),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.last 24 (4,false),
.cycle 12 32 true (-1),
.last 32 (4,false),
.last 27 (4,false),
.cycle 29 1 false (7),
.cycle 24 1 false (2),
.last 24 (4,false),
.cycle 18 6 true (1),
.cycle 0 123 true (0),
.last 27 (4,false),
.last 34 (4,false),
.cycle 24 1 false (0),
.last 24 (4,false),
.cycle 18 6 false (3),
.last 32 (4,false),
.cycle 20 4 true (1),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.last 24 (4,false),
.last 29 (4,false)
]),
.cycle 12 32 true (-1),
.cycle 15 41 true (1),
.cycle 23 22 true (2),
.cycle 17 12 true (1),
.cycle 0 52 true (0),
.split 23 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 69 true (0),
.cycle 57 1 false (7),
.cycle 31 1 false (3),
.last 24 (4,false),
.cycle 0 75 true (0),
.cycle 0 52 true (0),
.cycle 16 41 true (1),
.cycle 24 22 true (2),
.cycle 14 39 true (0),
.last 26 (4,false),
.cycle 0 27 true (0),
.cycle 38 16 true (4),
.cycle 20 4 true (2),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.last 24 (4,false),
.cycle 18 12 true (1),
.cycle 0 75 true (0),
.cycle 1 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 64, 4, 64],[2, 4, 4, 1, 4, 16, 64],80⟩,
.cycle 0 101 true (0),
.last 26 (4,false),
.cycle 22 31 true (2)
]),
.cycle 0 27 true (0),
.cycle 15 8 true (1),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.split 23 (4,true) (byMove [
.cycle 19 5 false (3),
.cycle 68 34 true (4),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.last 24 (4,false),
.cycle 86 38 true (4),
.cycle 45 1 false (7),
.cycle 16 8 true (1),
.cycle 17 7 false (3),
.cycle 44 1 false (10),
.last 28 (4,false),
.last 25 (4,false),
.last 32 (4,false),
.last 27 (4,false),
.cycle 51 1 false (7),
.cycle 24 1 false (0),
.last 24 (4,false),
.cycle 18 6 false (3),
.cycle 24 26 true (2),
.last 31 (4,false),
.last 26 (4,false),
.cycle 14 47 true (0),
.last 28 (4,false),
.cycle 22 2 true (1)
]),
.cycle 18 6 false (3),
.cycle 55 16 true (7),
.cycle 34 14 true (4),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.split 23 (4,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 64, 4, 64],[2, 4, 4, 1, 4, 16, 64],80⟩,
.cycle 14 43 true (0),
.cycle 17 10 false (3),
.cycle 0 35 true (0),
.last 26 (4,false),
.last 25 (4,false),
.cycle 6 18 true (0),
.cycle 56 16 true (7),
.cycle 34 14 true (4),
.cycle 0 63 true (0),
.last 26 (4,false),
.cycle 0 27 true (0),
.cycle 24 26 true (2),
.cycle 16 16 true (1),
.cycle 17 10 false (3),
.cycle 14 47 true (0),
.last 26 (4,false),
.cycle 22 2 true (2),
.cycle 0 75 true (0),
.cycle 1 31 true (0),
.cycle 2 28 true (0),
.cycle 24 38 true (3),
.last 26 (4,false),
.last 55 (4,false)
]),
.cycle 22 29 true (2)
])
theorem kid08_part619_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid08_part619) = true := by rfl

def kid08_part620 : Audit := .cycle 0 46 true (0)
theorem kid08_part620_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid08_part620) = true := by rfl

def kid08_part621 : Audit := .cycle 20 1 false (2)
theorem kid08_part621_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid08_part621) = true := by rfl

def kid08_part622 : Audit := .cycle 19 1 false (1)
theorem kid08_part622_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid08_part622) = true := by rfl

def kid08_part624 : Audit := .cycle 0 52 true (0)
theorem kid08_part624_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part624) = true := by rfl

def kid08_part625 : Audit := .cycle 12 10 true (0)
theorem kid08_part625_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part625) = true := by rfl

def kid08_part626 : Audit := .cycle 21 1 false (1)
theorem kid08_part626_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part626) = true := by rfl

def kid08_part627 : Audit := .cycle 20 1 false (0)
theorem kid08_part627_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part627) = true := by rfl

def kid08_part628 : Audit := .cycle 19 1 false (1)
theorem kid08_part628_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part628) = true := by rfl

def kid08_part629 : Audit := .cycle 18 2 false (2)
theorem kid08_part629_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part629) = true := by rfl

def kid08_part630 : Audit := .split 24 (4,true) (byMove [
.cycle 0 75 true (0),
.cycle 42 12 true (2),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.last 29 (5,true),
.cycle 0 81 true (0),
.cycle 30 12 true (4),
.last 27 (5,true),
.cycle 36 1 false (10),
.cycle 25 1 false (3),
.cycle 29 1 false (7),
.cycle 32 12 true (3),
.cycle 14 47 true (0),
.last 27 (5,true),
.cycle 34 12 true (4),
.cycle 25 1 false (1),
.last 29 (5,true),
.cycle 14 51 true (0),
.cycle 30 12 true (4),
.last 27 (5,true),
.cycle 0 69 true (0),
.cycle 25 12 true (2),
.cycle 6 20 true (0),
.cycle 23 2 true (2)
])
theorem kid08_part630_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part630) = true := by rfl

def kid08_part631 : Audit := .split 22 (5,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 58 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 19 4 true (1),
.cycle 0 64 true (0),
.cycle 40 1 false (10),
.cycle 39 1 false (7),
.cycle 17 6 true (1),
.cycle 27 1 false (7),
.last 23 (4,true),
.cycle 36 1 false (10),
.last 27 (4,true),
.cycle 20 3 false (3),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.cycle 16 8 true (1),
.cycle 18 5 false (3),
.cycle 55 16 true (7),
.last 26 (4,true),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.last 23 (4,true),
.last 27 (4,true)
])
theorem kid08_part631_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part631) = true := by rfl

def kid08_part632 : Audit := .cycle 25 1 false (7)
theorem kid08_part632_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part632) = true := by rfl

def kid08_part633 : Audit := .cycle 20 1 false (2)
theorem kid08_part633_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part633) = true := by rfl

def kid08_part634 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 28 1 true (4),
.cycle 33 1 true (3),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.cycle 24 1 true (6),
.last 22 (5,true),
.cycle 14 51 true (0),
.last 24 (5,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 18 4 true (1),
.cycle 0 67 true (0),
.last 28 (5,true),
.last 23 (5,true),
.cycle 5 87 true (0),
.cycle 24 1 true (6),
.last 22 (5,true)
])
theorem kid08_part634_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part634) = true := by rfl

def kid08_part635 : Audit := .cycle 18 2 true (1)
theorem kid08_part635_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part635) = true := by rfl

def kid08_part636 : Audit := .cycle 0 99 true (0)
theorem kid08_part636_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part636) = true := by rfl

def kid08_part637 : Audit := .split 22 (5,true) (byMove [
.cycle 20 8 true (-1),
.last 30 (4,true),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 48 1 false (10),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.last 28 (4,true),
.last 23 (4,true),
.cycle 18 6 true (0),
.last 27 (4,true),
.cycle 20 3 false (1),
.cycle 56 1 false (10),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 128 20 true (6),
.cycle 0 111 true (0),
.cycle 21 2 true (0),
.last 28 (4,true),
.last 23 (4,true),
.last 25 (4,true)
])
theorem kid08_part637_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part637) = true := by rfl

def kid08_part638 : Audit := .split 26 (4,true) (byMove [
.cycle 0 81 true (0),
.cycle 46 14 true (2),
.cycle 28 1 false (2),
.cycle 27 1 false (1),
.last 33 (5,true),
.last 189 (5,true),
.cycle 32 14 true (4),
.last 29 (5,true),
.cycle 38 1 false (10),
.cycle 27 1 false (3),
.cycle 33 1 false (7),
.cycle 36 14 true (2),
.cycle 14 51 true (0),
.last 29 (5,true),
.cycle 34 14 true (2),
.cycle 27 1 false (1),
.last 33 (5,true),
.cycle 14 59 true (-1),
.cycle 32 14 true (4),
.last 29 (5,true),
.cycle 0 75 true (0),
.cycle 27 14 true (2),
.cycle 17 11 false (4),
.cycle 25 2 true (2)
])
theorem kid08_part638_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part638) = true := by rfl

def kid08_part639 : Audit := .cycle 20 1 false (0)
theorem kid08_part639_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part639) = true := by rfl

def kid08_part640 : Audit := .cycle 19 1 false (1)
theorem kid08_part640_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part640) = true := by rfl

def kid08_part641 : Audit := .cycle 18 2 false (2)
theorem kid08_part641_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part641) = true := by rfl

def kid08_part642 : Audit := .split 24 (4,true) (byMove [
.cycle 0 75 true (0),
.cycle 27 1 false (3),
.cycle 49 1 false (-1),
.last 29 (5,true),
.cycle 0 81 true (0),
.last 25 (5,true),
.cycle 30 12 true (4),
.last 27 (5,true),
.cycle 14 43 true (0),
.cycle 38 12 true (2),
.cycle 72 12 true (10),
.cycle 32 12 true (3),
.cycle 38 1 false (10),
.cycle 14 55 true (0),
.cycle 17 8 false (4),
.last 29 (5,true),
.cycle 0 127 true (0),
.last 25 (5,true),
.cycle 30 12 true (4),
.last 27 (5,true),
.cycle 0 69 true (0),
.cycle 25 12 true (2),
.cycle 72 12 true (10),
.cycle 23 2 true (2)
])
theorem kid08_part642_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part642) = true := by rfl

def kid08_part643 : Audit := .split 22 (5,true) (byMove [
.cycle 20 8 true (1),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.last 28 (4,true),
.last 23 (4,true),
.last 41 (4,true),
.cycle 15 41 true (1),
.cycle 23 22 true (2),
.last 25 (4,true),
.cycle 0 52 true (0),
.last 23 (4,true),
.cycle 1 27 true (0),
.cycle 15 8 true (1),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.last 23 (4,true),
.cycle 18 6 false (3),
.cycle 55 16 true (7),
.last 26 (4,true),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.last 23 (4,true),
.last 27 (4,true)
])
theorem kid08_part643_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part643) = true := by rfl

def kid08_part644 : Audit := .cycle 0 46 true (0)
theorem kid08_part644_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part644) = true := by rfl

def kid08_part645 : Audit := .cycle 39 1 false (7)
theorem kid08_part645_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part645) = true := by rfl

def kid08_part646 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.cycle 14 39 true (0),
.last 23 (5,true),
.cycle 0 34 true (0),
.cycle 46 1 true (-2),
.last 22 (5,true),
.cycle 6 16 true (0),
.cycle 50 14 true (7),
.cycle 14 43 true (0),
.cycle 0 57 true (0),
.cycle 24 1 true (6),
.last 22 (5,true),
.cycle 22 22 true (2),
.last 28 (5,true),
.last 23 (5,true),
.cycle 14 41 true (0),
.cycle 22 3 false (2),
.last 22 (5,true),
.cycle 0 67 true (0),
.last 28 (5,true),
.last 23 (5,true),
.cycle 22 34 true (3),
.cycle 24 1 true (6),
.last 22 (5,true)
])
theorem kid08_part646_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part646) = true := by rfl

def kid08_part647 : Audit := .split 21 (4,true) (byMove [
.cycle 0 58 true (0),
.cycle 12 12 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 19 3 false (2),
.cycle 18 4 false (2),
.cycle 30 14 true (3),
.last 24 (5,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 23 (5,true),
.cycle 18 4 true (1),
.cycle 0 111 true (0),
.last 24 (5,true),
.cycle 34 16 true (2),
.cycle 22 1 false (0),
.last 23 (5,true),
.cycle 18 4 false (2),
.cycle 30 14 true (3),
.last 24 (5,true),
.cycle 0 52 true (0),
.cycle 45 1 false (7),
.last 23 (5,true),
.cycle 20 2 true (1)
])
theorem kid08_part647_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part647) = true := by rfl

def kid08_part623 : Audit := .split 19 (4,false) (byMove [(kid08_part624),(kid08_part625),(kid08_part626),(kid08_part627),(kid08_part628),(kid08_part629),(kid08_part630),(kid08_part631),(kid08_part632),(kid08_part633),(kid08_part634),(kid08_part635),(kid08_part636),(kid08_part637),(kid08_part638),(kid08_part639),(kid08_part640),(kid08_part641),(kid08_part642),(kid08_part643),(kid08_part644),(kid08_part645),(kid08_part646),(kid08_part647)])

theorem kid08_part623_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid08_part623) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part624),(kid08_part625),(kid08_part626),(kid08_part627),(kid08_part628),(kid08_part629),(kid08_part630),(kid08_part631),(kid08_part632),(kid08_part633),(kid08_part634),(kid08_part635),(kid08_part636),(kid08_part637),(kid08_part638),(kid08_part639),(kid08_part640),(kid08_part641),(kid08_part642),(kid08_part643),(kid08_part644),(kid08_part645),(kid08_part646),(kid08_part647)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part624_checked

  · exact kid08_part630_checked

  · exact kid08_part636_checked

  · exact kid08_part642_checked

  · exact kid08_part625_checked

  · exact kid08_part631_checked

  · exact kid08_part637_checked

  · exact kid08_part643_checked

  · exact kid08_part626_checked

  · exact kid08_part632_checked

  · exact kid08_part638_checked

  · exact kid08_part644_checked

  · exact kid08_part627_checked

  · exact kid08_part633_checked

  · exact kid08_part639_checked

  · exact kid08_part645_checked

  · exact kid08_part628_checked

  · exact kid08_part634_checked

  · exact kid08_part640_checked

  · exact kid08_part646_checked

  · exact kid08_part629_checked

  · exact kid08_part635_checked

  · exact kid08_part641_checked

  · exact kid08_part647_checked

def kid08_part648 : Audit := .cycle 18 1 false (2)
theorem kid08_part648_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid08_part648) = true := by rfl

def kid08_part649 : Audit := .cycle 32 1 false (10)
theorem kid08_part649_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid08_part649) = true := by rfl

def kid08_part650 : Audit := .cycle 27 1 false (7)
theorem kid08_part650_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid08_part650) = true := by rfl

def kid08_part651 : Audit := .cycle 17 2 true (2)
theorem kid08_part651_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid08_part651) = true := by rfl

def kid08_part652 : Audit := .cycle 23 1 false (7)
theorem kid08_part652_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid08_part652) = true := by rfl

def kid08_part654 : Audit := .split 23 (5,true) (byMove [
.cycle 20 8 true (2),
.cycle 36 1 false (10),
.cycle 0 81 true (0),
.cycle 0 30 true (0),
.cycle 0 75 true (0),
.last 26 (4,false),
.cycle 6 18 true (0),
.cycle 0 28 true (0),
.cycle 0 34 true (0),
.cycle 0 63 true (0),
.cycle 0 30 true (0),
.last 27 (4,false),
.cycle 0 38 true (0),
.cycle 16 8 true (2),
.cycle 17 7 false (4),
.cycle 0 30 true (0),
.cycle 19 5 false (4),
.cycle 18 7 false (4),
.cycle 0 71 true (0),
.cycle 0 28 true (0),
.cycle 22 2 true (3),
.cycle 0 57 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 64, 16, 64],[2, 4, 4, 1, 4, 16, 64],112⟩,
.last 27 (4,false)
])
theorem kid08_part654_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part654) = true := by rfl

def kid08_part655 : Audit := .cycle 0 57 true (0)
theorem kid08_part655_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part655) = true := by rfl

def kid08_part656 : Audit := .cycle 21 1 false (3)
theorem kid08_part656_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part656) = true := by rfl

def kid08_part657 : Audit := .cycle 20 1 false (2)
theorem kid08_part657_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part657) = true := by rfl

def kid08_part658 : Audit := .split 20 (4,false) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 20 2 true (1),
.cycle 0 27 true (0),
.last 23 (5,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 26 1 true (4),
.cycle 26 2 true (4),
.cycle 14 39 true (0),
.last 23 (5,true),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 18 3 false (3),
.cycle 0 27 true (0),
.last 23 (5,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.cycle 34 1 true (0),
.cycle 26 2 true (4)
])
theorem kid08_part658_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part658) = true := by rfl

def kid08_part659 : Audit := .split 21 (4,false) (byMove [
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 20 2 true (2),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.cycle 27 1 true (5),
.last 22 (5,true),
.cycle 30 14 true (4),
.last 24 (5,true),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 18 4 true (2),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.last 23 (5,true),
.cycle 5 87 true (0),
.last 23 (5,true),
.last 22 (5,true)
])
theorem kid08_part659_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part659) = true := by rfl

def kid08_part660 : Audit := .cycle 23 1 false (7)
theorem kid08_part660_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part660) = true := by rfl

def kid08_part661 : Audit := .cycle 32 1 false (10)
theorem kid08_part661_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part661) = true := by rfl

def kid08_part662 : Audit := .cycle 27 1 false (7)
theorem kid08_part662_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part662) = true := by rfl

def kid08_part663 : Audit := .cycle 30 1 false (10)
theorem kid08_part663_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part663) = true := by rfl

def kid08_part664 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 22 2 true (5),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 22 1 true (6),
.cycle 22 2 true (6),
.cycle 21 13 true (5),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 21 3 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.cycle 22 1 true (6),
.cycle 22 2 true (6)
])
theorem kid08_part664_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part664) = true := by rfl

def kid08_part665 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 22 (4,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 25 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false),
.last 27 (4,false),
.cycle 20 3 false (4),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 27 (4,false),
.cycle 0 57 true (0),
.last 33 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false)
])
theorem kid08_part665_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part665) = true := by rfl

def kid08_part666 : Audit := .cycle 26 12 true (4)
theorem kid08_part666_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part666) = true := by rfl

def kid08_part667 : Audit := .split 22 (5,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 58 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.last 24 (4,false),
.cycle 40 1 false (10),
.cycle 39 1 false (7),
.cycle 17 6 true (2),
.cycle 27 1 false (7),
.cycle 19 4 true (2),
.last 27 (4,false),
.cycle 15 16 true (1),
.cycle 20 3 false (3),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 18 5 false (3),
.cycle 55 16 true (7),
.cycle 30 14 true (4),
.cycle 21 2 true (2),
.cycle 5 18 true (0),
.cycle 16 8 true (2),
.last 27 (4,false)
])
theorem kid08_part667_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part667) = true := by rfl

def kid08_part668 : Audit := .cycle 25 1 false (7)
theorem kid08_part668_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part668) = true := by rfl

def kid08_part669 : Audit := .cycle 20 1 false (2)
theorem kid08_part669_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part669) = true := by rfl

def kid08_part670 : Audit := .split 20 (4,false) (byMove [
.last 24 (5,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 20 2 true (1),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (2),
.last 21 (5,true),
.cycle 15 12 true (1),
.last 23 (5,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 18 3 false (3),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 22 (5,true),
.cycle 5 16 true (0),
.cycle 19 3 false (3),
.last 21 (5,true)
])
theorem kid08_part670_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part670) = true := by rfl

def kid08_part671 : Audit := .cycle 18 2 true (2)
theorem kid08_part671_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part671) = true := by rfl

def kid08_part672 : Audit := .cycle 0 59 true (0)
theorem kid08_part672_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part672) = true := by rfl

def kid08_part673 : Audit := .cycle 1 23 true (0)
theorem kid08_part673_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part673) = true := by rfl

def kid08_part674 : Audit := .split 21 (5,true) (byMove [
.cycle 20 8 true (2),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 25 1 false (7),
.cycle 33 1 false (9),
.cycle 37 1 false (9),
.cycle 32 1 false (10),
.cycle 33 1 false (9),
.last 25 (4,false),
.cycle 16 40 true (2),
.cycle 20 3 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 18 4 true (2),
.cycle 30 57 true (4),
.cycle 16 78 true (2),
.cycle 20 2 true (3),
.cycle 0 85 true (0),
.cycle 2 24 true (0),
.last 25 (4,false)
])
theorem kid08_part674_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part674) = true := by rfl

def kid08_part675 : Audit := .cycle 5 77 true (0)
theorem kid08_part675_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part675) = true := by rfl

def kid08_part676 : Audit := .split 22 (4,false) (byMove [
.cycle 19 25 true (3),
.cycle 19 30 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 21 2 true (5),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 19 24 true (3),
.cycle 21 11 true (5),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.cycle 22 2 true (6),
.cycle 20 15 true (4),
.cycle 21 5 true (5),
.last 24 (5,true),
.cycle 19 28 true (3),
.cycle 20 3 true (4),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 19 29 true (3),
.cycle 22 1 true (6),
.cycle 22 2 true (6)
])
theorem kid08_part676_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part676) = true := by rfl

def kid08_part677 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.last 27 (4,false),
.last 35 (4,false),
.last 25 (4,false),
.last 23 (4,false),
.last 50 (4,false),
.last 60 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false),
.last 27 (4,false),
.last 31 (4,false),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (3),
.cycle 18 4 true (2),
.cycle 0 57 true (0),
.last 33 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false)
])
theorem kid08_part677_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part677) = true := by rfl

def kid08_part653 : Audit := .split 19 (4,true) (byMove [(kid08_part654),(kid08_part655),(kid08_part656),(kid08_part657),(kid08_part658),(kid08_part659),(kid08_part660),(kid08_part661),(kid08_part662),(kid08_part663),(kid08_part664),(kid08_part665),(kid08_part666),(kid08_part667),(kid08_part668),(kid08_part669),(kid08_part670),(kid08_part671),(kid08_part672),(kid08_part673),(kid08_part674),(kid08_part675),(kid08_part676),(kid08_part677)])

theorem kid08_part653_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid08_part653) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part654),(kid08_part655),(kid08_part656),(kid08_part657),(kid08_part658),(kid08_part659),(kid08_part660),(kid08_part661),(kid08_part662),(kid08_part663),(kid08_part664),(kid08_part665),(kid08_part666),(kid08_part667),(kid08_part668),(kid08_part669),(kid08_part670),(kid08_part671),(kid08_part672),(kid08_part673),(kid08_part674),(kid08_part675),(kid08_part676),(kid08_part677)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part654_checked

  · exact kid08_part660_checked

  · exact kid08_part666_checked

  · exact kid08_part672_checked

  · exact kid08_part655_checked

  · exact kid08_part661_checked

  · exact kid08_part667_checked

  · exact kid08_part673_checked

  · exact kid08_part656_checked

  · exact kid08_part662_checked

  · exact kid08_part668_checked

  · exact kid08_part674_checked

  · exact kid08_part657_checked

  · exact kid08_part663_checked

  · exact kid08_part669_checked

  · exact kid08_part675_checked

  · exact kid08_part658_checked

  · exact kid08_part664_checked

  · exact kid08_part670_checked

  · exact kid08_part676_checked

  · exact kid08_part659_checked

  · exact kid08_part665_checked

  · exact kid08_part671_checked

  · exact kid08_part677_checked

def kid08_part678 : Audit := .split 19 (5,true) (byMove [
.cycle 19 8 true (2),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 31 1 true (3),
.cycle 0 27 true (0),
.cycle 19 4 true (2),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 22 (4,true),
.cycle 27 1 true (5),
.cycle 14 39 true (0),
.cycle 19 4 false (3),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 18 3 false (3),
.cycle 0 27 true (0),
.last 24 (4,true),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 22 (4,true),
.cycle 27 1 true (5)
]),
.cycle 26 1 true (4),
.cycle 23 1 false (7),
.cycle 32 1 false (10),
.cycle 27 1 false (7),
.cycle 30 1 false (10),
.split 20 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 24 (4,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 24 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false),
.last 26 (4,false),
.cycle 19 4 true (3),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 26 (4,false),
.cycle 0 57 true (0),
.last 32 (4,false),
.cycle 31 1 false (9),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false)
]),
.cycle 22 1 true (6),
.cycle 26 12 true (4),
.cycle 19 3 false (3),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.last 25 (4,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 18 4 true (1),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 19 2 true (2),
.cycle 15 12 true (1),
.cycle 19 4 false (3),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 18 3 false (3),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 19 3 false (3),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 22 (4,true)
]),
.cycle 18 2 true (2),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 19 2 true (3),
.cycle 5 77 true (0),
.split 20 (4,true) (byMove [
.cycle 35 1 false (9),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 34 (4,false),
.last 22 (4,false),
.last 22 (4,false),
.last 49 (4,false),
.last 59 (4,false),
.last 24 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false),
.last 26 (4,false),
.last 30 (4,false),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 22 (4,false),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 32 (4,false),
.cycle 2 22 true (0),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false)
]),
.cycle 22 1 true (6)
])
theorem kid08_part678_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid08_part678) = true := by rfl

def kid08_part679 : Audit := .cycle 15 8 true (1)
theorem kid08_part679_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid08_part679) = true := by rfl

def kid08_part680 : Audit := .split 21 (5,true) (byMove [
.cycle 19 8 true (0),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.split 22 (4,false) (byMove [
.cycle 78 34 true (4),
.cycle 12 13 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 16 11 false (3),
.cycle 19 4 true (0),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.last 24 (4,true),
.cycle 18 5 false (2),
.cycle 14 67 true (-1),
.cycle 19 4 false (2),
.cycle 16 13 false (3),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 16 14 false (3),
.last 26 (4,true),
.cycle 62 30 true (4),
.cycle 13 10 true (0),
.last 24 (4,true),
.cycle 16 8 false (3)
]),
.cycle 18 4 false (2),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.split 22 (4,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 58 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 18 5 false (2),
.cycle 40 1 false (10),
.cycle 39 1 false (7),
.cycle 17 6 true (1),
.cycle 27 1 false (7),
.last 26 (4,false),
.last 26 (4,false),
.cycle 16 11 false (3),
.cycle 19 4 true (1),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 18 5 false (2),
.cycle 55 16 true (7),
.cycle 16 10 true (1),
.cycle 39 1 false (9),
.cycle 5 18 true (0),
.last 26 (4,false),
.last 26 (4,false)
]),
.cycle 24 5 true (4),
.cycle 16 10 false (3),
.cycle 19 3 false (2),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.split 22 (4,false) (byMove [
.last 27 (4,true),
.cycle 14 54 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.cycle 15 8 true (0),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.last 23 (4,true),
.cycle 21 2 true (0),
.cycle 16 11 false (3),
.cycle 19 4 false (2),
.cycle 14 10 true (-1),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 18 5 false (2),
.last 30 (4,true),
.cycle 16 10 false (3),
.cycle 20 3 false (2),
.cycle 5 36 true (0),
.last 23 (4,true),
.last 24 (4,true)
]),
.cycle 18 4 false (2),
.cycle 22 22 true (2),
.cycle 16 9 false (3),
.cycle 20 2 true (1),
.cycle 14 41 true (0),
.split 22 (4,true) (byMove [
.cycle 47 1 false (9),
.cycle 29 1 false (7),
.cycle 17 6 false (3),
.cycle 16 12 true (1),
.last 24 (4,false),
.last 24 (4,false),
.cycle 15 41 true (1),
.cycle 23 22 true (2),
.cycle 16 9 false (3),
.cycle 0 52 true (0),
.last 26 (4,false),
.last 26 (4,false),
.cycle 15 8 true (1),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.last 24 (4,false),
.cycle 21 2 true (1),
.cycle 55 16 true (7),
.cycle 16 13 false (4),
.cycle 2 30 true (0),
.cycle 5 18 true (0),
.last 26 (4,false),
.last 26 (4,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 32, 64],[2, 4, 32, 1, 64, 32, 64],80⟩
])
theorem kid08_part680_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid08_part680) = true := by rfl

def kid08_part681 : Audit := .cycle 36 1 false (10)
theorem kid08_part681_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid08_part681) = true := by rfl

def kid08_part682 : Audit := .cycle 19 1 false (1)
theorem kid08_part682_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid08_part682) = true := by rfl

def kid08_part684 : Audit := .split 23 (5,true) (byMove [
.cycle 20 8 true (0),
.cycle 48 1 false (10),
.cycle 17 7 false (3),
.last 29 (4,true),
.last 24 (4,true),
.cycle 18 7 false (2),
.cycle 6 36 true (0),
.cycle 16 16 true (0),
.last 26 (4,true),
.cycle 62 30 true (4),
.last 24 (4,true),
.cycle 26 7 true (4),
.cycle 15 9 false (3),
.cycle 16 8 false (3),
.cycle 17 7 false (3),
.cycle 14 10 true (0),
.last 24 (4,true),
.cycle 18 7 false (2),
.cycle 30 26 true (2),
.last 27 (4,true),
.cycle 22 2 true (1),
.cycle 14 47 true (0),
.last 24 (4,true),
.last 29 (4,true)
])
theorem kid08_part684_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid08_part684) = true := by rfl

def kid08_part685 : Audit := .cycle 56 26 true (4)
theorem kid08_part685_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid08_part685) = true := by rfl

def kid08_part686 : Audit := .cycle 21 1 false (1)
theorem kid08_part686_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid08_part686) = true := by rfl

def kid08_part687 : Audit := .cycle 20 1 false (0)
theorem kid08_part687_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid08_part687) = true := by rfl

def kid08_part688 : Audit := .cycle 19 1 false (1)
theorem kid08_part688_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid08_part688) = true := by rfl

def kid08_part689 : Audit := .cycle 18 2 false (2)
theorem kid08_part689_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid08_part689) = true := by rfl

def kid08_part690 : Audit := .cycle 33 1 false (7)
theorem kid08_part690_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid08_part690) = true := by rfl

def kid08_part691 : Audit := .cycle 16 4 true (1)
theorem kid08_part691_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid08_part691) = true := by rfl

def kid08_part692 : Audit := .cycle 17 3 false (3)
theorem kid08_part692_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid08_part692) = true := by rfl

def kid08_part693 : Audit := .cycle 36 1 false (10)
theorem kid08_part693_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid08_part693) = true := by rfl

def kid08_part694 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 30 1 true (4),
.cycle 18 3 false (2),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (1),
.cycle 25 1 false (7),
.cycle 24 1 true (6),
.last 21 (5,true),
.cycle 20 5 false (3),
.last 23 (5,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 19 2 true (1),
.cycle 18 3 false (2),
.cycle 49 14 true (7),
.cycle 20 4 true (2),
.last 22 (5,true),
.cycle 5 16 true (0),
.cycle 24 1 true (6),
.last 21 (5,true)
])
theorem kid08_part694_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid08_part694) = true := by rfl

def kid08_part695 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 4 true (1),
.cycle 18 3 false (2),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (1),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 23 3 true (5),
.last 25 (4,true),
.cycle 20 3 false (2),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 19 2 true (1),
.cycle 18 3 false (2),
.cycle 49 14 true (7),
.last 24 (4,true),
.cycle 20 2 true (2),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 25 (4,true)
])
theorem kid08_part695_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid08_part695) = true := by rfl

def kid08_part696 : Audit := .split 24 (4,true) (byMove [
.last 28 (5,true),
.cycle 14 62 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 4, 16384, 6, 128, 256, 32768, 2, 4, 5, 128, 256, 8, 4, 16384, 4, 262144],[2, 4, 4, 1, 8, 262144, 8192, 16384, 262144, 4096, 12, 262144, 2, 4, 6, 1, 8, 262144, 262144],262144⟩,
.cycle 18 7 false (2),
.cycle 15 10 true (0),
.cycle 16 9 false (3),
.cycle 17 8 false (3),
.cycle 51 1 false (7),
.cycle 26 21 true (2),
.last 25 (5,true),
.cycle 20 5 false (2),
.last 27 (5,true),
.cycle 14 12 true (-1),
.cycle 25 1 false (-1),
.cycle 19 6 false (2),
.cycle 18 7 false (2),
.cycle 15 15 false (3),
.cycle 21 4 true (0),
.last 26 (5,true),
.cycle 5 42 true (0),
.cycle 25 23 true (1),
.last 25 (5,true)
])
theorem kid08_part696_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid08_part696) = true := by rfl

def kid08_part697 : Audit := .split 22 (5,true) (byMove [
.cycle 20 8 true (-1),
.cycle 14 54 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 15 8 true (0),
.cycle 16 7 false (3),
.cycle 17 6 false (3),
.cycle 45 1 false (7),
.last 23 (4,true),
.cycle 25 7 true (3),
.last 27 (4,true),
.cycle 20 3 false (1),
.cycle 14 10 true (-1),
.cycle 23 1 false (-1),
.cycle 19 4 false (1),
.cycle 18 5 false (2),
.cycle 16 12 false (3),
.last 26 (4,true),
.cycle 21 2 true (0),
.cycle 5 36 true (0),
.last 23 (4,true),
.last 29 (4,true)
])
theorem kid08_part697_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid08_part697) = true := by rfl

def kid08_part698 : Audit := .cycle 39 1 false (7)
theorem kid08_part698_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid08_part698) = true := by rfl

def kid08_part699 : Audit := .cycle 20 1 false (0)
theorem kid08_part699_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid08_part699) = true := by rfl

def kid08_part700 : Audit := .cycle 19 1 false (1)
theorem kid08_part700_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid08_part700) = true := by rfl

def kid08_part701 : Audit := .cycle 18 2 false (2)
theorem kid08_part701_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid08_part701) = true := by rfl

def kid08_part702 : Audit := .cycle 20 18 true (2)
theorem kid08_part702_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid08_part702) = true := by rfl

def kid08_part703 : Audit := .split 23 (4,true) (byMove [
.last 27 (5,true),
.cycle 68 34 true (4),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.last 27 (5,true),
.cycle 14 75 true (-1),
.cycle 45 1 false (7),
.cycle 16 8 true (1),
.cycle 17 7 false (3),
.cycle 44 1 false (10),
.cycle 1 28 true (0),
.last 24 (5,true),
.cycle 20 5 false (3),
.last 26 (5,true),
.cycle 51 1 false (7),
.cycle 24 1 false (0),
.cycle 19 5 false (3),
.cycle 18 6 false (3),
.cycle 24 26 true (2),
.cycle 20 4 true (1),
.last 25 (5,true),
.cycle 14 47 true (0),
.cycle 1 28 true (0),
.last 24 (5,true)
])
theorem kid08_part703_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid08_part703) = true := by rfl

def kid08_part704 : Audit := .split 21 (5,true) (byMove [
.cycle 20 8 true (0),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 62 30 true (4),
.cycle 18 4 false (2),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.last 22 (4,true),
.cycle 24 5 true (4),
.last 26 (4,true),
.cycle 20 3 false (2),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 19 3 false (2),
.cycle 18 4 false (2),
.cycle 22 22 true (2),
.last 25 (4,true),
.cycle 20 2 true (1),
.cycle 14 41 true (0),
.last 22 (4,true),
.last 27 (4,true)
])
theorem kid08_part704_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid08_part704) = true := by rfl

def kid08_part705 : Audit := .cycle 14 35 true (0)
theorem kid08_part705_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid08_part705) = true := by rfl

def kid08_part706 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 27 1 false (7),
.cycle 17 4 false (3),
.cycle 27 1 false (1),
.cycle 55 1 true (-3),
.last 21 (5,true),
.cycle 15 35 true (1),
.cycle 21 18 true (2),
.cycle 17 7 false (3),
.cycle 0 46 true (0),
.cycle 24 1 true (6),
.last 21 (5,true),
.cycle 15 6 true (1),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.cycle 39 1 false (7),
.cycle 19 3 false (2),
.last 21 (5,true),
.cycle 49 14 true (7),
.cycle 20 4 true (2),
.last 22 (5,true),
.cycle 5 16 true (0),
.cycle 24 1 true (6),
.last 21 (5,true)
])
theorem kid08_part706_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid08_part706) = true := by rfl

def kid08_part707 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (1),
.cycle 27 1 false (7),
.cycle 17 4 false (3),
.last 26 (4,true),
.last 21 (4,true),
.cycle 18 4 false (2),
.cycle 15 35 true (1),
.cycle 21 18 true (2),
.last 23 (4,true),
.cycle 0 46 true (0),
.last 21 (4,true),
.cycle 23 3 true (5),
.cycle 15 6 true (1),
.cycle 16 5 false (3),
.cycle 17 4 false (3),
.cycle 39 1 false (7),
.last 21 (4,true),
.cycle 18 4 false (2),
.cycle 49 14 true (7),
.last 24 (4,true),
.cycle 20 2 true (2),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 25 (4,true)
])
theorem kid08_part707_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid08_part707) = true := by rfl

def kid08_part683 : Audit := .split 19 (4,false) (byMove [(kid08_part684),(kid08_part685),(kid08_part686),(kid08_part687),(kid08_part688),(kid08_part689),(kid08_part690),(kid08_part691),(kid08_part692),(kid08_part693),(kid08_part694),(kid08_part695),(kid08_part696),(kid08_part697),(kid08_part698),(kid08_part699),(kid08_part700),(kid08_part701),(kid08_part702),(kid08_part703),(kid08_part704),(kid08_part705),(kid08_part706),(kid08_part707)])

theorem kid08_part683_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid08_part683) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 19 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid08_part684),(kid08_part685),(kid08_part686),(kid08_part687),(kid08_part688),(kid08_part689),(kid08_part690),(kid08_part691),(kid08_part692),(kid08_part693),(kid08_part694),(kid08_part695),(kid08_part696),(kid08_part697),(kid08_part698),(kid08_part699),(kid08_part700),(kid08_part701),(kid08_part702),(kid08_part703),(kid08_part704),(kid08_part705),(kid08_part706),(kid08_part707)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part684_checked

  · exact kid08_part690_checked

  · exact kid08_part696_checked

  · exact kid08_part702_checked

  · exact kid08_part685_checked

  · exact kid08_part691_checked

  · exact kid08_part697_checked

  · exact kid08_part703_checked

  · exact kid08_part686_checked

  · exact kid08_part692_checked

  · exact kid08_part698_checked

  · exact kid08_part704_checked

  · exact kid08_part687_checked

  · exact kid08_part693_checked

  · exact kid08_part699_checked

  · exact kid08_part705_checked

  · exact kid08_part688_checked

  · exact kid08_part694_checked

  · exact kid08_part700_checked

  · exact kid08_part706_checked

  · exact kid08_part689_checked

  · exact kid08_part695_checked

  · exact kid08_part701_checked

  · exact kid08_part707_checked

def kid08_part708 : Audit := .cycle 18 1 false (2)
theorem kid08_part708_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid08_part708) = true := by rfl

def kid08_part709 : Audit := .cycle 43 12 true (7)
theorem kid08_part709_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid08_part709) = true := by rfl

def kid08_part710 : Audit := .cycle 22 10 true (4)
theorem kid08_part710_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid08_part710) = true := by rfl

def kid08_part711 : Audit := .split 20 (5,true) (byMove [
.cycle 19 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.split 21 (4,false) (byMove [
.cycle 0 58 true (0),
.cycle 12 12 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 12 12 true (0),
.last 28 (4,true),
.cycle 19 4 true (1),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 23 (4,true),
.cycle 18 4 true (1),
.cycle 0 111 true (0),
.cycle 19 4 false (3),
.last 30 (4,true),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 18 4 false (3),
.last 28 (4,true),
.last 25 (4,true),
.cycle 0 52 true (0),
.cycle 45 1 false (7),
.last 23 (4,true),
.last 25 (4,true)
]),
.cycle 0 52 true (0),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.split 21 (4,true) (byMove [
.cycle 0 32 true (0),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 0 63 true (0),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (10),
.last 24 (4,false),
.cycle 32 1 false (10),
.cycle 30 14 true (4),
.cycle 19 4 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 18 4 true (2),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.cycle 35 1 false (9),
.cycle 5 87 true (0),
.last 24 (4,false),
.cycle 2 23 true (0)
]),
.cycle 32 1 false (10),
.cycle 15 12 true (1),
.cycle 19 3 false (3),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.split 21 (4,false) (byMove [
.last 26 (4,true),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 62 30 true (4),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.last 22 (4,true),
.cycle 20 2 true (1),
.last 28 (4,true),
.cycle 19 4 false (3),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 18 4 false (3),
.cycle 22 22 true (2),
.last 27 (4,true),
.cycle 19 3 false (3),
.cycle 14 41 true (0),
.last 22 (4,true),
.last 23 (4,true)
]),
.cycle 18 3 false (3),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 19 2 true (2),
.cycle 5 16 true (0),
.split 21 (4,true) (byMove [
.cycle 41 1 false (9),
.cycle 34 1 false (10),
.cycle 17 5 false (3),
.cycle 0 31 true (0),
.last 23 (4,false),
.last 23 (4,false),
.cycle 6 16 true (0),
.cycle 50 14 true (8),
.cycle 27 12 true (4),
.cycle 0 57 true (0),
.last 24 (4,false),
.last 49 (4,false),
.cycle 39 1 false (7),
.cycle 16 6 true (2),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.last 23 (4,false),
.cycle 20 2 true (2),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.cycle 22 34 true (3),
.last 24 (4,false),
.cycle 2 23 true (0)
]),
.cycle 2 23 true (0)
])
theorem kid08_part711_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid08_part711) = true := by rfl

def kid08_part712 : Audit := .cycle 5 14 true (0)
theorem kid08_part712_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid08_part712) = true := by rfl

def kid08_part714 : Audit := .split 23 (5,true) (byMove [
.cycle 20 8 true (2),
.cycle 0 69 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.last 24 (4,false),
.last 25 (4,false),
.cycle 27 1 false (7),
.cycle 37 1 false (9),
.cycle 43 1 false (9),
.cycle 34 1 false (10),
.cycle 0 30 true (0),
.last 27 (4,false),
.cycle 16 48 true (2),
.cycle 21 3 false (4),
.cycle 29 1 false (7),
.cycle 24 1 false (2),
.last 24 (4,false),
.cycle 18 6 true (2),
.cycle 32 65 true (4),
.cycle 16 92 true (2),
.cycle 22 2 true (3),
.cycle 0 95 true (0),
.cycle 39 1 false (9),
.last 27 (4,false)
])
theorem kid08_part714_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part714) = true := by rfl

def kid08_part715 : Audit := .cycle 32 1 false (10)
theorem kid08_part715_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part715) = true := by rfl

def kid08_part716 : Audit := .cycle 17 3 false (3)
theorem kid08_part716_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part716) = true := by rfl

def kid08_part717 : Audit := .cycle 0 27 true (0)
theorem kid08_part717_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part717) = true := by rfl

def kid08_part718 : Audit := .split 21 (4,false) (byMove [
.cycle 0 48 true (0),
.cycle 40 1 false (10),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.last 24 (5,true),
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 28 1 true (4),
.last 24 (5,true),
.cycle 11 14 true (0),
.last 24 (5,true),
.last 27 (5,true),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 18 4 false (3),
.last 25 (5,true),
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.last 27 (5,true),
.cycle 39 1 true (-1),
.last 24 (5,true)
])
theorem kid08_part718_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part718) = true := by rfl

def kid08_part719 : Audit := .split 20 (5,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.last 22 (4,false),
.cycle 0 27 true (0),
.cycle 37 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 28 (4,false),
.cycle 14 39 true (0),
.cycle 20 3 false (2),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 18 3 false (3),
.cycle 0 27 true (0),
.cycle 1 28 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 21 (4,false),
.last 28 (4,false)
])
theorem kid08_part719_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part719) = true := by rfl

def kid08_part720 : Audit := .cycle 6 14 true (0)
theorem kid08_part720_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part720) = true := by rfl

def kid08_part721 : Audit := .cycle 44 12 true (8)
theorem kid08_part721_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part721) = true := by rfl

def kid08_part722 : Audit := .cycle 23 10 true (4)
theorem kid08_part722_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part722) = true := by rfl

def kid08_part723 : Audit := .cycle 0 51 true (0)
theorem kid08_part723_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part723) = true := by rfl

def kid08_part724 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 1024, 128, 256, 8, 2, 8, 1024, 4096],[2, 4, 16, 1, 16, 4096, 2, 4, 4096, 1, 16, 4096, 4096],4096⟩,
.cycle 54 1 false (10),
.cycle 44 1 false (10),
.cycle 27 1 false (3),
.last 25 (5,true),
.cycle 0 23 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 2, 1024, 128, 256, 8, 2, 2, 1024, 4096],[2, 4, 16, 1, 16, 4096, 2, 4, 4096, 1, 16, 4096, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 1024, 128, 256, 8, 2, 4, 1024, 4096],[2, 4, 16, 1, 16, 4096, 2, 4, 4096, 1, 16, 4096, 4096],4096⟩,
.cycle 9 14 true (0),
.cycle 22 1 true (6),
.cycle 22 2 true (6),
.cycle 21 13 true (5),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 48 1 false (10),
.cycle 31 1 false (7),
.cycle 21 3 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 256, 1024, 128, 256, 8, 2, 256, 1024, 4096],[2, 4, 16, 1, 16, 4096, 2, 4, 4096, 1, 16, 4096, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 512, 1024, 128, 256, 8, 2, 512, 1024, 4096],[2, 4, 16, 1, 16, 4096, 2, 4, 4096, 1, 16, 4096, 4096],4096⟩,
.cycle 22 1 true (6),
.cycle 22 2 true (6)
])
theorem kid08_part724_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part724) = true := by rfl

def kid08_part725 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.last 31 (4,false),
.cycle 27 1 false (3),
.last 21 (4,false),
.last 22 (4,false),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.last 25 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false),
.last 27 (4,false),
.cycle 16 8 true (2),
.cycle 0 57 true (0),
.last 29 (4,false),
.last 21 (4,false),
.last 27 (4,false),
.cycle 0 57 true (0),
.last 33 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false)
])
theorem kid08_part725_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part725) = true := by rfl

def kid08_part726 : Audit := .cycle 33 1 false (7)
theorem kid08_part726_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part726) = true := by rfl

def kid08_part727 : Audit := .cycle 16 4 true (2)
theorem kid08_part727_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part727) = true := by rfl

def kid08_part728 : Audit := .cycle 17 3 false (3)
theorem kid08_part728_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part728) = true := by rfl

def kid08_part729 : Audit := .cycle 36 1 false (10)
theorem kid08_part729_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part729) = true := by rfl

def kid08_part730 : Audit := .split 21 (4,false) (byMove [
.last 25 (5,true),
.cycle 62 30 true (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.last 24 (5,true),
.cycle 39 1 false (7),
.cycle 16 6 true (1),
.cycle 17 5 false (3),
.cycle 40 1 false (10),
.cycle 20 2 true (1),
.last 22 (5,true),
.cycle 19 8 false (3),
.last 24 (5,true),
.cycle 45 1 false (7),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 18 4 false (3),
.cycle 22 22 true (2),
.cycle 19 7 false (3),
.last 23 (5,true),
.cycle 14 41 true (0),
.cycle 19 3 false (3),
.last 22 (5,true)
])
theorem kid08_part730_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part730) = true := by rfl

def kid08_part731 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.last 22 (4,false),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 18 4 true (2),
.last 25 (4,false),
.cycle 15 12 true (1),
.cycle 20 3 false (2),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 18 3 false (3),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 20 2 true (2),
.cycle 5 16 true (0),
.cycle 19 2 true (2),
.last 25 (4,false)
])
theorem kid08_part731_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part731) = true := by rfl

def kid08_part732 : Audit := .cycle 0 59 true (0)
theorem kid08_part732_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part732) = true := by rfl

def kid08_part733 : Audit := .cycle 1 23 true (0)
theorem kid08_part733_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part733) = true := by rfl

def kid08_part734 : Audit := .split 21 (5,true) (byMove [
.cycle 20 8 true (2),
.cycle 34 1 false (10),
.cycle 0 69 true (0),
.cycle 2 26 true (0),
.cycle 0 63 true (0),
.last 24 (4,false),
.cycle 6 16 true (0),
.cycle 2 24 true (0),
.cycle 2 28 true (0),
.cycle 0 57 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 64, 16, 64],[2, 4, 4, 1, 4, 16, 64],112⟩,
.last 25 (4,false),
.cycle 2 32 true (0),
.cycle 16 6 true (2),
.cycle 17 5 false (4),
.cycle 2 26 true (0),
.last 25 (4,false),
.cycle 18 5 false (4),
.cycle 2 63 true (0),
.cycle 2 24 true (0),
.cycle 20 2 true (3),
.cycle 2 51 true (0),
.cycle 2 24 true (0),
.last 25 (4,false)
])
theorem kid08_part734_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part734) = true := by rfl

def kid08_part735 : Audit := .cycle 20 30 true (3)
theorem kid08_part735_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part735) = true := by rfl

def kid08_part736 : Audit := .split 22 (4,false) (byMove [
.cycle 19 25 true (3),
.cycle 21 12 true (4),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 21 2 true (5),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 19 24 true (3),
.cycle 21 11 true (5),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.cycle 22 2 true (6),
.cycle 20 15 true (4),
.cycle 21 5 true (5),
.last 24 (5,true),
.cycle 19 28 true (3),
.cycle 20 3 true (4),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 19 29 true (3),
.cycle 22 1 true (6),
.cycle 22 2 true (6)
])
theorem kid08_part736_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part736) = true := by rfl

def kid08_part737 : Audit := .split 20 (5,true) (byMove [
.cycle 20 8 true (3),
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.last 35 (4,false),
.last 25 (4,false),
.last 24 (4,false),
.last 50 (4,false),
.last 60 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false),
.last 27 (4,false),
.last 31 (4,false),
.last 31 (4,false),
.cycle 5 16 true (0),
.cycle 19 2 true (3),
.cycle 18 5 false (4),
.cycle 0 57 true (0),
.last 33 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 23 (4,false)
])
theorem kid08_part737_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part737) = true := by rfl

def kid08_part713 : Audit := .split 19 (4,true) (byMove [(kid08_part714),(kid08_part715),(kid08_part716),(kid08_part717),(kid08_part718),(kid08_part719),(kid08_part720),(kid08_part721),(kid08_part722),(kid08_part723),(kid08_part724),(kid08_part725),(kid08_part726),(kid08_part727),(kid08_part728),(kid08_part729),(kid08_part730),(kid08_part731),(kid08_part732),(kid08_part733),(kid08_part734),(kid08_part735),(kid08_part736),(kid08_part737)])

theorem kid08_part713_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid08_part713) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part714),(kid08_part715),(kid08_part716),(kid08_part717),(kid08_part718),(kid08_part719),(kid08_part720),(kid08_part721),(kid08_part722),(kid08_part723),(kid08_part724),(kid08_part725),(kid08_part726),(kid08_part727),(kid08_part728),(kid08_part729),(kid08_part730),(kid08_part731),(kid08_part732),(kid08_part733),(kid08_part734),(kid08_part735),(kid08_part736),(kid08_part737)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part714_checked

  · exact kid08_part720_checked

  · exact kid08_part726_checked

  · exact kid08_part732_checked

  · exact kid08_part715_checked

  · exact kid08_part721_checked

  · exact kid08_part727_checked

  · exact kid08_part733_checked

  · exact kid08_part716_checked

  · exact kid08_part722_checked

  · exact kid08_part728_checked

  · exact kid08_part734_checked

  · exact kid08_part717_checked

  · exact kid08_part723_checked

  · exact kid08_part729_checked

  · exact kid08_part735_checked

  · exact kid08_part718_checked

  · exact kid08_part724_checked

  · exact kid08_part730_checked

  · exact kid08_part736_checked

  · exact kid08_part719_checked

  · exact kid08_part725_checked

  · exact kid08_part731_checked

  · exact kid08_part737_checked

def kid08_part738 : Audit := .split 19 (5,true) (byMove [
.cycle 19 8 true (2),
.cycle 32 1 false (10),
.cycle 17 3 false (3),
.cycle 0 27 true (0),
.split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 39 1 true (-1),
.cycle 0 27 true (0),
.last 24 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 27 1 true (5),
.cycle 14 39 true (0),
.last 24 (4,false),
.cycle 0 50 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 18 3 false (3),
.cycle 0 27 true (0),
.cycle 19 4 true (2),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 21 (4,false),
.cycle 27 1 true (5)
]),
.cycle 39 1 true (-1),
.cycle 6 14 true (0),
.cycle 44 12 true (8),
.cycle 23 10 true (4),
.cycle 0 51 true (0),
.split 20 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.last 30 (4,false),
.cycle 28 1 false (4),
.last 21 (4,false),
.last 24 (4,false),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.last 24 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false),
.last 26 (4,false),
.cycle 19 4 true (3),
.cycle 0 57 true (0),
.last 28 (4,false),
.last 21 (4,false),
.last 26 (4,false),
.cycle 0 57 true (0),
.last 32 (4,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 2048, 128, 256, 32768, 524290, 16777216, 2048, 128, 256, 2097152, 4, 16777216, 2048, 128, 256, 8, 65536, 16777216, 2048, 16777216],[2, 4, 65536, 1, 256, 16, 8192, 16384, 256, 4096, 256, 65536, 524288, 1048576, 65536, 262144, 256, 4194304, 2, 4, 65536, 1, 256, 16, 16777216],23151632⟩,
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false)
]),
.cycle 22 1 true (6),
.cycle 33 1 false (7),
.cycle 16 4 true (2),
.cycle 17 3 false (3),
.cycle 36 1 false (10),
.split 20 (4,true) (byMove [
.cycle 19 5 false (3),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.last 26 (4,false),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 24 (4,false),
.last 22 (4,false),
.cycle 15 12 true (1),
.last 24 (4,false),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 18 3 false (3),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 23 (4,false),
.cycle 5 16 true (0),
.last 24 (4,false),
.cycle 19 2 true (2)
]),
.cycle 18 3 false (3),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 19 2 true (3),
.cycle 20 30 true (3),
.split 20 (4,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 2048, 128, 256, 32768, 524290, 16777216, 2048, 128, 256, 2097152, 4, 16777216, 2048, 128, 256, 8, 1024, 16777216, 2048, 16777216],[2, 4, 1024, 1, 256, 1024, 8192, 16384, 256, 4096, 256, 1024, 524288, 1048576, 1024, 262144, 256, 1024, 2, 4, 1024, 1, 256, 1024, 16777216],23151632⟩,
.cycle 0 24 true (0),
.last 27 (4,false),
.last 34 (4,false),
.last 23 (4,false),
.last 22 (4,false),
.last 49 (4,false),
.last 59 (4,false),
.last 24 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false),
.last 26 (4,false),
.last 30 (4,false),
.cycle 17 7 false (4),
.cycle 5 16 true (0),
.last 23 (4,false),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 32 (4,false),
.cycle 2 22 true (0),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 22 (4,false)
]),
.cycle 22 1 true (6)
])
theorem kid08_part738_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid08_part738) = true := by rfl

def kid08_part618 : Audit := .split 18 (5,false) (byMove [(kid08_part619),(kid08_part620),(kid08_part621),(kid08_part622),(kid08_part623),(kid08_part648),(kid08_part649),(kid08_part650),(kid08_part651),(kid08_part652),(kid08_part653),(kid08_part678),(kid08_part679),(kid08_part680),(kid08_part681),(kid08_part682),(kid08_part683),(kid08_part708),(kid08_part709),(kid08_part710),(kid08_part711),(kid08_part712),(kid08_part713),(kid08_part738)])

theorem kid08_part618_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (kid08_part618) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid08_part619),(kid08_part620),(kid08_part621),(kid08_part622),(kid08_part623),(kid08_part648),(kid08_part649),(kid08_part650),(kid08_part651),(kid08_part652),(kid08_part653),(kid08_part678),(kid08_part679),(kid08_part680),(kid08_part681),(kid08_part682),(kid08_part683),(kid08_part708),(kid08_part709),(kid08_part710),(kid08_part711),(kid08_part712),(kid08_part713),(kid08_part738)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part619_checked

  · exact kid08_part649_checked

  · exact kid08_part679_checked

  · exact kid08_part709_checked

  · exact kid08_part620_checked

  · exact kid08_part650_checked

  · exact kid08_part680_checked

  · exact kid08_part710_checked

  · exact kid08_part621_checked

  · exact kid08_part651_checked

  · exact kid08_part681_checked

  · exact kid08_part711_checked

  · exact kid08_part622_checked

  · exact kid08_part652_checked

  · exact kid08_part682_checked

  · exact kid08_part712_checked

  · exact kid08_part623_checked

  · exact kid08_part653_checked

  · exact kid08_part683_checked

  · exact kid08_part713_checked

  · exact kid08_part648_checked

  · exact kid08_part678_checked

  · exact kid08_part708_checked

  · exact kid08_part738_checked

def kid08_part739 : Audit := .cycle 0 51 true (0)
theorem kid08_part739_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,0⟩)) (kid08_part739) = true := by rfl

def kid08_part740 : Audit := .cycle 1 19 true (0)
theorem kid08_part740_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,1⟩)) (kid08_part740) = true := by rfl

def kid08_part741 : Audit := .cycle 2 18 true (0)
theorem kid08_part741_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,2⟩)) (kid08_part741) = true := by rfl

def kid08_part742 : Audit := .cycle 5 67 true (0)
theorem kid08_part742_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,3⟩)) (kid08_part742) = true := by rfl

def kid08_part744 : Audit := .split 22 (4,false) (byMove [
.cycle 23 24 true (4),
.cycle 35 1 false (9),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 33 1 false (9),
.split 23 (5,true) (byMove [
.cycle 33 1 false (9),
.cycle 26 1 false (6),
.cycle 28 1 false (4),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 24 24 true (4),
.cycle 35 1 false (9),
.cycle 30 1 false (8),
.last 25 (5,false),
.last 24 (5,false),
.cycle 27 1 false (7),
.cycle 20 8 true (4),
.cycle 35 1 false (9),
.cycle 34 1 false (10),
.cycle 18 12 true (3),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 22 2 true (5),
.last 24 (5,false)
]),
.cycle 0 23 true (0),
.cycle 23 24 true (5),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 22 2 true (6),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 17 29 true (3),
.cycle 17 46 true (3),
.cycle 21 9 true (5),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 21 12 true (5),
.cycle 20 4 true (4),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.last 25 (5,true),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 24 24 true (5),
.cycle 50 24 true (10),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
]),
.cycle 44 1 false (12),
.cycle 21 3 true (5),
.cycle 23 24 true (4),
.cycle 17 30 true (3),
.cycle 18 5 true (3),
.split 23 (5,true) (byMove [
.cycle 19 5 true (3),
.cycle 0 27 true (0),
.cycle 28 1 false (4),
.cycle 37 1 false (7),
.cycle 0 29 true (0),
.last 25 (5,false),
.cycle 17 30 true (3),
.cycle 44 1 false (12),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 25 (5,false),
.cycle 25 5 true (5),
.cycle 36 1 false (10),
.cycle 17 7 true (3),
.cycle 28 1 false (8),
.cycle 26 24 true (4),
.last 25 (5,false),
.cycle 24 24 true (5),
.cycle 21 11 true (5),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 24 24 true (4),
.last 25 (5,false)
]),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 24 24 true (5),
.cycle 21 11 true (5),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 24 24 true (4),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 24 24 true (6),
.cycle 21 10 true (5),
.cycle 3 21 true (0),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 17 48 true (3),
.cycle 21 4 true (5),
.cycle 24 24 true (5),
.cycle 17 31 true (3),
.cycle 18 6 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
])
])
theorem kid08_part744_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part744) = true := by rfl

def kid08_part745 : Audit := .cycle 0 22 true (0)
theorem kid08_part745_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part745) = true := by rfl

def kid08_part746 : Audit := .split 20 (4,false) (byMove [
.cycle 23 28 true (4),
.cycle 0 24 true (0),
.cycle 19 2 true (3),
.cycle 0 34 true (0),
.cycle 23 1 false (3),
.split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 40 1 false (8),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 34 true (0),
.cycle 23 28 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 26 true (0),
.cycle 19 8 true (2),
.cycle 0 38 true (0),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 34 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.cycle 20 2 true (3),
.last 22 (5,false)
]),
.cycle 0 48 true (0),
.cycle 32 24 true (6),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.last 48 (5,false),
.last 34 (5,false),
.last 30 (5,false),
.last 23 (5,false),
.last 22 (5,false),
.last 33 (5,false),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.cycle 20 2 true (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 45 (5,false),
.cycle 5 44 true (0),
.last 23 (5,false),
.last 22 (5,false)
]),
.cycle 28 1 false (8),
.cycle 24 3 true (4),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 23 1 false (3),
.split 21 (5,true) (byMove [
.cycle 26 5 true (3),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 25 1 false (7),
.cycle 28 1 false (8),
.cycle 24 3 true (4),
.cycle 32 1 false (10),
.cycle 24 1 false (4),
.last 24 (5,false),
.cycle 26 5 true (3),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 34 28 true (6),
.cycle 22 11 true (4),
.cycle 24 3 true (4),
.cycle 0 54 true (0),
.cycle 18 4 true (3),
.last 24 (5,false)
]),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 23 1 true (5),
.split 21 (5,true) (byMove [
.last 49 (5,false),
.last 32 (5,false),
.last 24 (5,false),
.cycle 0 23 true (0),
.last 25 (5,false),
.last 24 (5,false),
.cycle 0 22 true (0),
.last 57 (5,false),
.last 31 (5,false),
.cycle 3 19 true (0),
.last 23 (5,false),
.last 22 (5,false),
.last 36 (5,false),
.last 25 (5,false),
.last 26 (5,false),
.last 52 (5,false),
.cycle 18 4 true (3),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 23 (5,false),
.last 22 (5,false)
])
])
theorem kid08_part746_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part746) = true := by rfl

def kid08_part747 : Audit := .split 30 (4,false) (byMove [
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.cycle 32 1 false (6),
.split 31 (5,true) (byMove [
.cycle 0 32 true (0),
.cycle 40 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (6),
.last 33 (5,false),
.last 32 (5,false),
.cycle 0 32 true (0),
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.cycle 32 1 false (8),
.last 33 (5,false),
.last 32 (5,false),
.cycle 20 12 true (4),
.cycle 28 8 true (6),
.cycle 0 34 true (0),
.cycle 32 1 false (6),
.last 33 (5,false),
.last 32 (5,false),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 39 1 false (11),
.cycle 43 1 false (13),
.cycle 30 2 true (7),
.last 32 (5,false)
]),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 37 1 false (11),
.cycle 30 1 true (8),
.split 31 (5,false) (byMove [
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 39 1 false (11),
.cycle 43 1 false (13),
.cycle 30 2 true (8),
.last 33 (5,true),
.cycle 0 32 true (0),
.cycle 0 58 true (0),
.cycle 0 43 true (0),
.cycle 23 9 true (4),
.cycle 30 2 true (8),
.cycle 31 1 true (9),
.cycle 20 12 true (4),
.cycle 29 4 true (7),
.cycle 0 34 true (0),
.cycle 37 1 false (11),
.last 33 (5,true),
.last 33 (5,true),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 28 24 true (6),
.cycle 16 42 true (2),
.cycle 30 2 true (8),
.cycle 31 1 true (9)
]),
.cycle 34 1 false (10),
.cycle 28 3 true (6),
.cycle 0 34 true (0),
.cycle 41 1 false (13),
.cycle 32 1 false (6),
.split 31 (5,true) (byMove [
.cycle 33 5 true (7),
.cycle 0 35 true (0),
.cycle 33 1 false (7),
.cycle 32 1 false (6),
.last 33 (5,false),
.last 32 (5,false),
.cycle 41 1 false (13),
.cycle 34 1 false (10),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 33 1 false (7),
.last 33 (5,false),
.cycle 28 5 true (6),
.cycle 0 36 true (0),
.cycle 43 1 false (13),
.cycle 32 1 false (6),
.last 33 (5,false),
.last 32 (5,false),
.cycle 28 26 true (6),
.cycle 21 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 0 34 true (0),
.last 33 (5,false)
]),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.cycle 30 1 true (8),
.split 31 (5,false) (byMove [
.cycle 28 26 true (6),
.cycle 21 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.cycle 0 34 true (0),
.last 32 (5,true),
.cycle 0 32 true (0),
.cycle 28 25 true (6),
.cycle 22 10 true (4),
.cycle 3 29 true (0),
.cycle 30 2 true (8),
.cycle 31 1 true (9),
.cycle 0 45 true (0),
.cycle 28 4 true (6),
.cycle 0 35 true (0),
.cycle 0 60 true (0),
.cycle 18 14 true (3),
.last 32 (5,true),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 2 30 true (0),
.cycle 0 61 true (0),
.cycle 30 2 true (8),
.cycle 31 1 true (9)
])
])
theorem kid08_part747_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part747) = true := by rfl

def kid08_part748 : Audit := .split 20 (4,false) (byMove [
.cycle 12 59 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.split 21 (5,false) (byMove [
.cycle 0 32 true (0),
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 0 26 true (0),
.last 31 (5,true),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 20 2 true (1),
.last 25 (5,true),
.last 33 (5,true),
.last 25 (5,true),
.cycle 0 28 true (0),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 0 26 true (0),
.last 31 (5,true),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.last 23 (5,true),
.last 25 (5,true)
]),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 1 31 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 21 1 false (3),
.cycle 0 34 true (0),
.cycle 0 59 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 26 true (0),
.last 25 (5,true),
.cycle 0 38 true (0),
.cycle 22 1 false (2),
.last 23 (5,true),
.cycle 21 1 false (3),
.cycle 0 34 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (5,true),
.last 23 (5,true)
]),
.cycle 48 1 false (8),
.cycle 33 3 true (3),
.cycle 0 35 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.split 21 (5,false) (byMove [
.last 26 (5,true),
.last 29 (5,true),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 24 (5,true),
.last 27 (5,true),
.cycle 19 3 false (3),
.last 22 (5,true),
.last 26 (5,true),
.cycle 18 7 false (4),
.cycle 0 28 true (0),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 0 26 true (0),
.last 45 (5,true),
.last 24 (5,true),
.last 27 (5,true),
.cycle 18 4 false (4),
.last 22 (5,true)
]),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 2 27 true (0),
.cycle 0 67 true (0),
.cycle 27 1 true (1),
.split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 27 (5,true),
.cycle 0 29 true (0),
.cycle 19 3 false (3),
.last 22 (5,true),
.cycle 0 34 true (0),
.cycle 24 29 true (6),
.cycle 0 24 true (0),
.cycle 3 27 true (0),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 26 true (0),
.last 25 (5,true),
.cycle 17 5 false (4),
.cycle 0 67 true (0),
.cycle 19 3 false (3),
.last 22 (5,true),
.cycle 0 34 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (5,true),
.last 23 (5,true)
])
])
theorem kid08_part748_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part748) = true := by rfl

def kid08_part750 : Audit := .cycle 0 24 true (0)
theorem kid08_part750_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part750) = true := by rfl

def kid08_part751 : Audit := .split 28 (4,false) (byMove [
.cycle 38 1 false (10),
.cycle 31 1 false (7),
.cycle 27 2 true (5),
.cycle 0 30 true (0),
.last 30 (5,false),
.cycle 38 1 false (8),
.cycle 0 29 true (0),
.cycle 67 1 false (13),
.cycle 22 9 true (2),
.cycle 35 1 false (9),
.cycle 28 1 true (6),
.last 29 (5,false),
.cycle 32 1 false (8),
.cycle 26 3 true (4),
.cycle 40 1 false (8),
.cycle 39 1 false (11),
.last 30 (5,false),
.cycle 0 33 true (0),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 12 43 true (0),
.cycle 28 1 true (6),
.last 29 (5,false)
])
theorem kid08_part751_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part751) = true := by rfl

def kid08_part752 : Audit := .cycle 21 1 false (3)
theorem kid08_part752_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part752) = true := by rfl

def kid08_part753 : Audit := .cycle 20 1 false (2)
theorem kid08_part753_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part753) = true := by rfl

def kid08_part754 : Audit := .split 20 (4,false) (byMove [
.cycle 12 59 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 24 (5,false),
.last 21 (5,false),
.cycle 48 1 false (8),
.cycle 33 3 true (3),
.cycle 0 35 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 2 27 true (0),
.last 60 (5,false),
.cycle 27 1 true (1),
.last 21 (5,false)
])
theorem kid08_part754_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part754) = true := by rfl

def kid08_part755 : Audit := .split 20 (5,false) (byMove [
.last 30 (4,false),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 24 1 true (4),
.last 44 (4,false),
.last 23 (4,false),
.last 26 (4,false),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 28 (4,false),
.last 26 (4,false),
.last 21 (4,false),
.cycle 27 1 true (1)
])
theorem kid08_part755_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part755) = true := by rfl

def kid08_part756 : Audit := .split 30 (4,false) (byMove [
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.last 32 (5,false),
.cycle 0 32 true (0),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 37 1 false (11),
.cycle 30 1 true (8),
.last 31 (5,false),
.cycle 34 1 false (10),
.cycle 28 3 true (6),
.cycle 0 34 true (0),
.cycle 41 1 false (13),
.last 32 (5,false),
.cycle 41 1 false (13),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.cycle 30 1 true (8),
.last 31 (5,false)
])
theorem kid08_part756_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part756) = true := by rfl

def kid08_part757 : Audit := .split 22 (4,false) (byMove [
.cycle 24 24 true (4),
.cycle 35 1 false (9),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 33 1 false (9),
.cycle 23 24 true (4),
.cycle 0 23 true (0),
.cycle 23 24 true (5),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 44 1 false (12),
.cycle 21 3 true (5),
.cycle 23 24 true (4),
.cycle 17 30 true (3),
.cycle 18 5 true (3),
.cycle 44 1 false (12),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part757_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part757) = true := by rfl

def kid08_part758 : Audit := .cycle 0 22 true (0)
theorem kid08_part758_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part758) = true := by rfl

def kid08_part759 : Audit := .cycle 20 1 false (4)
theorem kid08_part759_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part759) = true := by rfl

def kid08_part760 : Audit := .split 20 (4,false) (byMove [
.cycle 0 53 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 23 (5,false),
.cycle 6 19 true (0),
.cycle 27 3 true (5),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 23 1 true (5),
.last 23 (5,false)
])
theorem kid08_part760_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part760) = true := by rfl

def kid08_part761 : Audit := .split 20 (5,false) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.last 24 (4,false),
.last 28 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 57 true (0),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part761_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part761) = true := by rfl

def kid08_part762 : Audit := .cycle 0 24 true (0)
theorem kid08_part762_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part762) = true := by rfl

def kid08_part763 : Audit := .split 22 (4,false) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 64, 64],[8, 8, 10, 8, 32, 2, 64],96⟩,
.cycle 0 26 true (0),
.cycle 21 2 true (3),
.cycle 0 36 true (0),
.cycle 18 5 false (4),
.cycle 19 8 true (2),
.cycle 0 52 true (0),
.cycle 36 26 true (6),
.cycle 23 9 true (5),
.cycle 0 24 true (0),
.last 24 (5,false),
.last 27 (5,false),
.cycle 45 16 true (5),
.cycle 28 3 true (4),
.cycle 17 12 true (2),
.cycle 5 18 true (0),
.cycle 18 5 false (4),
.cycle 16 8 true (2),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.cycle 2 23 true (0),
.cycle 0 24 true (0),
.cycle 27 1 true (5),
.last 27 (5,false)
])
theorem kid08_part763_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part763) = true := by rfl

def kid08_part764 : Audit := .split 32 (4,false) (byMove [
.cycle 42 1 false (12),
.cycle 35 1 false (9),
.cycle 31 2 true (7),
.cycle 0 34 true (0),
.last 34 (5,false),
.cycle 0 36 true (0),
.cycle 0 33 true (0),
.cycle 30 26 true (6),
.cycle 24 9 true (4),
.cycle 39 1 false (11),
.cycle 32 1 true (8),
.last 33 (5,false),
.cycle 36 1 false (10),
.cycle 30 3 true (6),
.cycle 0 38 true (0),
.cycle 43 1 false (13),
.last 34 (5,false),
.cycle 45 1 false (13),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 2 31 true (0),
.cycle 0 66 true (0),
.cycle 32 1 true (8),
.last 33 (5,false)
])
theorem kid08_part764_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part764) = true := by rfl

def kid08_part765 : Audit := .cycle 20 1 false (2)
theorem kid08_part765_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part765) = true := by rfl

def kid08_part766 : Audit := .split 20 (4,false) (byMove [
.last 61 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 1167, 8, 262144, 8192, 16384, 8, 2, 8, 262144, 128, 256, 8, 2, 8, 262144, 262144],[2, 4, 1024, 1, 262144, 1, 2, 4, 65536, 1, 136, 262144, 2, 4, 1024, 1, 262144, 5, 262144],395296⟩,
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 23 9 true (5),
.cycle 39 1 false (11),
.last 22 (5,false),
.cycle 19 2 true (2),
.cycle 15 35 true (1),
.last 26 (5,false),
.last 31 (5,false),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 2 23 true (0),
.cycle 0 66 true (0),
.cycle 18 3 false (4),
.last 23 (5,false)
])
theorem kid08_part766_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part766) = true := by rfl

def kid08_part767 : Audit := .split 20 (5,false) (byMove [
.last 24 (4,false),
.last 34 (4,false),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 22 (4,false),
.last 32 (4,false),
.last 23 (4,false),
.cycle 19 2 true (2),
.last 24 (4,false),
.cycle 19 6 false (3),
.last 26 (4,false),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 22 (4,false),
.last 32 (4,false),
.cycle 18 3 false (4),
.cycle 19 3 false (3)
])
theorem kid08_part767_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part767) = true := by rfl

def kid08_part768 : Audit := .split 30 (4,false) (byMove [
.cycle 0 91 true (0),
.cycle 0 61 true (0),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.last 32 (5,false),
.cycle 0 32 true (0),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 16 36 true (2),
.cycle 30 1 true (8),
.last 31 (5,false),
.cycle 0 52 true (0),
.cycle 28 3 true (6),
.cycle 0 34 true (0),
.cycle 0 67 true (0),
.last 32 (5,false),
.cycle 28 26 true (6),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.cycle 30 1 true (8),
.last 31 (5,false)
])
theorem kid08_part768_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part768) = true := by rfl

def kid08_part769 : Audit := .split 22 (4,false) (byMove [
.cycle 1 47 true (0),
.cycle 1 50 true (0),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 1 24 true (0),
.cycle 1 23 true (0),
.cycle 0 23 true (0),
.cycle 1 46 true (0),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 1 35 true (0),
.cycle 21 3 true (5),
.cycle 1 25 true (0),
.cycle 17 30 true (3),
.cycle 18 5 true (3),
.cycle 21 11 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part769_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part769) = true := by rfl

def kid08_part770 : Audit := .cycle 0 22 true (0)
theorem kid08_part770_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part770) = true := by rfl

def kid08_part771 : Audit := .cycle 25 1 false (7)
theorem kid08_part771_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part771) = true := by rfl

def kid08_part772 : Audit := .split 20 (4,false) (byMove [
.cycle 24 28 true (4),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.cycle 0 34 true (0),
.last 22 (5,false),
.cycle 19 2 true (3),
.cycle 0 48 true (0),
.cycle 33 24 true (6),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 23 (5,false),
.cycle 28 1 false (8),
.cycle 25 3 true (4),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 22 (5,false),
.cycle 18 4 true (3),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 23 1 true (5),
.last 23 (5,false)
])
theorem kid08_part772_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part772) = true := by rfl

def kid08_part773 : Audit := .split 20 (5,false) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.last 22 (4,false),
.last 32 (4,false),
.last 23 (4,false),
.cycle 19 2 true (3),
.last 47 (4,false),
.last 57 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.last 24 (4,false),
.last 28 (4,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 23 (4,false),
.cycle 22 3 true (4),
.cycle 0 57 true (0),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part773_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part773) = true := by rfl

def kid08_part749 : Audit := .split 19 (5,true) (byMove [(kid08_part750),(kid08_part751),(kid08_part752),(kid08_part753),(kid08_part754),(kid08_part755),(kid08_part756),(kid08_part757),(kid08_part758),(kid08_part759),(kid08_part760),(kid08_part761),(kid08_part762),(kid08_part763),(kid08_part764),(kid08_part765),(kid08_part766),(kid08_part767),(kid08_part768),(kid08_part769),(kid08_part770),(kid08_part771),(kid08_part772),(kid08_part773)])

theorem kid08_part749_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part749) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid08_part750),(kid08_part751),(kid08_part752),(kid08_part753),(kid08_part754),(kid08_part755),(kid08_part756),(kid08_part757),(kid08_part758),(kid08_part759),(kid08_part760),(kid08_part761),(kid08_part762),(kid08_part763),(kid08_part764),(kid08_part765),(kid08_part766),(kid08_part767),(kid08_part768),(kid08_part769),(kid08_part770),(kid08_part771),(kid08_part772),(kid08_part773)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part750_checked

  · exact kid08_part756_checked

  · exact kid08_part762_checked

  · exact kid08_part768_checked

  · exact kid08_part751_checked

  · exact kid08_part757_checked

  · exact kid08_part763_checked

  · exact kid08_part769_checked

  · exact kid08_part752_checked

  · exact kid08_part758_checked

  · exact kid08_part764_checked

  · exact kid08_part770_checked

  · exact kid08_part753_checked

  · exact kid08_part759_checked

  · exact kid08_part765_checked

  · exact kid08_part771_checked

  · exact kid08_part754_checked

  · exact kid08_part760_checked

  · exact kid08_part766_checked

  · exact kid08_part772_checked

  · exact kid08_part755_checked

  · exact kid08_part761_checked

  · exact kid08_part767_checked

  · exact kid08_part773_checked

def kid08_part774 : Audit := .split 43 (4,false) (byMove [
.cycle 15 52 true (1),
.cycle 6 51 true (0),
.cycle 42 2 true (10),
.cycle 0 45 true (0),
.cycle 0 45 true (0),
.split 44 (5,true) (byMove [
.cycle 0 45 true (0),
.cycle 20 25 true (3),
.cycle 0 55 true (0),
.cycle 54 1 false (8),
.last 46 (5,false),
.last 45 (5,false),
.cycle 0 45 true (0),
.cycle 15 52 true (1),
.cycle 6 51 true (0),
.cycle 9 36 true (0),
.last 46 (5,false),
.last 45 (5,false),
.cycle 40 12 true (8),
.cycle 41 8 true (9),
.cycle 0 47 true (0),
.cycle 0 53 true (0),
.last 46 (5,false),
.last 45 (5,false),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 0 69 true (0),
.cycle 6 69 true (0),
.cycle 43 2 true (10),
.last 45 (5,false)
]),
.cycle 0 44 true (0),
.cycle 6 57 true (0),
.cycle 40 9 true (8),
.cycle 0 67 true (0),
.cycle 43 1 true (11),
.split 44 (5,false) (byMove [
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 0 69 true (0),
.cycle 6 69 true (0),
.cycle 43 2 true (11),
.last 46 (5,true),
.cycle 0 45 true (0),
.cycle 20 25 true (3),
.cycle 0 55 true (0),
.cycle 40 9 true (8),
.cycle 43 2 true (11),
.cycle 44 1 true (12),
.cycle 40 12 true (8),
.cycle 42 4 true (10),
.cycle 0 47 true (0),
.cycle 0 67 true (0),
.last 46 (5,true),
.last 46 (5,true),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 6 57 true (0),
.cycle 0 73 true (0),
.cycle 43 2 true (11),
.cycle 44 1 true (12)
]),
.cycle 25 19 true (3),
.cycle 41 3 true (9),
.cycle 0 46 true (0),
.cycle 6 67 true (0),
.cycle 6 67 true (0),
.split 44 (5,true) (byMove [
.cycle 46 5 true (10),
.cycle 0 48 true (0),
.cycle 10 36 true (0),
.cycle 54 1 false (8),
.last 46 (5,false),
.last 45 (5,false),
.cycle 6 67 true (0),
.cycle 26 19 true (3),
.cycle 42 3 true (10),
.cycle 0 46 true (0),
.cycle 0 46 true (0),
.last 46 (5,false),
.cycle 41 5 true (9),
.cycle 0 48 true (0),
.cycle 6 69 true (0),
.cycle 11 34 true (0),
.last 46 (5,false),
.last 45 (5,false),
.cycle 6 59 true (0),
.cycle 40 11 true (8),
.cycle 42 3 true (10),
.cycle 0 46 true (0),
.cycle 0 46 true (0),
.last 46 (5,false)
]),
.cycle 0 44 true (0),
.cycle 1 43 true (0),
.cycle 2 42 true (0),
.cycle 19 27 true (3),
.cycle 43 1 true (11),
.split 44 (5,false) (byMove [
.cycle 6 59 true (0),
.cycle 40 11 true (8),
.cycle 42 3 true (10),
.cycle 0 46 true (0),
.cycle 0 46 true (0),
.last 45 (5,true),
.cycle 0 45 true (0),
.cycle 6 58 true (0),
.cycle 40 10 true (8),
.cycle 3 42 true (0),
.cycle 43 2 true (11),
.cycle 44 1 true (12),
.cycle 0 57 true (0),
.cycle 41 4 true (9),
.cycle 0 47 true (0),
.cycle 19 27 true (3),
.cycle 18 27 true (3),
.last 45 (5,true),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 2 43 true (0),
.cycle 19 28 true (3),
.cycle 43 2 true (11),
.cycle 44 1 true (12)
])
])
theorem kid08_part774_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part774) = true := by rfl

def kid08_part775 : Audit := .split 51 (4,false) (byMove [
.cycle 16 58 true (2),
.cycle 7 45 true (0),
.cycle 50 2 true (12),
.cycle 0 53 true (0),
.cycle 16 58 true (2),
.split 52 (5,true) (byMove [
.cycle 0 53 true (0),
.cycle 30 23 true (6),
.cycle 64 1 false (12),
.cycle 59 1 false (13),
.last 54 (5,false),
.last 53 (5,false),
.cycle 0 53 true (0),
.cycle 16 58 true (2),
.cycle 8 45 true (0),
.cycle 21 32 true (3),
.last 54 (5,false),
.last 53 (5,false),
.cycle 49 12 true (11),
.cycle 49 8 true (11),
.cycle 0 55 true (0),
.cycle 61 1 false (11),
.last 54 (5,false),
.last 53 (5,false),
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 27 45 true (5),
.cycle 46 32 true (8),
.cycle 51 2 true (12),
.last 53 (5,false)
]),
.cycle 0 52 true (0),
.cycle 30 22 true (6),
.cycle 49 9 true (11),
.cycle 27 43 true (5),
.cycle 51 1 true (13),
.split 52 (5,false) (byMove [
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 27 45 true (5),
.cycle 46 32 true (8),
.cycle 51 2 true (13),
.last 54 (5,true),
.cycle 0 53 true (0),
.cycle 27 46 true (5),
.cycle 20 33 true (3),
.cycle 49 9 true (11),
.cycle 51 2 true (13),
.cycle 52 1 true (14),
.cycle 49 12 true (11),
.cycle 50 4 true (12),
.cycle 0 55 true (0),
.cycle 27 43 true (5),
.last 54 (5,true),
.last 54 (5,true),
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 31 22 true (6),
.cycle 16 61 true (2),
.cycle 51 2 true (13),
.cycle 52 1 true (14)
]),
.cycle 35 17 true (6),
.cycle 49 3 true (11),
.cycle 28 24 true (6),
.cycle 46 30 true (8),
.cycle 36 17 true (6),
.split 52 (5,true) (byMove [
.cycle 54 5 true (12),
.cycle 0 56 true (0),
.cycle 22 32 true (3),
.cycle 0 60 true (0),
.last 54 (5,false),
.last 53 (5,false),
.cycle 46 30 true (8),
.cycle 36 17 true (6),
.cycle 50 3 true (12),
.cycle 0 54 true (0),
.cycle 46 30 true (8),
.last 54 (5,false),
.cycle 49 5 true (11),
.cycle 28 26 true (6),
.cycle 46 32 true (8),
.cycle 23 30 true (3),
.last 54 (5,false),
.last 53 (5,false),
.cycle 30 24 true (6),
.cycle 49 11 true (11),
.cycle 50 3 true (12),
.cycle 0 54 true (0),
.cycle 29 24 true (6),
.last 54 (5,false)
]),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.cycle 27 48 true (5),
.cycle 51 1 true (13),
.split 52 (5,false) (byMove [
.cycle 30 24 true (6),
.cycle 49 11 true (11),
.cycle 50 3 true (12),
.cycle 0 54 true (0),
.cycle 29 24 true (6),
.last 53 (5,true),
.cycle 0 53 true (0),
.cycle 30 23 true (6),
.cycle 49 10 true (11),
.cycle 3 50 true (0),
.cycle 51 2 true (13),
.cycle 52 1 true (14),
.cycle 19 35 true (3),
.cycle 49 4 true (11),
.cycle 28 25 true (6),
.cycle 27 48 true (5),
.cycle 18 35 true (3),
.last 53 (5,true),
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 2 51 true (0),
.cycle 27 49 true (5),
.cycle 51 2 true (13),
.cycle 52 1 true (14)
])
])
theorem kid08_part775_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part775) = true := by rfl

def kid08_part776 : Audit := .split 20 (4,false) (byMove [
.cycle 17 25 true (3),
.cycle 43 1 false (11),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.cycle 43 1 false (11),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 25 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 43 1 false (11),
.cycle 31 1 false (7),
.last 23 (5,false),
.last 22 (5,false),
.cycle 19 12 true (4),
.cycle 19 8 true (4),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 25 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 58 true (3),
.cycle 17 74 true (3),
.cycle 20 2 true (5),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 19 30 true (5),
.cycle 19 9 true (5),
.cycle 17 54 true (3),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 58 true (3),
.cycle 17 74 true (3),
.cycle 20 2 true (6),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 19 20 true (5),
.cycle 19 9 true (5),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 17 54 true (3),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 19 30 true (5),
.cycle 19 38 true (5),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 6 15 true (0),
.cycle 19 3 true (5),
.cycle 19 11 true (5),
.cycle 17 70 true (3),
.cycle 18 3 true (4),
.split 21 (5,true) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 32 1 false (6),
.cycle 42 1 false (8),
.last 25 (5,false),
.last 22 (5,false),
.cycle 17 70 true (3),
.cycle 7 15 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 8 15 true (0),
.last 23 (5,false),
.cycle 19 5 true (4),
.cycle 19 13 true (4),
.cycle 17 74 true (3),
.cycle 29 1 false (5),
.last 25 (5,false),
.last 22 (5,false),
.cycle 19 32 true (5),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 19 11 true (5),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 19 32 true (5),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 19 11 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 19 31 true (5),
.cycle 19 10 true (5),
.cycle 3 19 true (0),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 22 true (5),
.cycle 19 4 true (5),
.cycle 19 12 true (5),
.cycle 17 27 true (3),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part776_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part776) = true := by rfl

def kid08_part777 : Audit := .cycle 0 20 true (0)
theorem kid08_part777_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part777) = true := by rfl

def kid08_part778 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 8, 64, 64],[2, 4, 16, 1, 16, 64, 64],96⟩,
.cycle 28 2 true (6),
.cycle 27 1 false (7),
.cycle 24 1 false (4),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 256, 2, 128, 256, 32768, 524290, 16777216, 8192, 128, 256, 2097152, 4, 256, 524288, 128, 256, 8, 1024, 256, 2, 16777216],[2, 4, 1024, 1, 16, 16777216, 8192, 16384, 1024, 4096, 65536, 16777216, 524288, 1048576, 1024, 262144, 4194304, 16777216, 2, 4, 1024, 1, 16, 16777216, 16777216],18891776⟩,
.last 43 (5,true),
.last 30 (5,true),
.cycle 20 2 true (5),
.cycle 21 1 true (5),
.last 33 (5,true),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 32768, 256, 128, 256, 32768, 524290, 16777216, 256, 128, 256, 2097152, 4, 32768, 256, 128, 256, 8, 1024, 32768, 256, 16777216],[2, 4, 1024, 1, 16, 16777216, 8192, 16384, 1024, 4096, 65536, 16777216, 524288, 1048576, 1024, 262144, 4194304, 16777216, 2, 4, 1024, 1, 16, 16777216, 16777216],18891776⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 524290, 512, 128, 256, 32768, 524290, 16777216, 512, 128, 256, 2097152, 4, 524290, 512, 128, 256, 8, 1024, 524290, 512, 16777216],[2, 4, 1024, 1, 16, 16777216, 8192, 16384, 1024, 4096, 65536, 16777216, 524288, 1048576, 1024, 262144, 4194304, 16777216, 2, 4, 1024, 1, 16, 16777216, 16777216],18891776⟩,
.last 23 (5,true),
.cycle 21 1 true (5)
]),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 2, 64, 64],[2, 4, 16, 1, 16, 64, 64],96⟩,
.cycle 8 13 true (0),
.cycle 45 1 false (13),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 51 1 false (13),
.cycle 42 1 false (12),
.cycle 20 2 true (6),
.last 25 (5,true),
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 2, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 9 13 true (0),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 45 1 false (13),
.last 23 (5,true),
.last 25 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 4, 16, 1, 16, 64, 64],96⟩,
.cycle 22 3 true (6),
.cycle 0 23 true (0),
.cycle 38 1 false (12),
.cycle 27 1 false (7),
.split 21 (5,false) (byMove [
.last 26 (5,true),
.cycle 0 25 true (0),
.last 30 (5,true),
.last 28 (5,true),
.last 23 (5,true),
.last 23 (5,true),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 2, 1, 128, 256, 32768, 524290, 16777216, 4096, 128, 256, 2097152, 4, 524288, 262144, 128, 256, 8, 1024, 2, 1, 16777216],[2, 4, 1024, 1, 16, 16777216, 8192, 16384, 1024, 4096, 65536, 16777216, 524288, 1048576, 1024, 262144, 4194304, 16777216, 2, 4, 1024, 1, 16, 16777216, 16777216],18891776⟩,
.cycle 7 15 true (0),
.last 24 (5,true),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true),
.last 26 (5,true),
.cycle 23 5 true (5),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 2, 1, 128, 256, 32768, 524290, 16777216, 65536, 128, 256, 2097152, 4, 4194304, 262144, 128, 256, 8, 1024, 2, 1, 16777216],[2, 4, 1024, 1, 16, 16777216, 8192, 16384, 1024, 4096, 65536, 16777216, 524288, 1048576, 1024, 262144, 4194304, 16777216, 2, 4, 1024, 1, 16, 16777216, 16777216],18891776⟩,
.last 28 (5,true),
.last 23 (5,true),
.last 23 (5,true),
.cycle 18 24 true (4),
.last 32 (5,true),
.last 24 (5,true),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 4, 16, 1, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 8, 64, 64],[2, 4, 16, 1, 16, 64, 64],96⟩,
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 7 15 true (0),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 22, 64],[2, 4, 16, 1, 16, 64, 64],64⟩,
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part778_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part778) = true := by rfl

def kid08_part780 : Audit := .cycle 0 20 true (0)
theorem kid08_part780_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part780) = true := by rfl

def kid08_part781 : Audit := .cycle 1 19 true (0)
theorem kid08_part781_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part781) = true := by rfl

def kid08_part782 : Audit := .cycle 27 1 false (7)
theorem kid08_part782_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part782) = true := by rfl

def kid08_part783 : Audit := .cycle 31 1 false (9)
theorem kid08_part783_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part783) = true := by rfl

def kid08_part784 : Audit := .split 20 (4,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 20 2 true (3),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 20 24 true (3),
.cycle 20 9 true (3),
.cycle 27 1 false (7),
.cycle 20 1 true (4),
.last 21 (5,false),
.cycle 24 1 false (6),
.cycle 20 3 true (3),
.last 23 (5,false),
.cycle 31 1 false (9),
.cycle 23 1 false (3),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 20 31 true (3),
.cycle 20 1 true (4),
.last 21 (5,false)
])
theorem kid08_part784_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part784) = true := by rfl

def kid08_part785 : Audit := .split 20 (5,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.last 44 (4,false),
.last 29 (4,false),
.cycle 27 1 false (7),
.last 21 (4,false),
.cycle 20 1 true (4),
.cycle 24 1 false (6),
.last 23 (4,false),
.cycle 0 26 true (0),
.cycle 31 1 false (9),
.last 24 (4,false),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 51 (4,false),
.last 21 (4,false),
.cycle 20 1 true (4)
])
theorem kid08_part785_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part785) = true := by rfl

def kid08_part786 : Audit := .cycle 0 20 true (0)
theorem kid08_part786_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part786) = true := by rfl

def kid08_part787 : Audit := .split 43 (4,false) (byMove [
.cycle 16 52 true (2),
.cycle 7 51 true (0),
.cycle 42 2 true (10),
.cycle 0 45 true (0),
.last 45 (5,false),
.cycle 16 52 true (2),
.cycle 0 44 true (0),
.cycle 7 57 true (0),
.cycle 41 9 true (9),
.last 67 (5,false),
.cycle 43 1 true (11),
.last 44 (5,false),
.cycle 25 19 true (3),
.cycle 41 3 true (9),
.last 46 (5,false),
.cycle 7 67 true (0),
.cycle 7 67 true (0),
.cycle 26 19 true (3),
.cycle 0 44 true (0),
.cycle 1 43 true (0),
.cycle 2 42 true (0),
.cycle 20 27 true (3),
.cycle 43 1 true (11),
.last 44 (5,false)
])
theorem kid08_part787_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part787) = true := by rfl

def kid08_part788 : Audit := .split 30 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 38 1 false (10),
.cycle 42 1 false (12),
.last 31 (4,false),
.cycle 34 1 false (8),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 20 11 true (3),
.last 38 (4,false),
.last 31 (4,false),
.cycle 30 1 true (8),
.last 41 (4,false),
.last 33 (4,false),
.cycle 0 33 true (0),
.cycle 36 1 false (10),
.last 31 (4,false),
.cycle 28 5 true (6),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 51 (4,false),
.cycle 17 39 true (3),
.last 31 (4,false),
.cycle 30 1 true (8)
])
theorem kid08_part788_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part788) = true := by rfl

def kid08_part789 : Audit := .split 27 (4,false) (byMove [
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 26 2 true (6),
.cycle 0 29 true (0),
.last 29 (5,false),
.cycle 29 1 false (7),
.cycle 0 28 true (0),
.cycle 0 49 true (0),
.cycle 20 9 true (3),
.cycle 34 1 false (10),
.cycle 27 1 true (7),
.last 28 (5,false),
.cycle 31 1 false (9),
.cycle 25 3 true (5),
.last 30 (5,false),
.cycle 38 1 false (12),
.cycle 30 1 false (8),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.cycle 23 54 true (3),
.cycle 27 1 true (7),
.last 28 (5,false)
])
theorem kid08_part789_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part789) = true := by rfl

def kid08_part790 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.last 42 (5,false),
.cycle 28 2 true (6),
.cycle 27 1 false (7),
.last 24 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.last 46 (5,false),
.cycle 8 13 true (0),
.last 30 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 52 (5,false),
.cycle 22 3 true (6),
.cycle 0 23 true (0),
.cycle 38 1 false (12),
.cycle 27 1 false (7),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far true 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 4, 4, 5, 8, 7, 7, 4, 6],[0, 549755813888, 2097152, 512, 549755813888, 18014398509481984, 0, 0, 0, 2097152, 0, 18014398509481984, 0, 0, 549755813888, 512, 0, 18014398509481984, 0, 18014398509481984, 2251799813685248, 549755813888, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 20301382697353216, 35184372088832, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 2252349569499136, 134217728, 18014398509481984, 18014398509481984, 18014398509481984, 0, 20266198323167232, 2251799813685248, 0, 18014398509481984, 20301932451069952, 20301932451069952, 20301932451069952, 35184372088832, 20301932451069952, 18014398509481984, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 18014398509481984, 18014398509481984],[2251799813685248, 549755813888, 0, 0, 18014398509481984, 2251799813685248, 2251799813685248, 0, 18014398509481984, 549755813888, 549755813888, 18014398509481984, 0, 0, 0, 0, 18014398509481984, 0, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 2251799813685248, 20266198323167232, 20266748078981120, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014948265295872, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 0, 18014398509481984, 0, 18014398509481984, 18014398509481984, 2251799813685248, 18014398509481984],32332638220584992⟩,
.far true 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 4, 4, 5, 8, 7, 7, 4, 6],[0, 549755813888, 2097152, 512, 549755813888, 18014398509481984, 0, 0, 0, 2097152, 0, 18014398509481984, 0, 0, 549755813888, 512, 549755813888, 18014398509481984, 0, 18014398509481984, 2251799813685248, 549755813888, 0, 18014398509481984, 18014398509481984, 18014398509481984, 20301382697353216, 35184372088832, 18014948265295872, 18014398509481984, 18014398509481984, 18014398509481984, 2252349569499136, 134217728, 18014398509481984, 18014398509481984, 18014398509481984, 0, 20266198323167232, 2251799813685248, 18014398509481984, 18014398509481984, 20301932451069952, 20301932451069952, 20301932451069952, 35184372088832, 20301932451069952, 18014398509481984, 0, 18014398509481984, 0, 549755813888, 0, 18014398509481984, 18014398509481984],[2251799813685248, 549755813888, 0, 0, 18014398509481984, 2251799813685248, 2251799813685248, 0, 18014398509481984, 549755813888, 549755813888, 18014398509481984, 0, 0, 0, 0, 18014398509481984, 0, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 2251799813685248, 20266198323167232, 20266748078981120, 18014398509481984, 18014398509481984, 18014398509481984, 20266198323167232, 18014398509481984, 18014948265295872, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 0, 18014398509481984, 0, 18014398509481984, 18014398509481984, 2251799813685248, 18014398509481984],27830138100647968⟩,
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part790_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part790) = true := by rfl

def kid08_part791 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 16777216, 32768, 128, 256, 32768, 524290, 16777216, 2097160, 128, 256, 2097152, 4, 16777216, 32768, 128, 256, 8, 1024, 16777216, 32768, 16777216],[2, 4, 1024, 1, 32, 32, 8192, 16384, 1024, 4096, 131072, 131072, 524288, 1048576, 1024, 262144, 8388608, 8388608, 2, 4, 1024, 1, 32, 32, 16777216],23153680⟩,
.last 29 (4,false),
.cycle 27 1 false (7),
.last 21 (4,false),
.cycle 24 1 false (4),
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 16777216, 2, 128, 256, 32768, 524290, 16777216, 8192, 128, 256, 2097152, 4, 16777216, 524288, 128, 256, 8, 1024, 16777216, 2, 16777216],[2, 4, 1024, 1, 32, 32, 8192, 16384, 1024, 4096, 131072, 131072, 524288, 1048576, 1024, 262144, 8388608, 8388608, 2, 4, 1024, 1, 32, 32, 16777216],23151632⟩,
.cycle 8 13 true (0),
.last 38 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 27 (4,false),
.last 21 (4,false),
.cycle 27 1 false (7),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 16777216, 256, 128, 256, 32768, 524290, 16777216, 256, 128, 256, 2097152, 4, 16777216, 256, 128, 256, 8, 1024, 16777216, 256, 16777216],[2, 4, 1024, 1, 32, 32, 8192, 16384, 1024, 4096, 131072, 131072, 524288, 1048576, 1024, 262144, 8388608, 8388608, 2, 4, 1024, 1, 32, 32, 16777216],23151632⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 16777216, 512, 128, 256, 32768, 524290, 16777216, 512, 128, 256, 2097152, 4, 16777216, 512, 128, 256, 8, 1024, 16777216, 512, 16777216],[2, 4, 1024, 1, 32, 32, 8192, 16384, 1024, 4096, 131072, 131072, 524288, 1048576, 1024, 262144, 8388608, 8388608, 2, 4, 1024, 1, 32, 32, 16777216],23151632⟩,
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part791_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part791) = true := by rfl

def kid08_part792 : Audit := .split 30 (4,false) (byMove [
.last 90 (5,false),
.last 60 (5,false),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.last 32 (5,false),
.cycle 19 12 true (4),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 16 36 true (2),
.cycle 30 1 true (8),
.last 31 (5,false),
.last 51 (5,false),
.cycle 28 3 true (6),
.last 33 (5,false),
.last 66 (5,false),
.cycle 18 13 true (4),
.cycle 28 5 true (6),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.last 59 (5,false),
.cycle 30 1 true (8),
.last 31 (5,false)
])
theorem kid08_part792_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part792) = true := by rfl

def kid08_part793 : Audit := .split 22 (4,false) (byMove [
.last 47 (5,false),
.last 50 (5,false),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.last 24 (5,false),
.cycle 19 8 true (4),
.cycle 0 23 true (0),
.last 46 (5,false),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.last 35 (5,false),
.cycle 21 3 true (5),
.last 25 (5,false),
.cycle 17 30 true (3),
.cycle 18 5 true (4),
.last 27 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part793_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part793) = true := by rfl

def kid08_part794 : Audit := .cycle 0 22 true (0)
theorem kid08_part794_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part794) = true := by rfl

def kid08_part795 : Audit := .cycle 25 1 false (7)
theorem kid08_part795_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part795) = true := by rfl

def kid08_part796 : Audit := .split 20 (4,false) (byMove [
.last 51 (5,false),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.cycle 0 34 true (0),
.last 22 (5,false),
.last 23 (5,false),
.cycle 0 48 true (0),
.last 32 (5,false),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 19 2 true (4),
.cycle 28 1 false (8),
.last 24 (5,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 23 1 false (3),
.last 23 (5,false),
.last 55 (5,false),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 18 4 true (4)
])
theorem kid08_part796_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part796) = true := by rfl

def kid08_part797 : Audit := .split 20 (5,false) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.last 22 (4,false),
.last 32 (4,false),
.last 23 (4,false),
.cycle 22 1 false (2),
.last 47 (4,false),
.cycle 29 26 true (5),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 19 2 true (4),
.last 24 (4,false),
.last 27 (4,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 24 (4,false),
.cycle 22 1 false (2),
.cycle 0 56 true (0),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 22 3 false (4)
])
theorem kid08_part797_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part797) = true := by rfl

def kid08_part798 : Audit := .cycle 0 20 true (0)
theorem kid08_part798_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part798) = true := by rfl

def kid08_part799 : Audit := .cycle 1 19 true (0)
theorem kid08_part799_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part799) = true := by rfl

def kid08_part800 : Audit := .split 40 (4,false) (byMove [
.cycle 20 23 true (3),
.last 68 (5,false),
.cycle 39 2 true (9),
.cycle 0 42 true (0),
.last 42 (5,false),
.cycle 2 40 true (0),
.cycle 0 41 true (0),
.cycle 20 22 true (3),
.cycle 39 9 true (9),
.cycle 3 38 true (0),
.cycle 40 1 true (10),
.last 41 (5,false),
.last 53 (5,false),
.cycle 39 3 true (9),
.last 43 (5,false),
.last 66 (5,false),
.cycle 18 23 true (3),
.cycle 38 3 true (8),
.cycle 0 41 true (0),
.cycle 1 40 true (0),
.cycle 2 39 true (0),
.last 67 (5,false),
.cycle 40 1 true (10),
.last 41 (5,false)
])
theorem kid08_part800_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part800) = true := by rfl

def kid08_part801 : Audit := .cycle 5 40 true (0)
theorem kid08_part801_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part801) = true := by rfl

def kid08_part802 : Audit := .split 20 (4,false) (byMove [
.cycle 18 25 true (3),
.last 32 (5,false),
.cycle 20 2 true (5),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.last 42 (5,false),
.cycle 20 9 true (5),
.last 40 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 6 15 true (0),
.cycle 20 3 true (5),
.last 23 (5,false),
.last 48 (5,false),
.cycle 18 3 true (4),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part802_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part802) = true := by rfl

def kid08_part803 : Audit := .split 20 (5,false) (byMove [
.cycle 43 23 true (9),
.cycle 1 32 true (0),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (4,false),
.cycle 3 38 true (0),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 6 15 true (0),
.last 23 (4,false),
.cycle 0 26 true (0),
.cycle 45 26 true (9),
.cycle 18 3 true (4),
.cycle 19 3 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part803_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part803) = true := by rfl

def kid08_part779 : Audit := .split 19 (5,true) (byMove [(kid08_part780),(kid08_part781),(kid08_part782),(kid08_part783),(kid08_part784),(kid08_part785),(kid08_part786),(kid08_part787),(kid08_part788),(kid08_part789),(kid08_part790),(kid08_part791),(kid08_part792),(kid08_part793),(kid08_part794),(kid08_part795),(kid08_part796),(kid08_part797),(kid08_part798),(kid08_part799),(kid08_part800),(kid08_part801),(kid08_part802),(kid08_part803)])

theorem kid08_part779_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part779) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part780),(kid08_part781),(kid08_part782),(kid08_part783),(kid08_part784),(kid08_part785),(kid08_part786),(kid08_part787),(kid08_part788),(kid08_part789),(kid08_part790),(kid08_part791),(kid08_part792),(kid08_part793),(kid08_part794),(kid08_part795),(kid08_part796),(kid08_part797),(kid08_part798),(kid08_part799),(kid08_part800),(kid08_part801),(kid08_part802),(kid08_part803)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part780_checked

  · exact kid08_part786_checked

  · exact kid08_part792_checked

  · exact kid08_part798_checked

  · exact kid08_part781_checked

  · exact kid08_part787_checked

  · exact kid08_part793_checked

  · exact kid08_part799_checked

  · exact kid08_part782_checked

  · exact kid08_part788_checked

  · exact kid08_part794_checked

  · exact kid08_part800_checked

  · exact kid08_part783_checked

  · exact kid08_part789_checked

  · exact kid08_part795_checked

  · exact kid08_part801_checked

  · exact kid08_part784_checked

  · exact kid08_part790_checked

  · exact kid08_part796_checked

  · exact kid08_part802_checked

  · exact kid08_part785_checked

  · exact kid08_part791_checked

  · exact kid08_part797_checked

  · exact kid08_part803_checked

def kid08_part804 : Audit := .split 22 (4,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 19 12 true (3),
.split 23 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.last 25 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.last 25 (5,false),
.last 24 (5,false),
.cycle 19 12 true (3),
.cycle 20 8 true (4),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 25 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 31 1 false (9),
.cycle 35 1 false (11),
.cycle 22 2 true (5),
.last 24 (5,false)
]),
.cycle 0 23 true (0),
.cycle 49 1 false (13),
.cycle 19 9 true (3),
.cycle 29 1 false (9),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 31 1 false (9),
.cycle 35 1 false (11),
.cycle 22 2 true (6),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 15 29 true (1),
.cycle 37 1 false (11),
.cycle 19 9 true (3),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 19 12 true (3),
.cycle 21 4 true (5),
.cycle 0 26 true (0),
.cycle 29 1 false (9),
.last 25 (5,true),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 49 1 false (13),
.cycle 59 1 false (15),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
]),
.cycle 26 1 false (8),
.cycle 20 3 true (4),
.cycle 28 1 false (8),
.cycle 33 1 false (11),
.cycle 20 5 true (4),
.split 23 (5,true) (byMove [
.cycle 25 5 true (5),
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.last 25 (5,false),
.last 24 (5,false),
.cycle 33 1 false (11),
.cycle 26 1 false (8),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 19 13 true (3),
.last 25 (5,false),
.cycle 20 5 true (4),
.cycle 42 1 false (10),
.cycle 35 1 false (11),
.cycle 24 1 false (4),
.last 25 (5,false),
.last 24 (5,false),
.cycle 51 1 false (13),
.cycle 19 11 true (3),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.last 25 (5,false)
]),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 31 true (1),
.cycle 22 1 true (6),
.split 23 (5,false) (byMove [
.cycle 51 1 false (13),
.cycle 19 11 true (3),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 15 53 true (1),
.cycle 19 10 true (3),
.cycle 3 21 true (0),
.cycle 22 2 true (6),
.cycle 23 1 true (7),
.cycle 39 1 false (11),
.cycle 20 4 true (4),
.cycle 41 1 false (11),
.cycle 15 31 true (1),
.cycle 18 6 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 15 32 true (1),
.cycle 22 2 true (6),
.cycle 23 1 true (7)
])
])
theorem kid08_part804_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part804) = true := by rfl

def kid08_part805 : Audit := .split 24 (4,false) (byMove [
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 23 2 true (5),
.cycle 0 26 true (0),
.cycle 21 8 true (4),
.split 25 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 34 1 false (8),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.last 27 (5,false),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.last 27 (5,false),
.last 26 (5,false),
.cycle 22 12 true (4),
.cycle 22 8 true (4),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.last 27 (5,false),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 33 1 false (9),
.cycle 37 1 false (11),
.cycle 24 2 true (5),
.last 26 (5,false)
]),
.cycle 0 25 true (0),
.cycle 16 28 true (2),
.cycle 22 9 true (4),
.cycle 31 1 false (9),
.cycle 24 1 true (6),
.split 25 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 33 1 false (9),
.cycle 37 1 false (11),
.cycle 24 2 true (6),
.last 27 (5,true),
.cycle 0 26 true (0),
.cycle 16 33 true (2),
.cycle 19 14 true (3),
.cycle 22 9 true (4),
.cycle 24 2 true (6),
.cycle 25 1 true (7),
.cycle 22 12 true (4),
.cycle 23 4 true (5),
.cycle 0 28 true (0),
.cycle 31 1 false (9),
.last 27 (5,true),
.last 27 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 16 28 true (2),
.cycle 16 40 true (2),
.cycle 24 2 true (6),
.cycle 25 1 true (7)
]),
.cycle 28 1 false (8),
.cycle 22 3 true (4),
.cycle 20 5 true (4),
.cycle 35 1 false (11),
.cycle 20 7 true (4),
.split 25 (5,true) (byMove [
.cycle 27 5 true (5),
.cycle 0 29 true (0),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.last 27 (5,false),
.last 26 (5,false),
.cycle 35 1 false (11),
.cycle 28 1 false (8),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 23 5 true (5),
.last 27 (5,false),
.cycle 22 5 true (4),
.cycle 20 7 true (4),
.cycle 37 1 false (11),
.cycle 26 1 false (4),
.last 27 (5,false),
.last 26 (5,false),
.cycle 16 30 true (2),
.cycle 22 11 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 21 5 true (4),
.last 27 (5,false)
]),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 16 35 true (2),
.cycle 24 1 true (6),
.split 25 (5,false) (byMove [
.cycle 16 30 true (2),
.cycle 22 11 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 21 5 true (4),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 16 29 true (2),
.cycle 22 10 true (4),
.cycle 3 23 true (0),
.cycle 24 2 true (6),
.cycle 25 1 true (7),
.cycle 19 16 true (3),
.cycle 22 4 true (4),
.cycle 20 6 true (4),
.cycle 16 35 true (2),
.cycle 18 8 true (3),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 16 36 true (2),
.cycle 24 2 true (6),
.cycle 25 1 true (7)
])
])
theorem kid08_part805_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part805) = true := by rfl

def kid08_part806 : Audit := .cycle 17 2 true (3)
theorem kid08_part806_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part806) = true := by rfl

def kid08_part807 : Audit := .cycle 23 1 false (7)
theorem kid08_part807_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part807) = true := by rfl

def kid08_part808 : Audit := .split 20 (4,false) (byMove [
.cycle 18 8 false (4),
.cycle 14 87 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.split 21 (5,false) (byMove [
.last 51 (5,true),
.cycle 12 12 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.last 28 (5,true),
.cycle 18 7 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (1),
.last 23 (5,true),
.last 104 (5,true),
.last 25 (5,true),
.last 30 (5,true),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.last 28 (5,true),
.cycle 18 8 false (4),
.last 47 (5,true),
.last 37 (5,true),
.last 23 (5,true),
.last 23 (5,true)
]),
.cycle 0 25 true (0),
.cycle 16 34 true (2),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (2),
.split 21 (5,true) (byMove [
.cycle 18 9 false (5),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 25 1 false (7),
.last 25 (5,false),
.last 29 (5,false),
.cycle 32 1 false (10),
.last 29 (5,false),
.last 24 (5,false),
.last 33 (5,false),
.cycle 18 7 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.last 22 (5,false),
.last 64 (5,false),
.last 25 (5,false),
.cycle 18 6 true (2),
.last 52 (5,false),
.cycle 18 4 true (2),
.last 24 (5,false)
]),
.cycle 15 12 true (1),
.cycle 18 6 false (4),
.cycle 36 1 false (8),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.split 21 (5,false) (byMove [
.cycle 18 9 false (4),
.last 29 (5,true),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.last 33 (5,true),
.cycle 16 6 true (1),
.cycle 17 5 false (4),
.last 27 (5,true),
.cycle 19 3 false (3),
.last 22 (5,true),
.last 28 (5,true),
.cycle 18 7 false (4),
.last 37 (5,true),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.last 33 (5,true),
.last 27 (5,true),
.cycle 18 6 false (4),
.last 27 (5,true),
.cycle 18 4 false (4),
.last 22 (5,true)
]),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.cycle 18 5 false (4),
.cycle 5 16 true (0),
.cycle 18 3 false (4),
.split 21 (5,true) (byMove [
.cycle 18 8 true (2),
.cycle 34 1 false (10),
.last 30 (5,false),
.last 27 (5,false),
.cycle 19 3 false (3),
.last 23 (5,false),
.cycle 6 16 true (0),
.last 25 (5,false),
.last 29 (5,false),
.cycle 0 57 true (0),
.last 29 (5,false),
.last 24 (5,false),
.last 33 (5,false),
.cycle 16 6 true (2),
.cycle 17 5 false (4),
.last 27 (5,false),
.cycle 19 3 false (3),
.last 23 (5,false),
.last 64 (5,false),
.last 25 (5,false),
.cycle 18 7 false (5),
.last 52 (5,false),
.cycle 18 5 false (4),
.last 24 (5,false)
])
])
theorem kid08_part808_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part808) = true := by rfl

def kid08_part810 : Audit := .split 28 (4,false) (byMove [
.cycle 21 35 true (3),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 2, 64, 64],[8, 8, 9, 8, 32, 1, 64],96⟩,
.cycle 27 2 true (5),
.cycle 0 30 true (0),
.cycle 23 12 true (3),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 8, 1, 8, 32, 1, 64],112⟩,
.cycle 0 29 true (0),
.cycle 21 34 true (3),
.cycle 27 9 true (5),
.cycle 3 26 true (0),
.cycle 28 1 true (6),
.last 29 (5,false),
.cycle 26 17 true (4),
.cycle 27 3 true (5),
.cycle 22 7 true (3),
.cycle 21 42 true (3),
.cycle 18 11 true (2),
.cycle 24 5 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 21 43 true (3),
.cycle 28 1 true (6),
.last 29 (5,false)
])
theorem kid08_part810_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part810) = true := by rfl

def kid08_part811 : Audit := .cycle 0 57 true (0)
theorem kid08_part811_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part811) = true := by rfl

def kid08_part812 : Audit := .cycle 21 1 false (3)
theorem kid08_part812_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part812) = true := by rfl

def kid08_part813 : Audit := .cycle 20 1 false (2)
theorem kid08_part813_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part813) = true := by rfl

def kid08_part814 : Audit := .split 20 (4,false) (byMove [
.cycle 0 63 true (0),
.cycle 43 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.last 26 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 23 (5,false),
.last 21 (5,false),
.cycle 14 39 true (0),
.cycle 16 16 true (1),
.cycle 0 41 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 1 40 true (0),
.cycle 0 57 true (0),
.cycle 13 39 true (0),
.last 25 (5,false),
.last 21 (5,false)
])
theorem kid08_part814_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part814) = true := by rfl

def kid08_part815 : Audit := .split 20 (5,false) (byMove [
.cycle 0 63 true (0),
.last 40 (4,false),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.cycle 0 30 true (0),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 26 1 true (4),
.cycle 14 39 true (0),
.last 23 (4,false),
.last 26 (4,false),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.last 36 (4,false),
.cycle 0 57 true (0),
.last 26 (4,false),
.last 21 (4,false),
.cycle 34 1 true (0)
])
theorem kid08_part815_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part815) = true := by rfl

def kid08_part816 : Audit := .cycle 23 1 false (7)
theorem kid08_part816_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part816) = true := by rfl

def kid08_part817 : Audit := .split 22 (4,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.last 24 (5,false),
.cycle 32 1 false (10),
.cycle 0 23 true (0),
.cycle 49 1 false (13),
.cycle 20 9 true (4),
.cycle 29 1 false (9),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 26 1 false (8),
.cycle 20 3 true (4),
.cycle 28 1 false (8),
.cycle 33 1 false (11),
.last 24 (5,false),
.cycle 26 1 false (8),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 16 31 true (2),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part817_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part817) = true := by rfl

def kid08_part818 : Audit := .split 24 (4,false) (byMove [
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 23 2 true (5),
.cycle 0 26 true (0),
.last 26 (5,false),
.cycle 27 1 false (7),
.cycle 0 25 true (0),
.cycle 17 28 true (3),
.cycle 23 9 true (5),
.cycle 31 1 false (9),
.cycle 24 1 true (6),
.last 25 (5,false),
.cycle 28 1 false (8),
.cycle 23 3 true (5),
.cycle 20 5 true (4),
.cycle 35 1 false (11),
.last 26 (5,false),
.cycle 22 3 true (4),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.cycle 24 1 true (6),
.last 25 (5,false)
])
theorem kid08_part818_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part818) = true := by rfl

def kid08_part819 : Audit := .cycle 30 1 false (10)
theorem kid08_part819_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part819) = true := by rfl

def kid08_part820 : Audit := .split 21 (5,false) (byMove [
.last 32 (4,false),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 1 false (3),
.cycle 25 1 false (7),
.last 24 (4,false),
.last 28 (4,false),
.cycle 32 1 false (10),
.cycle 20 2 true (3),
.last 26 (4,false),
.last 32 (4,false),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 1 false (3),
.last 63 (4,false),
.last 24 (4,false),
.last 28 (4,false),
.last 51 (4,false),
.cycle 18 4 true (3),
.last 26 (4,false)
])
theorem kid08_part820_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part820) = true := by rfl

def kid08_part821 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.last 23 (4,false),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.last 23 (4,false),
.cycle 22 1 true (6),
.last 33 (4,false),
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.last 23 (4,false),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part821_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part821) = true := by rfl

def kid08_part822 : Audit := .split 28 (4,false) (byMove [
.cycle 16 41 true (2),
.cycle 21 16 true (3),
.cycle 27 2 true (5),
.cycle 0 30 true (0),
.last 30 (5,false),
.cycle 26 12 true (4),
.cycle 0 29 true (0),
.cycle 16 34 true (2),
.cycle 26 9 true (4),
.cycle 16 32 true (2),
.cycle 28 1 true (6),
.last 29 (5,false),
.cycle 6 23 true (0),
.cycle 26 3 true (4),
.cycle 22 7 true (3),
.cycle 16 48 true (2),
.last 30 (5,false),
.cycle 24 5 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 16 43 true (2),
.cycle 28 1 true (6),
.last 29 (5,false)
])
theorem kid08_part822_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part822) = true := by rfl

def kid08_part823 : Audit := .cycle 16 8 true (2)
theorem kid08_part823_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part823) = true := by rfl

def kid08_part824 : Audit := .cycle 25 1 false (7)
theorem kid08_part824_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part824) = true := by rfl

def kid08_part825 : Audit := .cycle 20 1 false (2)
theorem kid08_part825_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part825) = true := by rfl

def kid08_part826 : Audit := .split 20 (4,false) (byMove [
.cycle 18 8 false (4),
.cycle 14 87 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 16 34 true (2),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.last 22 (5,false),
.cycle 19 2 true (2),
.cycle 15 12 true (1),
.last 26 (5,false),
.cycle 36 1 false (8),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.last 25 (5,false),
.cycle 5 16 true (0),
.cycle 18 3 false (4),
.last 23 (5,false)
])
theorem kid08_part826_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part826) = true := by rfl

def kid08_part827 : Audit := .split 20 (5,false) (byMove [
.cycle 19 8 false (4),
.last 46 (4,false),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.last 28 (4,false),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 20 2 true (2),
.cycle 19 2 true (2),
.cycle 15 12 true (1),
.cycle 19 6 false (3),
.last 26 (4,false),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.last 24 (4,false),
.last 28 (4,false),
.cycle 19 5 false (4),
.cycle 5 16 true (0),
.cycle 18 3 false (4),
.cycle 19 3 false (3)
])
theorem kid08_part827_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part827) = true := by rfl

def kid08_part828 : Audit := .split 57 (4,false) (byMove [
.cycle 15 66 true (1),
.cycle 7 51 true (0),
.cycle 56 2 true (12),
.cycle 0 59 true (0),
.last 59 (5,false),
.cycle 0 59 true (0),
.cycle 0 58 true (0),
.cycle 34 24 true (6),
.cycle 54 9 true (10),
.cycle 28 49 true (4),
.cycle 57 1 true (13),
.last 58 (5,false),
.cycle 39 19 true (6),
.cycle 55 3 true (11),
.cycle 30 28 true (6),
.cycle 49 34 true (7),
.last 59 (5,false),
.cycle 32 26 true (6),
.cycle 0 58 true (0),
.cycle 1 57 true (0),
.cycle 2 56 true (0),
.cycle 28 54 true (4),
.cycle 57 1 true (13),
.last 58 (5,false)
])
theorem kid08_part828_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part828) = true := by rfl

def kid08_part829 : Audit := .split 22 (4,false) (byMove [
.cycle 16 29 true (2),
.cycle 47 1 false (11),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.last 24 (5,false),
.cycle 1 23 true (0),
.cycle 0 23 true (0),
.cycle 20 34 true (4),
.cycle 20 9 true (4),
.cycle 16 64 true (2),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 6 17 true (0),
.cycle 20 3 true (4),
.cycle 20 13 true (4),
.cycle 16 84 true (2),
.last 24 (5,false),
.cycle 20 11 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 16 31 true (2),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part829_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part829) = true := by rfl

def kid08_part830 : Audit := .split 24 (4,false) (byMove [
.cycle 17 29 true (3),
.cycle 17 32 true (3),
.cycle 23 2 true (5),
.cycle 0 26 true (0),
.cycle 21 4 true (4),
.cycle 2 24 true (0),
.cycle 0 25 true (0),
.cycle 17 28 true (3),
.cycle 23 9 true (5),
.cycle 3 22 true (0),
.cycle 24 1 true (6),
.last 25 (5,false),
.cycle 20 15 true (4),
.cycle 23 3 true (5),
.cycle 20 5 true (4),
.cycle 17 34 true (3),
.cycle 18 7 true (3),
.cycle 22 3 true (4),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.cycle 24 1 true (6),
.last 25 (5,false)
])
theorem kid08_part830_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part830) = true := by rfl

def kid08_part831 : Audit := .split 47 (4,false) (byMove [
.cycle 14 58 true (0),
.cycle 5 57 true (0),
.cycle 46 2 true (10),
.cycle 0 49 true (0),
.last 49 (5,false),
.cycle 5 77 true (0),
.cycle 0 48 true (0),
.cycle 5 63 true (0),
.cycle 43 9 true (7),
.cycle 0 75 true (0),
.cycle 47 1 true (11),
.last 48 (5,false),
.cycle 27 21 true (3),
.cycle 45 3 true (9),
.cycle 0 52 true (0),
.cycle 5 75 true (0),
.last 49 (5,false),
.cycle 0 50 true (0),
.cycle 0 48 true (0),
.cycle 1 47 true (0),
.cycle 2 46 true (0),
.cycle 20 29 true (3),
.cycle 47 1 true (11),
.last 48 (5,false)
])
theorem kid08_part831_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part831) = true := by rfl

def kid08_part832 : Audit := .cycle 18 2 true (3)
theorem kid08_part832_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part832) = true := by rfl

def kid08_part833 : Audit := .split 22 (5,false) (byMove [
.cycle 19 25 true (3),
.last 32 (4,false),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 20 4 true (4),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 19 24 true (3),
.last 31 (4,false),
.cycle 3 20 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 20 15 true (4),
.last 25 (4,false),
.cycle 20 5 true (4),
.cycle 19 28 true (3),
.cycle 18 5 true (3),
.cycle 20 3 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 19 29 true (3),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part833_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part833) = true := by rfl

def kid08_part809 : Audit := .split 19 (5,true) (byMove [(kid08_part810),(kid08_part811),(kid08_part812),(kid08_part813),(kid08_part814),(kid08_part815),(kid08_part816),(kid08_part817),(kid08_part818),(kid08_part819),(kid08_part820),(kid08_part821),(kid08_part822),(kid08_part823),(kid08_part824),(kid08_part825),(kid08_part826),(kid08_part827),(kid08_part828),(kid08_part829),(kid08_part830),(kid08_part831),(kid08_part832),(kid08_part833)])

theorem kid08_part809_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part809) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid08_part810),(kid08_part811),(kid08_part812),(kid08_part813),(kid08_part814),(kid08_part815),(kid08_part816),(kid08_part817),(kid08_part818),(kid08_part819),(kid08_part820),(kid08_part821),(kid08_part822),(kid08_part823),(kid08_part824),(kid08_part825),(kid08_part826),(kid08_part827),(kid08_part828),(kid08_part829),(kid08_part830),(kid08_part831),(kid08_part832),(kid08_part833)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part810_checked

  · exact kid08_part816_checked

  · exact kid08_part822_checked

  · exact kid08_part828_checked

  · exact kid08_part811_checked

  · exact kid08_part817_checked

  · exact kid08_part823_checked

  · exact kid08_part829_checked

  · exact kid08_part812_checked

  · exact kid08_part818_checked

  · exact kid08_part824_checked

  · exact kid08_part830_checked

  · exact kid08_part813_checked

  · exact kid08_part819_checked

  · exact kid08_part825_checked

  · exact kid08_part831_checked

  · exact kid08_part814_checked

  · exact kid08_part820_checked

  · exact kid08_part826_checked

  · exact kid08_part832_checked

  · exact kid08_part815_checked

  · exact kid08_part821_checked

  · exact kid08_part827_checked

  · exact kid08_part833_checked

def kid08_part834 : Audit := .cycle 0 51 true (0)
theorem kid08_part834_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part834) = true := by rfl

def kid08_part835 : Audit := .split 28 (4,false) (byMove [
.cycle 1 81 true (0),
.cycle 1 55 true (0),
.cycle 27 2 true (7),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.split 29 (5,true) (byMove [
.cycle 0 30 true (0),
.cycle 1 52 true (0),
.cycle 1 39 true (0),
.cycle 39 1 false (5),
.last 31 (5,false),
.last 30 (5,false),
.cycle 0 30 true (0),
.cycle 1 81 true (0),
.cycle 1 55 true (0),
.cycle 9 21 true (0),
.last 31 (5,false),
.last 30 (5,false),
.cycle 19 12 true (4),
.cycle 26 8 true (6),
.cycle 0 32 true (0),
.cycle 1 37 true (0),
.last 31 (5,false),
.last 30 (5,false),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 16 34 true (2),
.cycle 1 61 true (0),
.cycle 28 2 true (7),
.last 30 (5,false)
]),
.cycle 0 29 true (0),
.cycle 26 22 true (6),
.cycle 20 9 true (4),
.cycle 16 32 true (2),
.cycle 28 1 true (8),
.split 29 (5,false) (byMove [
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 16 34 true (2),
.cycle 1 61 true (0),
.cycle 28 2 true (8),
.last 31 (5,true),
.cycle 0 30 true (0),
.cycle 1 52 true (0),
.cycle 1 39 true (0),
.cycle 21 9 true (4),
.cycle 28 2 true (8),
.cycle 29 1 true (9),
.cycle 19 12 true (4),
.cycle 27 4 true (7),
.cycle 0 32 true (0),
.cycle 16 32 true (2),
.last 31 (5,true),
.last 31 (5,true),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 26 22 true (6),
.cycle 16 38 true (2),
.cycle 28 2 true (8),
.cycle 29 1 true (9)
]),
.cycle 1 46 true (0),
.cycle 26 3 true (6),
.cycle 1 30 true (0),
.cycle 1 59 true (0),
.cycle 18 11 true (4),
.split 29 (5,true) (byMove [
.cycle 31 5 true (7),
.cycle 0 33 true (0),
.cycle 10 21 true (0),
.cycle 39 1 false (5),
.last 31 (5,false),
.last 30 (5,false),
.cycle 1 59 true (0),
.cycle 1 46 true (0),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 31 (5,false),
.cycle 26 5 true (6),
.cycle 1 32 true (0),
.cycle 1 61 true (0),
.cycle 11 19 true (0),
.last 31 (5,false),
.last 30 (5,false),
.cycle 26 24 true (6),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 31 (5,false)
]),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 1 54 true (0),
.cycle 28 1 true (8),
.split 29 (5,false) (byMove [
.cycle 26 24 true (6),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 30 (5,true),
.cycle 0 30 true (0),
.cycle 26 23 true (6),
.cycle 20 10 true (4),
.cycle 3 27 true (0),
.cycle 28 2 true (8),
.cycle 29 1 true (9),
.cycle 1 41 true (0),
.cycle 26 4 true (6),
.cycle 1 31 true (0),
.cycle 1 54 true (0),
.cycle 18 12 true (4),
.last 30 (5,true),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 1 55 true (0),
.cycle 28 2 true (8),
.cycle 29 1 true (9)
])
])
theorem kid08_part835_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part835) = true := by rfl

def kid08_part836 : Audit := .split 20 (4,false) (byMove [
.cycle 2 41 true (0),
.cycle 2 44 true (0),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.cycle 2 20 true (0),
.split 21 (5,true) (byMove [
.cycle 2 42 true (0),
.cycle 41 1 false (9),
.cycle 29 1 false (3),
.cycle 0 23 true (0),
.cycle 2 21 true (0),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 2 41 true (0),
.cycle 2 44 true (0),
.cycle 3 19 true (0),
.last 23 (5,false),
.last 22 (5,false),
.cycle 2 32 true (0),
.cycle 19 8 true (4),
.cycle 2 22 true (0),
.cycle 17 27 true (3),
.cycle 18 4 true (4),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 20 2 true (5),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 2 40 true (0),
.cycle 19 9 true (5),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 20 2 true (6),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 2 30 true (0),
.cycle 19 9 true (5),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 40 true (0),
.cycle 2 48 true (0),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 2 31 true (0),
.cycle 19 3 true (5),
.cycle 2 21 true (0),
.cycle 17 26 true (3),
.cycle 18 3 true (4),
.split 21 (5,true) (byMove [
.cycle 19 5 true (4),
.cycle 0 25 true (0),
.cycle 29 1 false (3),
.cycle 0 46 true (0),
.cycle 0 25 true (0),
.last 24 (5,false),
.cycle 17 26 true (3),
.cycle 2 31 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 2 41 true (0),
.last 23 (5,false),
.cycle 23 5 true (5),
.cycle 2 23 true (0),
.cycle 17 5 true (3),
.cycle 5 17 true (0),
.cycle 2 23 true (0),
.last 24 (5,false),
.cycle 2 42 true (0),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 2 21 true (0),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 2 42 true (0),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 2 21 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 2 41 true (0),
.cycle 19 10 true (5),
.cycle 3 19 true (0),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 2 32 true (0),
.cycle 19 4 true (5),
.cycle 2 22 true (0),
.cycle 17 27 true (3),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part836_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part836) = true := by rfl

def kid08_part837 : Audit := .cycle 0 20 true (0)
theorem kid08_part837_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part837) = true := by rfl

def kid08_part838 : Audit := .split 20 (4,false) (byMove [
.cycle 18 23 true (4),
.cycle 18 26 true (3),
.cycle 20 2 true (5),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.split 21 (5,true) (byMove [
.cycle 18 24 true (3),
.cycle 41 1 false (9),
.cycle 29 1 false (3),
.cycle 0 23 true (0),
.last 29 (5,false),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 18 26 true (3),
.cycle 3 19 true (0),
.last 23 (5,false),
.last 22 (5,false),
.cycle 39 1 false (9),
.cycle 20 8 true (4),
.cycle 19 4 true (4),
.cycle 18 27 true (3),
.cycle 18 4 true (4),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (5),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 18 22 true (4),
.cycle 20 9 true (5),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (6),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 18 25 true (4),
.cycle 19 12 true (5),
.cycle 20 9 true (5),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 18 22 true (4),
.cycle 18 30 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 19 13 true (4),
.cycle 20 3 true (5),
.cycle 19 3 true (5),
.cycle 18 26 true (4),
.cycle 18 3 true (4),
.split 21 (5,true) (byMove [
.cycle 20 5 true (4),
.cycle 0 25 true (0),
.cycle 29 1 false (3),
.cycle 72 1 false (12),
.last 29 (5,false),
.last 24 (5,false),
.cycle 18 26 true (4),
.cycle 19 13 true (4),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 23 (5,false),
.cycle 23 5 true (5),
.cycle 19 5 true (4),
.cycle 17 5 true (3),
.cycle 5 17 true (0),
.cycle 18 5 true (4),
.last 24 (5,false),
.cycle 18 24 true (4),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 18 24 true (4),
.cycle 20 11 true (5),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.cycle 19 3 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.cycle 3 19 true (0),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 19 14 true (5),
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.cycle 18 27 true (4),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid08_part838_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part838) = true := by rfl

def kid08_part840 : Audit := .split 44 (4,false) (byMove [
.cycle 20 25 true (3),
.last 74 (5,false),
.cycle 43 2 true (9),
.cycle 0 46 true (0),
.last 46 (5,false),
.last 72 (5,false),
.cycle 0 45 true (0),
.cycle 21 24 true (3),
.cycle 43 9 true (9),
.cycle 3 42 true (0),
.cycle 44 1 true (10),
.last 45 (5,false),
.last 57 (5,false),
.cycle 43 3 true (9),
.last 47 (5,false),
.last 72 (5,false),
.cycle 18 27 true (3),
.cycle 40 5 true (7),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 2 43 true (0),
.last 73 (5,false),
.cycle 44 1 true (10),
.last 45 (5,false)
])
theorem kid08_part840_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part840) = true := by rfl

def kid08_part841 : Audit := .split 29 (4,false) (byMove [
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.cycle 28 2 true (6),
.cycle 0 31 true (0),
.last 31 (5,false),
.cycle 39 1 false (9),
.cycle 0 30 true (0),
.cycle 0 53 true (0),
.cycle 21 9 true (3),
.cycle 36 1 false (10),
.cycle 29 1 true (7),
.last 30 (5,false),
.cycle 33 1 false (9),
.cycle 27 3 true (5),
.last 32 (5,false),
.cycle 40 1 false (12),
.cycle 34 1 false (8),
.cycle 0 34 true (0),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 25 58 true (3),
.cycle 29 1 true (7),
.last 30 (5,false)
])
theorem kid08_part841_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part841) = true := by rfl

def kid08_part842 : Audit := .split 21 (4,false) (byMove [
.cycle 20 27 true (3),
.cycle 34 1 false (8),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.last 23 (5,false),
.cycle 27 1 false (3),
.cycle 0 22 true (0),
.last 55 (5,false),
.cycle 20 9 true (4),
.cycle 3 19 true (0),
.cycle 21 1 true (5),
.last 22 (5,false),
.last 34 (5,false),
.cycle 20 3 true (4),
.last 24 (5,false),
.cycle 5 83 true (0),
.cycle 18 4 true (4),
.cycle 27 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 21 1 true (5),
.last 22 (5,false)
])
theorem kid08_part842_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part842) = true := by rfl

def kid08_part843 : Audit := .cycle 0 21 true (0)
theorem kid08_part843_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part843) = true := by rfl

def kid08_part844 : Audit := .split 21 (5,false) (byMove [
.last 48 (4,false),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 20 2 true (4),
.last 26 (4,false),
.cycle 0 22 true (0),
.cycle 20 34 true (4),
.last 30 (4,false),
.cycle 3 19 true (0),
.last 22 (4,false),
.cycle 21 1 true (5),
.cycle 20 13 true (3),
.last 24 (4,false),
.cycle 20 3 true (4),
.last 51 (4,false),
.cycle 18 4 true (4),
.last 26 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 21 1 true (5)
])
theorem kid08_part844_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part844) = true := by rfl

def kid08_part845 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 22 1 false (2),
.cycle 0 23 true (0),
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 22 1 true (2),
.last 33 (4,false),
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 22 1 false (2),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (6),
.cycle 34 1 false (8),
.last 23 (4,false),
.cycle 22 1 true (2)
])
theorem kid08_part845_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part845) = true := by rfl

def kid08_part846 : Audit := .cycle 0 20 true (0)
theorem kid08_part846_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part846) = true := by rfl

def kid08_part847 : Audit := .split 51 (5,false) (byMove [
.cycle 20 33 true (4),
.last 61 (4,false),
.last 53 (4,false),
.cycle 0 53 true (0),
.cycle 50 2 true (12),
.cycle 19 33 true (4),
.cycle 0 52 true (0),
.cycle 20 32 true (4),
.last 60 (4,false),
.cycle 3 49 true (0),
.last 52 (4,false),
.cycle 51 1 true (13),
.cycle 40 13 true (8),
.last 54 (4,false),
.cycle 49 3 true (11),
.last 77 (4,false),
.cycle 18 34 true (4),
.cycle 39 13 true (8),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.last 78 (4,false),
.last 52 (4,false),
.cycle 51 1 true (13)
])
theorem kid08_part847_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part847) = true := by rfl

def kid08_part848 : Audit := .split 28 (4,false) (byMove [
.last 82 (5,false),
.last 56 (5,false),
.cycle 27 2 true (7),
.cycle 0 30 true (0),
.last 30 (5,false),
.last 56 (5,false),
.cycle 0 29 true (0),
.cycle 27 22 true (7),
.cycle 20 9 true (4),
.cycle 17 32 true (3),
.cycle 28 1 true (8),
.last 29 (5,false),
.last 47 (5,false),
.cycle 26 3 true (6),
.last 31 (5,false),
.last 60 (5,false),
.cycle 18 11 true (4),
.cycle 27 3 true (7),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.last 55 (5,false),
.cycle 28 1 true (8),
.last 29 (5,false)
])
theorem kid08_part848_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part848) = true := by rfl

def kid08_part849 : Audit := .cycle 3 17 true (0)
theorem kid08_part849_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part849) = true := by rfl

def kid08_part850 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 76 (5,false),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 18 24 true (4),
.last 31 (5,false),
.last 52 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 18 30 true (4),
.cycle 22 3 true (6),
.cycle 0 23 true (0),
.cycle 4 17 true (0),
.last 25 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 41 (5,false),
.last 49 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part850_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part850) = true := by rfl

def kid08_part851 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 55 (4,false),
.last 21 (4,false),
.cycle 26 1 false (4),
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8521760, 16777216, 2, 128, 256, 32768, 524290, 16777216, 8192, 128, 256, 2097152, 4, 16777216, 524288, 128, 256, 8, 1024, 16777216, 2, 16777216],[2, 4, 1024, 1, 2048, 32, 8192, 16384, 1024, 4096, 2048, 131072, 524288, 1048576, 1024, 262144, 2048, 8388608, 2, 4, 1024, 1, 2048, 32, 16777216],23151632⟩,
.last 40 (4,false),
.last 28 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 31 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 4 17 true (0),
.last 21 (4,false),
.cycle 34 1 false (8),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8521760, 16777216, 256, 128, 256, 32768, 524290, 16777216, 256, 128, 256, 2097152, 4, 16777216, 256, 128, 256, 8, 1024, 16777216, 256, 16777216],[2, 4, 1024, 1, 2048, 32, 8192, 16384, 1024, 4096, 2048, 131072, 524288, 1048576, 1024, 262144, 2048, 8388608, 2, 4, 1024, 1, 2048, 32, 16777216],23151632⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8521760, 16777216, 512, 128, 256, 32768, 524290, 16777216, 512, 128, 256, 2097152, 4, 16777216, 512, 128, 256, 8, 1024, 16777216, 512, 16777216],[2, 4, 1024, 1, 2048, 32, 8192, 16384, 1024, 4096, 2048, 131072, 524288, 1048576, 1024, 262144, 2048, 8388608, 2, 4, 1024, 1, 2048, 32, 16777216],23151632⟩,
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part851_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part851) = true := by rfl

def kid08_part852 : Audit := .split 32 (5,false) (byMove [
.last 57 (4,false),
.last 42 (4,false),
.last 34 (4,false),
.cycle 0 34 true (0),
.cycle 31 2 true (7),
.cycle 37 1 false (9),
.cycle 0 33 true (0),
.last 56 (4,false),
.last 41 (4,false),
.cycle 3 30 true (0),
.last 33 (4,false),
.cycle 32 1 true (8),
.cycle 20 13 true (3),
.last 35 (4,false),
.cycle 30 3 true (6),
.cycle 28 28 true (4),
.cycle 18 15 true (3),
.last 37 (4,false),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 2 31 true (0),
.cycle 28 29 true (4),
.last 33 (4,false),
.cycle 32 1 true (8)
])
theorem kid08_part852_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part852) = true := by rfl

def kid08_part853 : Audit := .split 22 (4,false) (byMove [
.cycle 16 29 true (2),
.last 34 (5,false),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.last 24 (5,false),
.cycle 19 8 true (4),
.cycle 0 23 true (0),
.last 46 (5,false),
.cycle 20 9 true (4),
.last 44 (5,false),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 6 17 true (0),
.cycle 20 3 true (4),
.last 25 (5,false),
.last 54 (5,false),
.cycle 18 5 true (4),
.last 27 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 16 31 true (2),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part853_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part853) = true := by rfl

def kid08_part854 : Audit := .split 22 (5,false) (byMove [
.cycle 17 27 true (3),
.last 32 (4,false),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 21 2 true (5),
.cycle 19 4 true (4),
.cycle 0 23 true (0),
.cycle 17 26 true (3),
.last 31 (4,false),
.cycle 3 20 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 20 13 true (4),
.last 25 (4,false),
.cycle 20 3 true (4),
.cycle 17 32 true (3),
.cycle 18 5 true (4),
.cycle 17 7 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 33 true (3),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part854_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part854) = true := by rfl

def kid08_part855 : Audit := .split 47 (4,false) (byMove [
.cycle 14 58 true (0),
.cycle 5 57 true (0),
.cycle 46 2 true (10),
.cycle 0 49 true (0),
.last 49 (5,false),
.last 57 (5,false),
.cycle 0 48 true (0),
.cycle 5 63 true (0),
.cycle 43 9 true (7),
.last 73 (5,false),
.cycle 47 1 true (11),
.last 48 (5,false),
.cycle 27 21 true (3),
.cycle 45 3 true (9),
.last 50 (5,false),
.cycle 5 75 true (0),
.cycle 5 77 true (0),
.cycle 11 38 true (0),
.cycle 0 48 true (0),
.cycle 1 47 true (0),
.cycle 2 46 true (0),
.cycle 20 29 true (3),
.cycle 47 1 true (11),
.last 48 (5,false)
])
theorem kid08_part855_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part855) = true := by rfl

def kid08_part856 : Audit := .cycle 18 2 true (4)
theorem kid08_part856_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part856) = true := by rfl

def kid08_part857 : Audit := .split 22 (5,false) (byMove [
.cycle 19 10 false (5),
.last 50 (4,false),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 22 1 false (2),
.last 26 (4,false),
.cycle 16 34 true (2),
.cycle 17 6 true (2),
.cycle 27 1 false (7),
.cycle 20 4 true (2),
.cycle 21 2 true (2),
.cycle 15 16 true (1),
.cycle 19 8 false (5),
.last 28 (4,false),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 22 1 false (2),
.last 26 (4,false),
.cycle 1 26 true (0),
.cycle 19 7 false (5),
.cycle 5 18 true (0),
.cycle 18 5 false (5),
.cycle 20 3 false (4)
])
theorem kid08_part857_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part857) = true := by rfl

def kid08_part858 : Audit := .cycle 0 20 true (0)
theorem kid08_part858_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part858) = true := by rfl

def kid08_part859 : Audit := .cycle 1 19 true (0)
theorem kid08_part859_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part859) = true := by rfl

def kid08_part860 : Audit := .cycle 2 18 true (0)
theorem kid08_part860_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part860) = true := by rfl

def kid08_part861 : Audit := .cycle 21 23 true (4)
theorem kid08_part861_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part861) = true := by rfl

def kid08_part862 : Audit := .split 20 (4,false) (byMove [
.last 43 (5,false),
.last 46 (5,false),
.cycle 20 2 true (5),
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.last 42 (5,false),
.cycle 20 9 true (5),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 33 (5,false),
.cycle 20 3 true (5),
.last 23 (5,false),
.cycle 18 26 true (4),
.cycle 18 3 true (4),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part862_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part862) = true := by rfl

def kid08_part863 : Audit := .split 20 (5,false) (byMove [
.cycle 19 23 true (4),
.last 30 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 20 2 true (5),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (4,false),
.cycle 3 18 true (0),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 20 13 true (4),
.last 23 (4,false),
.cycle 20 3 true (5),
.cycle 19 26 true (4),
.cycle 18 3 true (4),
.cycle 19 3 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part863_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part863) = true := by rfl

def kid08_part839 : Audit := .split 19 (5,true) (byMove [(kid08_part840),(kid08_part841),(kid08_part842),(kid08_part843),(kid08_part844),(kid08_part845),(kid08_part846),(kid08_part847),(kid08_part848),(kid08_part849),(kid08_part850),(kid08_part851),(kid08_part852),(kid08_part853),(kid08_part854),(kid08_part855),(kid08_part856),(kid08_part857),(kid08_part858),(kid08_part859),(kid08_part860),(kid08_part861),(kid08_part862),(kid08_part863)])

theorem kid08_part839_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part839) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part840),(kid08_part841),(kid08_part842),(kid08_part843),(kid08_part844),(kid08_part845),(kid08_part846),(kid08_part847),(kid08_part848),(kid08_part849),(kid08_part850),(kid08_part851),(kid08_part852),(kid08_part853),(kid08_part854),(kid08_part855),(kid08_part856),(kid08_part857),(kid08_part858),(kid08_part859),(kid08_part860),(kid08_part861),(kid08_part862),(kid08_part863)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part840_checked

  · exact kid08_part846_checked

  · exact kid08_part852_checked

  · exact kid08_part858_checked

  · exact kid08_part841_checked

  · exact kid08_part847_checked

  · exact kid08_part853_checked

  · exact kid08_part859_checked

  · exact kid08_part842_checked

  · exact kid08_part848_checked

  · exact kid08_part854_checked

  · exact kid08_part860_checked

  · exact kid08_part843_checked

  · exact kid08_part849_checked

  · exact kid08_part855_checked

  · exact kid08_part861_checked

  · exact kid08_part844_checked

  · exact kid08_part850_checked

  · exact kid08_part856_checked

  · exact kid08_part862_checked

  · exact kid08_part845_checked

  · exact kid08_part851_checked

  · exact kid08_part857_checked

  · exact kid08_part863_checked

def kid08_part743 : Audit := .split 18 (4,true) (byMove [(kid08_part744),(kid08_part745),(kid08_part746),(kid08_part747),(kid08_part748),(kid08_part749),(kid08_part774),(kid08_part775),(kid08_part776),(kid08_part777),(kid08_part778),(kid08_part779),(kid08_part804),(kid08_part805),(kid08_part806),(kid08_part807),(kid08_part808),(kid08_part809),(kid08_part834),(kid08_part835),(kid08_part836),(kid08_part837),(kid08_part838),(kid08_part839)])

theorem kid08_part743_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (kid08_part743) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part744),(kid08_part745),(kid08_part746),(kid08_part747),(kid08_part748),(kid08_part749),(kid08_part774),(kid08_part775),(kid08_part776),(kid08_part777),(kid08_part778),(kid08_part779),(kid08_part804),(kid08_part805),(kid08_part806),(kid08_part807),(kid08_part808),(kid08_part809),(kid08_part834),(kid08_part835),(kid08_part836),(kid08_part837),(kid08_part838),(kid08_part839)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part744_checked

  · exact kid08_part774_checked

  · exact kid08_part804_checked

  · exact kid08_part834_checked

  · exact kid08_part745_checked

  · exact kid08_part775_checked

  · exact kid08_part805_checked

  · exact kid08_part835_checked

  · exact kid08_part746_checked

  · exact kid08_part776_checked

  · exact kid08_part806_checked

  · exact kid08_part836_checked

  · exact kid08_part747_checked

  · exact kid08_part777_checked

  · exact kid08_part807_checked

  · exact kid08_part837_checked

  · exact kid08_part748_checked

  · exact kid08_part778_checked

  · exact kid08_part808_checked

  · exact kid08_part838_checked

  · exact kid08_part749_checked

  · exact kid08_part779_checked

  · exact kid08_part809_checked

  · exact kid08_part839_checked

def kid08_part865 : Audit := .split 22 (5,false) (byMove [
.cycle 23 24 true (4),
.cycle 35 1 false (9),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.split 23 (4,true) (byMove [
.cycle 33 1 false (9),
.cycle 26 1 false (6),
.cycle 28 1 false (4),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 24 true (4),
.cycle 35 1 false (9),
.cycle 30 1 false (8),
.last 24 (4,false),
.last 25 (4,false),
.cycle 27 1 false (7),
.cycle 20 8 true (4),
.cycle 35 1 false (9),
.cycle 34 1 false (10),
.last 25 (4,false),
.cycle 18 12 true (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.last 24 (4,false),
.cycle 22 2 true (5)
]),
.cycle 33 1 false (9),
.cycle 0 23 true (0),
.cycle 23 24 true (5),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.last 25 (4,true),
.cycle 22 2 true (6),
.cycle 0 24 true (0),
.cycle 17 29 true (3),
.cycle 17 46 true (3),
.cycle 21 9 true (5),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 21 12 true (5),
.cycle 20 4 true (4),
.cycle 0 26 true (0),
.cycle 4 20 true (0),
.last 25 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 24 24 true (5),
.cycle 50 24 true (10),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6),
.cycle 44 1 false (12),
.cycle 21 3 true (5),
.cycle 23 24 true (4),
.cycle 17 30 true (3),
.split 23 (4,true) (byMove [
.cycle 19 5 true (3),
.cycle 0 27 true (0),
.cycle 28 1 false (4),
.cycle 37 1 false (7),
.last 25 (4,false),
.cycle 0 29 true (0),
.cycle 17 30 true (3),
.cycle 44 1 false (12),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 25 5 true (5),
.cycle 36 1 false (10),
.cycle 17 7 true (3),
.cycle 28 1 false (8),
.last 25 (4,false),
.cycle 26 24 true (4),
.cycle 24 24 true (5),
.cycle 21 11 true (5),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 24 24 true (4)
]),
.cycle 18 5 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.split 23 (4,false) (byMove [
.cycle 24 24 true (5),
.cycle 21 11 true (5),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 24 24 true (4),
.cycle 0 24 true (0),
.cycle 24 24 true (6),
.cycle 21 10 true (5),
.cycle 3 21 true (0),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 17 48 true (3),
.cycle 21 4 true (5),
.cycle 24 24 true (5),
.cycle 17 31 true (3),
.last 24 (4,true),
.cycle 18 6 true (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 17 32 true (3),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6)
])
theorem kid08_part865_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid08_part865) = true := by rfl

def kid08_part866 : Audit := .cycle 0 22 true (0)
theorem kid08_part866_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid08_part866) = true := by rfl

def kid08_part867 : Audit := .split 20 (5,false) (byMove [
.cycle 23 28 true (4),
.cycle 0 24 true (0),
.cycle 19 2 true (3),
.cycle 0 34 true (0),
.split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 40 1 false (8),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 0 34 true (0),
.cycle 23 28 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 22 (4,false),
.last 23 (4,false),
.cycle 0 26 true (0),
.cycle 19 8 true (2),
.cycle 0 38 true (0),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 0 34 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 22 (4,false),
.cycle 20 2 true (3)
]),
.cycle 23 1 false (3),
.cycle 0 48 true (0),
.cycle 32 24 true (6),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 22 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 48 (4,false),
.last 34 (4,false),
.last 30 (4,false),
.last 22 (4,false),
.last 23 (4,false),
.last 33 (4,false),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 22 (4,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 45 (4,false),
.cycle 5 44 true (0),
.last 22 (4,false),
.last 23 (4,false)
]),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.cycle 24 3 true (4),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.split 21 (4,true) (byMove [
.cycle 26 5 true (3),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 25 1 false (7),
.cycle 28 1 false (8),
.cycle 24 3 true (4),
.cycle 32 1 false (10),
.last 24 (4,false),
.cycle 24 1 false (4),
.cycle 26 5 true (3),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 34 28 true (6),
.cycle 22 11 true (4),
.cycle 24 3 true (4),
.cycle 0 54 true (0),
.last 24 (4,false),
.cycle 18 4 true (3)
]),
.cycle 23 1 false (3),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.last 49 (4,false),
.last 32 (4,false),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 24 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.last 57 (4,false),
.last 31 (4,false),
.cycle 3 19 true (0),
.last 22 (4,false),
.last 23 (4,false),
.last 36 (4,false),
.last 25 (4,false),
.last 26 (4,false),
.last 52 (4,false),
.last 24 (4,false),
.cycle 18 4 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.last 23 (4,false)
]),
.cycle 23 1 true (5)
])
theorem kid08_part867_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid08_part867) = true := by rfl

def kid08_part868 : Audit := .split 30 (5,false) (byMove [
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.split 31 (4,true) (byMove [
.cycle 0 32 true (0),
.cycle 40 1 false (10),
.cycle 33 1 false (7),
.cycle 32 1 false (6),
.last 32 (4,false),
.last 33 (4,false),
.cycle 0 32 true (0),
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.cycle 32 1 false (8),
.last 32 (4,false),
.last 33 (4,false),
.cycle 20 12 true (4),
.cycle 28 8 true (6),
.cycle 0 34 true (0),
.cycle 32 1 false (6),
.last 32 (4,false),
.last 33 (4,false),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 39 1 false (11),
.cycle 43 1 false (13),
.last 32 (4,false),
.cycle 30 2 true (7)
]),
.cycle 32 1 false (6),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 37 1 false (11),
.split 31 (4,false) (byMove [
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 39 1 false (11),
.cycle 43 1 false (13),
.last 33 (4,true),
.cycle 30 2 true (8),
.cycle 0 32 true (0),
.cycle 0 58 true (0),
.cycle 0 43 true (0),
.cycle 23 9 true (4),
.cycle 31 1 true (9),
.cycle 30 2 true (8),
.cycle 20 12 true (4),
.cycle 29 4 true (7),
.cycle 0 34 true (0),
.cycle 37 1 false (11),
.last 33 (4,true),
.last 33 (4,true),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 28 24 true (6),
.cycle 16 42 true (2),
.cycle 31 1 true (9),
.cycle 30 2 true (8)
]),
.cycle 30 1 true (8),
.cycle 34 1 false (10),
.cycle 28 3 true (6),
.cycle 0 34 true (0),
.cycle 41 1 false (13),
.split 31 (4,true) (byMove [
.cycle 33 5 true (7),
.cycle 0 35 true (0),
.cycle 33 1 false (7),
.cycle 32 1 false (6),
.last 32 (4,false),
.last 33 (4,false),
.cycle 41 1 false (13),
.cycle 34 1 false (10),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.last 33 (4,false),
.cycle 33 1 false (7),
.cycle 28 5 true (6),
.cycle 0 36 true (0),
.cycle 43 1 false (13),
.cycle 32 1 false (6),
.last 32 (4,false),
.last 33 (4,false),
.cycle 28 26 true (6),
.cycle 21 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.last 33 (4,false),
.cycle 0 34 true (0)
]),
.cycle 32 1 false (6),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.split 31 (4,false) (byMove [
.cycle 28 26 true (6),
.cycle 21 11 true (4),
.cycle 29 3 true (7),
.cycle 0 33 true (0),
.last 32 (4,true),
.cycle 0 34 true (0),
.cycle 0 32 true (0),
.cycle 28 25 true (6),
.cycle 22 10 true (4),
.cycle 3 29 true (0),
.cycle 31 1 true (9),
.cycle 30 2 true (8),
.cycle 0 45 true (0),
.cycle 28 4 true (6),
.cycle 0 35 true (0),
.cycle 0 60 true (0),
.last 32 (4,true),
.cycle 18 14 true (3),
.cycle 0 32 true (0),
.cycle 1 31 true (0),
.cycle 2 30 true (0),
.cycle 0 61 true (0),
.cycle 31 1 true (9),
.cycle 30 2 true (8)
]),
.cycle 30 1 true (8)
])
theorem kid08_part868_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid08_part868) = true := by rfl

def kid08_part870 : Audit := .cycle 0 24 true (0)
theorem kid08_part870_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part870) = true := by rfl

def kid08_part871 : Audit := .split 28 (5,false) (byMove [
.cycle 38 1 false (10),
.cycle 31 1 false (7),
.cycle 27 2 true (5),
.cycle 0 30 true (0),
.cycle 38 1 false (8),
.last 30 (4,false),
.cycle 0 29 true (0),
.cycle 67 1 false (13),
.cycle 22 9 true (2),
.cycle 35 1 false (9),
.last 29 (4,false),
.cycle 28 1 true (6),
.cycle 32 1 false (8),
.cycle 26 3 true (4),
.cycle 40 1 false (8),
.cycle 39 1 false (11),
.cycle 0 33 true (0),
.last 30 (4,false),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 12 43 true (0),
.last 29 (4,false),
.cycle 28 1 true (6)
])
theorem kid08_part871_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part871) = true := by rfl

def kid08_part872 : Audit := .cycle 21 1 false (3)
theorem kid08_part872_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part872) = true := by rfl

def kid08_part873 : Audit := .cycle 20 1 false (2)
theorem kid08_part873_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part873) = true := by rfl

def kid08_part874 : Audit := .split 20 (4,false) (byMove [
.last 30 (5,false),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.last 21 (5,false),
.last 44 (5,false),
.last 23 (5,false),
.last 26 (5,false),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.last 28 (5,false),
.last 26 (5,false),
.cycle 27 1 true (1),
.last 21 (5,false)
])
theorem kid08_part874_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part874) = true := by rfl

def kid08_part875 : Audit := .split 20 (5,false) (byMove [
.cycle 12 59 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 24 (4,false),
.cycle 48 1 false (8),
.cycle 33 3 true (3),
.cycle 0 35 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 2 27 true (0),
.last 60 (4,false),
.last 21 (4,false),
.cycle 27 1 true (1)
])
theorem kid08_part875_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part875) = true := by rfl

def kid08_part876 : Audit := .split 30 (5,false) (byMove [
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.cycle 0 32 true (0),
.last 32 (4,false),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 37 1 false (11),
.last 31 (4,false),
.cycle 30 1 true (8),
.cycle 34 1 false (10),
.cycle 28 3 true (6),
.cycle 0 34 true (0),
.cycle 41 1 false (13),
.cycle 41 1 false (13),
.last 32 (4,false),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.last 31 (4,false),
.cycle 30 1 true (8)
])
theorem kid08_part876_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part876) = true := by rfl

def kid08_part877 : Audit := .split 22 (5,false) (byMove [
.cycle 24 24 true (4),
.cycle 35 1 false (9),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 23 24 true (4),
.cycle 33 1 false (9),
.cycle 0 23 true (0),
.cycle 23 24 true (5),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 44 1 false (12),
.cycle 21 3 true (5),
.cycle 23 24 true (4),
.cycle 17 30 true (3),
.cycle 44 1 false (12),
.cycle 18 5 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part877_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part877) = true := by rfl

def kid08_part878 : Audit := .cycle 0 22 true (0)
theorem kid08_part878_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part878) = true := by rfl

def kid08_part879 : Audit := .cycle 20 1 false (4)
theorem kid08_part879_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part879) = true := by rfl

def kid08_part880 : Audit := .split 20 (4,false) (byMove [
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 24 (5,false)
])
theorem kid08_part880_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part880) = true := by rfl

def kid08_part881 : Audit := .split 20 (5,false) (byMove [
.cycle 0 53 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 22 (4,false),
.cycle 6 19 true (0),
.cycle 27 3 true (5),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 20 1 false (4),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 23 1 true (5)
])
theorem kid08_part881_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part881) = true := by rfl

def kid08_part882 : Audit := .cycle 0 24 true (0)
theorem kid08_part882_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part882) = true := by rfl

def kid08_part883 : Audit := .split 22 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 1, 64],[8, 8, 10, 8, 2, 16, 64],80⟩,
.cycle 0 26 true (0),
.cycle 21 2 true (3),
.cycle 0 36 true (0),
.cycle 19 8 true (2),
.cycle 18 5 false (4),
.cycle 0 52 true (0),
.cycle 36 26 true (6),
.cycle 23 9 true (5),
.cycle 0 24 true (0),
.last 27 (4,false),
.last 24 (4,false),
.cycle 45 16 true (5),
.cycle 28 3 true (4),
.cycle 17 12 true (2),
.cycle 5 18 true (0),
.cycle 16 8 true (2),
.cycle 18 5 false (4),
.cycle 0 63 true (0),
.cycle 1 32 true (0),
.cycle 2 23 true (0),
.cycle 0 24 true (0),
.last 27 (4,false),
.cycle 27 1 true (5)
])
theorem kid08_part883_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part883) = true := by rfl

def kid08_part884 : Audit := .split 32 (5,false) (byMove [
.cycle 42 1 false (12),
.cycle 35 1 false (9),
.cycle 31 2 true (7),
.cycle 0 34 true (0),
.cycle 0 36 true (0),
.last 34 (4,false),
.cycle 0 33 true (0),
.cycle 30 26 true (6),
.cycle 24 9 true (4),
.cycle 39 1 false (11),
.last 33 (4,false),
.cycle 32 1 true (8),
.cycle 36 1 false (10),
.cycle 30 3 true (6),
.cycle 0 38 true (0),
.cycle 43 1 false (13),
.cycle 45 1 false (13),
.last 34 (4,false),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 2 31 true (0),
.cycle 0 66 true (0),
.last 33 (4,false),
.cycle 32 1 true (8)
])
theorem kid08_part884_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part884) = true := by rfl

def kid08_part885 : Audit := .cycle 20 1 false (2)
theorem kid08_part885_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part885) = true := by rfl

def kid08_part886 : Audit := .split 20 (4,false) (byMove [
.last 24 (5,false),
.last 34 (5,false),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.last 22 (5,false),
.last 32 (5,false),
.cycle 19 2 true (2),
.last 23 (5,false),
.last 24 (5,false),
.cycle 19 6 false (3),
.last 26 (5,false),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.last 22 (5,false),
.last 32 (5,false),
.cycle 19 3 false (3),
.cycle 18 3 false (4)
])
theorem kid08_part886_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part886) = true := by rfl

def kid08_part887 : Audit := .split 20 (5,false) (byMove [
.last 61 (4,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 2191, 262144, 8, 8192, 16384, 8, 2, 262144, 8, 128, 256, 8, 2, 262144, 8, 262144],[2, 4, 2048, 1, 1, 262144, 2, 4, 131072, 1, 262144, 136, 2, 4, 2048, 1, 5, 262144, 262144],328720⟩,
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 23 9 true (5),
.cycle 39 1 false (11),
.cycle 19 2 true (2),
.last 22 (4,false),
.cycle 15 35 true (1),
.last 26 (4,false),
.last 31 (4,false),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 2 23 true (0),
.cycle 0 66 true (0),
.last 23 (4,false),
.cycle 18 3 false (4)
])
theorem kid08_part887_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part887) = true := by rfl

def kid08_part888 : Audit := .split 30 (5,false) (byMove [
.cycle 0 91 true (0),
.cycle 0 61 true (0),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.cycle 0 32 true (0),
.last 32 (4,false),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 16 36 true (2),
.last 31 (4,false),
.cycle 30 1 true (8),
.cycle 0 52 true (0),
.cycle 28 3 true (6),
.cycle 0 34 true (0),
.cycle 0 67 true (0),
.cycle 28 26 true (6),
.last 32 (4,false),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.last 31 (4,false),
.cycle 30 1 true (8)
])
theorem kid08_part888_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part888) = true := by rfl

def kid08_part889 : Audit := .split 22 (5,false) (byMove [
.cycle 1 47 true (0),
.cycle 1 50 true (0),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 1 24 true (0),
.cycle 0 23 true (0),
.cycle 1 46 true (0),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 1 35 true (0),
.cycle 21 3 true (5),
.cycle 1 25 true (0),
.cycle 17 30 true (3),
.cycle 21 11 true (5),
.cycle 18 5 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part889_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part889) = true := by rfl

def kid08_part890 : Audit := .cycle 0 22 true (0)
theorem kid08_part890_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part890) = true := by rfl

def kid08_part891 : Audit := .cycle 25 1 false (7)
theorem kid08_part891_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part891) = true := by rfl

def kid08_part892 : Audit := .split 20 (4,false) (byMove [
.last 24 (5,false),
.cycle 0 24 true (0),
.last 22 (5,false),
.last 32 (5,false),
.cycle 19 2 true (3),
.last 23 (5,false),
.last 47 (5,false),
.last 57 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 22 3 true (4),
.last 23 (5,false),
.cycle 0 57 true (0),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.last 24 (5,false)
])
theorem kid08_part892_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part892) = true := by rfl

def kid08_part893 : Audit := .split 20 (5,false) (byMove [
.cycle 24 28 true (4),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.cycle 0 34 true (0),
.cycle 19 2 true (3),
.last 22 (4,false),
.cycle 0 48 true (0),
.cycle 33 24 true (6),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 22 (4,false),
.cycle 28 1 false (8),
.cycle 25 3 true (4),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 18 4 true (3),
.last 22 (4,false),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.last 23 (4,false),
.cycle 23 1 true (5)
])
theorem kid08_part893_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part893) = true := by rfl

def kid08_part869 : Audit := .split 19 (4,true) (byMove [(kid08_part870),(kid08_part871),(kid08_part872),(kid08_part873),(kid08_part874),(kid08_part875),(kid08_part876),(kid08_part877),(kid08_part878),(kid08_part879),(kid08_part880),(kid08_part881),(kid08_part882),(kid08_part883),(kid08_part884),(kid08_part885),(kid08_part886),(kid08_part887),(kid08_part888),(kid08_part889),(kid08_part890),(kid08_part891),(kid08_part892),(kid08_part893)])

theorem kid08_part869_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid08_part869) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid08_part870),(kid08_part871),(kid08_part872),(kid08_part873),(kid08_part874),(kid08_part875),(kid08_part876),(kid08_part877),(kid08_part878),(kid08_part879),(kid08_part880),(kid08_part881),(kid08_part882),(kid08_part883),(kid08_part884),(kid08_part885),(kid08_part886),(kid08_part887),(kid08_part888),(kid08_part889),(kid08_part890),(kid08_part891),(kid08_part892),(kid08_part893)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part870_checked

  · exact kid08_part876_checked

  · exact kid08_part882_checked

  · exact kid08_part888_checked

  · exact kid08_part871_checked

  · exact kid08_part877_checked

  · exact kid08_part883_checked

  · exact kid08_part889_checked

  · exact kid08_part872_checked

  · exact kid08_part878_checked

  · exact kid08_part884_checked

  · exact kid08_part890_checked

  · exact kid08_part873_checked

  · exact kid08_part879_checked

  · exact kid08_part885_checked

  · exact kid08_part891_checked

  · exact kid08_part874_checked

  · exact kid08_part880_checked

  · exact kid08_part886_checked

  · exact kid08_part892_checked

  · exact kid08_part875_checked

  · exact kid08_part881_checked

  · exact kid08_part887_checked

  · exact kid08_part893_checked

def kid08_part894 : Audit := .split 20 (5,false) (byMove [
.cycle 12 59 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.split 21 (4,false) (byMove [
.cycle 0 32 true (0),
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 0 26 true (0),
.last 31 (4,true),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 25 (4,true),
.cycle 20 2 true (1),
.last 33 (4,true),
.last 25 (4,true),
.cycle 0 28 true (0),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 0 26 true (0),
.last 31 (4,true),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.last 25 (4,true),
.last 23 (4,true)
]),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.split 21 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 1 31 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 20 2 true (2),
.cycle 0 34 true (0),
.cycle 0 59 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 0 38 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 23 (4,true),
.cycle 0 34 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (4,true),
.last 23 (4,true)
]),
.cycle 24 1 true (4),
.cycle 48 1 false (8),
.cycle 33 3 true (3),
.cycle 0 35 true (0),
.cycle 21 1 false (1),
.split 21 (4,false) (byMove [
.last 26 (4,true),
.last 29 (4,true),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 24 (4,true),
.last 27 (4,true),
.last 22 (4,true),
.cycle 19 3 false (3),
.last 26 (4,true),
.cycle 18 7 false (4),
.cycle 0 28 true (0),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 0 26 true (0),
.last 45 (4,true),
.last 24 (4,true),
.last 27 (4,true),
.last 22 (4,true),
.cycle 18 4 false (4)
]),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 2 27 true (0),
.cycle 0 67 true (0),
.split 21 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 27 (4,true),
.cycle 0 29 true (0),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 34 true (0),
.cycle 24 29 true (6),
.cycle 0 24 true (0),
.cycle 3 27 true (0),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 17 5 false (4),
.cycle 0 67 true (0),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 34 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (4,true),
.last 23 (4,true)
]),
.cycle 27 1 true (1)
])
theorem kid08_part894_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid08_part894) = true := by rfl

def kid08_part895 : Audit := .split 43 (5,false) (byMove [
.cycle 15 52 true (1),
.cycle 6 51 true (0),
.cycle 42 2 true (10),
.cycle 0 45 true (0),
.split 44 (4,true) (byMove [
.cycle 0 45 true (0),
.cycle 20 25 true (3),
.cycle 0 55 true (0),
.cycle 54 1 false (8),
.last 45 (4,false),
.last 46 (4,false),
.cycle 0 45 true (0),
.cycle 15 52 true (1),
.cycle 6 51 true (0),
.cycle 9 36 true (0),
.last 45 (4,false),
.last 46 (4,false),
.cycle 40 12 true (8),
.cycle 41 8 true (9),
.cycle 0 47 true (0),
.cycle 0 53 true (0),
.last 45 (4,false),
.last 46 (4,false),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 0 69 true (0),
.cycle 6 69 true (0),
.last 45 (4,false),
.cycle 43 2 true (10)
]),
.cycle 0 45 true (0),
.cycle 0 44 true (0),
.cycle 6 57 true (0),
.cycle 40 9 true (8),
.cycle 0 67 true (0),
.split 44 (4,false) (byMove [
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 0 69 true (0),
.cycle 6 69 true (0),
.last 46 (4,true),
.cycle 43 2 true (11),
.cycle 0 45 true (0),
.cycle 20 25 true (3),
.cycle 0 55 true (0),
.cycle 40 9 true (8),
.cycle 44 1 true (12),
.cycle 43 2 true (11),
.cycle 40 12 true (8),
.cycle 42 4 true (10),
.cycle 0 47 true (0),
.cycle 0 67 true (0),
.last 46 (4,true),
.last 46 (4,true),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 6 57 true (0),
.cycle 0 73 true (0),
.cycle 44 1 true (12),
.cycle 43 2 true (11)
]),
.cycle 43 1 true (11),
.cycle 25 19 true (3),
.cycle 41 3 true (9),
.cycle 0 46 true (0),
.cycle 6 67 true (0),
.split 44 (4,true) (byMove [
.cycle 46 5 true (10),
.cycle 0 48 true (0),
.cycle 10 36 true (0),
.cycle 54 1 false (8),
.last 45 (4,false),
.last 46 (4,false),
.cycle 6 67 true (0),
.cycle 26 19 true (3),
.cycle 42 3 true (10),
.cycle 0 46 true (0),
.last 46 (4,false),
.cycle 0 46 true (0),
.cycle 41 5 true (9),
.cycle 0 48 true (0),
.cycle 6 69 true (0),
.cycle 11 34 true (0),
.last 45 (4,false),
.last 46 (4,false),
.cycle 6 59 true (0),
.cycle 40 11 true (8),
.cycle 42 3 true (10),
.cycle 0 46 true (0),
.last 46 (4,false),
.cycle 0 46 true (0)
]),
.cycle 6 67 true (0),
.cycle 0 44 true (0),
.cycle 1 43 true (0),
.cycle 2 42 true (0),
.cycle 19 27 true (3),
.split 44 (4,false) (byMove [
.cycle 6 59 true (0),
.cycle 40 11 true (8),
.cycle 42 3 true (10),
.cycle 0 46 true (0),
.last 45 (4,true),
.cycle 0 46 true (0),
.cycle 0 45 true (0),
.cycle 6 58 true (0),
.cycle 40 10 true (8),
.cycle 3 42 true (0),
.cycle 44 1 true (12),
.cycle 43 2 true (11),
.cycle 0 57 true (0),
.cycle 41 4 true (9),
.cycle 0 47 true (0),
.cycle 19 27 true (3),
.last 45 (4,true),
.cycle 18 27 true (3),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 2 43 true (0),
.cycle 19 28 true (3),
.cycle 44 1 true (12),
.cycle 43 2 true (11)
]),
.cycle 43 1 true (11)
])
theorem kid08_part895_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid08_part895) = true := by rfl

def kid08_part896 : Audit := .split 51 (5,false) (byMove [
.cycle 16 58 true (2),
.cycle 7 45 true (0),
.cycle 50 2 true (12),
.cycle 0 53 true (0),
.split 52 (4,true) (byMove [
.cycle 0 53 true (0),
.cycle 30 23 true (6),
.cycle 64 1 false (12),
.cycle 59 1 false (13),
.last 53 (4,false),
.last 54 (4,false),
.cycle 0 53 true (0),
.cycle 16 58 true (2),
.cycle 8 45 true (0),
.cycle 21 32 true (3),
.last 53 (4,false),
.last 54 (4,false),
.cycle 49 12 true (11),
.cycle 49 8 true (11),
.cycle 0 55 true (0),
.cycle 61 1 false (11),
.last 53 (4,false),
.last 54 (4,false),
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 27 45 true (5),
.cycle 46 32 true (8),
.last 53 (4,false),
.cycle 51 2 true (12)
]),
.cycle 16 58 true (2),
.cycle 0 52 true (0),
.cycle 30 22 true (6),
.cycle 49 9 true (11),
.cycle 27 43 true (5),
.split 52 (4,false) (byMove [
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 27 45 true (5),
.cycle 46 32 true (8),
.last 54 (4,true),
.cycle 51 2 true (13),
.cycle 0 53 true (0),
.cycle 27 46 true (5),
.cycle 20 33 true (3),
.cycle 49 9 true (11),
.cycle 52 1 true (14),
.cycle 51 2 true (13),
.cycle 49 12 true (11),
.cycle 50 4 true (12),
.cycle 0 55 true (0),
.cycle 27 43 true (5),
.last 54 (4,true),
.last 54 (4,true),
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 31 22 true (6),
.cycle 16 61 true (2),
.cycle 52 1 true (14),
.cycle 51 2 true (13)
]),
.cycle 51 1 true (13),
.cycle 35 17 true (6),
.cycle 49 3 true (11),
.cycle 28 24 true (6),
.cycle 46 30 true (8),
.split 52 (4,true) (byMove [
.cycle 54 5 true (12),
.cycle 0 56 true (0),
.cycle 22 32 true (3),
.cycle 0 60 true (0),
.last 53 (4,false),
.last 54 (4,false),
.cycle 46 30 true (8),
.cycle 36 17 true (6),
.cycle 50 3 true (12),
.cycle 0 54 true (0),
.last 54 (4,false),
.cycle 46 30 true (8),
.cycle 49 5 true (11),
.cycle 28 26 true (6),
.cycle 46 32 true (8),
.cycle 23 30 true (3),
.last 53 (4,false),
.last 54 (4,false),
.cycle 30 24 true (6),
.cycle 49 11 true (11),
.cycle 50 3 true (12),
.cycle 0 54 true (0),
.last 54 (4,false),
.cycle 29 24 true (6)
]),
.cycle 36 17 true (6),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.cycle 27 48 true (5),
.split 52 (4,false) (byMove [
.cycle 30 24 true (6),
.cycle 49 11 true (11),
.cycle 50 3 true (12),
.cycle 0 54 true (0),
.last 53 (4,true),
.cycle 29 24 true (6),
.cycle 0 53 true (0),
.cycle 30 23 true (6),
.cycle 49 10 true (11),
.cycle 3 50 true (0),
.cycle 52 1 true (14),
.cycle 51 2 true (13),
.cycle 19 35 true (3),
.cycle 49 4 true (11),
.cycle 28 25 true (6),
.cycle 27 48 true (5),
.last 53 (4,true),
.cycle 18 35 true (3),
.cycle 0 53 true (0),
.cycle 1 52 true (0),
.cycle 2 51 true (0),
.cycle 27 49 true (5),
.cycle 52 1 true (14),
.cycle 51 2 true (13)
]),
.cycle 51 1 true (13)
])
theorem kid08_part896_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid08_part896) = true := by rfl

def kid08_part897 : Audit := .split 20 (5,false) (byMove [
.cycle 17 25 true (3),
.cycle 43 1 false (11),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 22 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 43 1 false (11),
.cycle 31 1 false (7),
.last 22 (4,false),
.last 23 (4,false),
.cycle 19 12 true (4),
.cycle 19 8 true (4),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 22 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 58 true (3),
.cycle 17 74 true (3),
.last 22 (4,false),
.cycle 20 2 true (5)
]),
.cycle 43 1 false (11),
.cycle 0 21 true (0),
.cycle 19 30 true (5),
.cycle 19 9 true (5),
.cycle 17 54 true (3),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 58 true (3),
.cycle 17 74 true (3),
.last 23 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 19 20 true (5),
.cycle 19 9 true (5),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 17 54 true (3),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 19 30 true (5),
.cycle 19 38 true (5),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 6 15 true (0),
.cycle 19 3 true (5),
.cycle 19 11 true (5),
.cycle 17 70 true (3),
.split 21 (4,true) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 32 1 false (6),
.cycle 42 1 false (8),
.last 22 (4,false),
.last 25 (4,false),
.cycle 17 70 true (3),
.cycle 7 15 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 8 15 true (0),
.cycle 19 5 true (4),
.cycle 19 13 true (4),
.cycle 17 74 true (3),
.cycle 29 1 false (5),
.last 22 (4,false),
.last 25 (4,false),
.cycle 19 32 true (5),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 19 11 true (5)
]),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.split 21 (4,false) (byMove [
.cycle 19 32 true (5),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 11 true (5),
.cycle 0 22 true (0),
.cycle 19 31 true (5),
.cycle 19 10 true (5),
.cycle 3 19 true (0),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 22 true (5),
.cycle 19 4 true (5),
.cycle 19 12 true (5),
.cycle 17 27 true (3),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part897_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid08_part897) = true := by rfl

def kid08_part898 : Audit := .cycle 0 20 true (0)
theorem kid08_part898_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid08_part898) = true := by rfl

def kid08_part900 : Audit := .cycle 0 20 true (0)
theorem kid08_part900_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part900) = true := by rfl

def kid08_part901 : Audit := .cycle 1 19 true (0)
theorem kid08_part901_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part901) = true := by rfl

def kid08_part902 : Audit := .cycle 27 1 false (7)
theorem kid08_part902_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part902) = true := by rfl

def kid08_part903 : Audit := .cycle 31 1 false (9)
theorem kid08_part903_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part903) = true := by rfl

def kid08_part904 : Audit := .split 20 (4,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 1 false (2),
.last 23 (5,false),
.cycle 0 21 true (0),
.last 44 (5,false),
.last 29 (5,false),
.cycle 27 1 false (7),
.cycle 20 1 true (4),
.last 21 (5,false),
.cycle 24 1 false (6),
.last 23 (5,false),
.cycle 0 26 true (0),
.cycle 31 1 false (9),
.cycle 22 1 false (2),
.last 24 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 51 (5,false),
.cycle 20 1 true (4),
.last 21 (5,false)
])
theorem kid08_part904_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part904) = true := by rfl

def kid08_part905 : Audit := .split 20 (5,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 20 2 true (3),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 22 (4,false),
.cycle 0 21 true (0),
.cycle 20 24 true (3),
.cycle 20 9 true (3),
.cycle 27 1 false (7),
.last 21 (4,false),
.cycle 20 1 true (4),
.cycle 24 1 false (6),
.cycle 20 3 true (3),
.last 23 (4,false),
.cycle 31 1 false (9),
.last 23 (4,false),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 20 31 true (3),
.last 21 (4,false),
.cycle 20 1 true (4)
])
theorem kid08_part905_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part905) = true := by rfl

def kid08_part906 : Audit := .cycle 0 20 true (0)
theorem kid08_part906_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part906) = true := by rfl

def kid08_part907 : Audit := .split 43 (5,false) (byMove [
.cycle 16 52 true (2),
.cycle 7 51 true (0),
.cycle 42 2 true (10),
.cycle 0 45 true (0),
.cycle 16 52 true (2),
.last 45 (4,false),
.cycle 0 44 true (0),
.cycle 7 57 true (0),
.cycle 41 9 true (9),
.last 67 (4,false),
.last 44 (4,false),
.cycle 43 1 true (11),
.cycle 25 19 true (3),
.cycle 41 3 true (9),
.last 46 (4,false),
.cycle 7 67 true (0),
.cycle 26 19 true (3),
.cycle 7 67 true (0),
.cycle 0 44 true (0),
.cycle 1 43 true (0),
.cycle 2 42 true (0),
.cycle 20 27 true (3),
.last 44 (4,false),
.cycle 43 1 true (11)
])
theorem kid08_part907_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part907) = true := by rfl

def kid08_part908 : Audit := .split 30 (4,false) (byMove [
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 38 1 false (10),
.cycle 42 1 false (12),
.cycle 34 1 false (8),
.last 31 (5,false),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 20 11 true (3),
.last 38 (5,false),
.cycle 30 1 true (8),
.last 31 (5,false),
.last 41 (5,false),
.last 33 (5,false),
.cycle 0 33 true (0),
.cycle 36 1 false (10),
.cycle 28 5 true (6),
.last 31 (5,false),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.last 51 (5,false),
.cycle 17 39 true (3),
.cycle 30 1 true (8),
.last 31 (5,false)
])
theorem kid08_part908_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part908) = true := by rfl

def kid08_part909 : Audit := .split 27 (5,false) (byMove [
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 26 2 true (6),
.cycle 0 29 true (0),
.cycle 29 1 false (7),
.last 29 (4,false),
.cycle 0 28 true (0),
.cycle 0 49 true (0),
.cycle 20 9 true (3),
.cycle 34 1 false (10),
.last 28 (4,false),
.cycle 27 1 true (7),
.cycle 31 1 false (9),
.cycle 25 3 true (5),
.last 30 (4,false),
.cycle 38 1 false (12),
.cycle 0 30 true (0),
.cycle 30 1 false (8),
.cycle 0 28 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.cycle 23 54 true (3),
.last 28 (4,false),
.cycle 27 1 true (7)
])
theorem kid08_part909_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part909) = true := by rfl

def kid08_part910 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 32768, 16777216, 128, 256, 32768, 524290, 2097160, 16777216, 128, 256, 2097152, 4, 32768, 16777216, 128, 256, 8, 2048, 32768, 16777216, 16777216],[2, 4, 2048, 1, 16, 16, 8192, 16384, 2048, 4096, 65536, 65536, 524288, 1048576, 2048, 262144, 4194304, 4194304, 2, 4, 2048, 1, 16, 16, 16777216],27413536⟩,
.last 29 (5,false),
.cycle 27 1 false (7),
.cycle 24 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 2, 16777216, 128, 256, 32768, 524290, 8192, 16777216, 128, 256, 2097152, 4, 524288, 16777216, 128, 256, 8, 2048, 2, 16777216, 16777216],[2, 4, 2048, 1, 16, 16, 8192, 16384, 2048, 4096, 65536, 65536, 524288, 1048576, 2048, 262144, 4194304, 4194304, 2, 4, 2048, 1, 16, 16, 16777216],27412512⟩,
.cycle 8 13 true (0),
.last 38 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.last 27 (5,false),
.cycle 27 1 false (7),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 256, 16777216, 128, 256, 32768, 524290, 256, 16777216, 128, 256, 2097152, 4, 256, 16777216, 128, 256, 8, 2048, 256, 16777216, 16777216],[2, 4, 2048, 1, 16, 16, 8192, 16384, 2048, 4096, 65536, 65536, 524288, 1048576, 2048, 262144, 4194304, 4194304, 2, 4, 2048, 1, 16, 16, 16777216],27412512⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4259856, 512, 16777216, 128, 256, 32768, 524290, 512, 16777216, 128, 256, 2097152, 4, 512, 16777216, 128, 256, 8, 2048, 512, 16777216, 16777216],[2, 4, 2048, 1, 16, 16, 8192, 16384, 2048, 4096, 65536, 65536, 524288, 1048576, 2048, 262144, 4194304, 4194304, 2, 4, 2048, 1, 16, 16, 16777216],27412512⟩,
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part910_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part910) = true := by rfl

def kid08_part911 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.last 42 (4,false),
.cycle 28 2 true (6),
.cycle 27 1 false (7),
.last 21 (4,false),
.last 24 (4,false),
.cycle 0 21 true (0),
.last 46 (4,false),
.cycle 8 13 true (0),
.last 30 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 52 (4,false),
.cycle 22 3 true (6),
.cycle 0 23 true (0),
.cycle 38 1 false (12),
.last 21 (4,false),
.cycle 27 1 false (7),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far true 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 4, 4, 5, 8, 7, 7, 4, 6],[0, 549755813888, 2097152, 512, 18014398509481984, 549755813888, 0, 0, 0, 2097152, 18014398509481984, 0, 0, 0, 549755813888, 512, 18014398509481984, 0, 0, 18014398509481984, 2251799813685248, 549755813888, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 20301382697353216, 35184372088832, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 2252349569499136, 134217728, 18014398509481984, 18014398509481984, 18014398509481984, 0, 20266198323167232, 2251799813685248, 18014398509481984, 0, 20301932451069952, 20301932451069952, 20301932451069952, 35184372088832, 18014398509481984, 20301932451069952, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 18014398509481984, 18014398509481984],[2251799813685248, 549755813888, 0, 0, 2251799813685248, 18014398509481984, 2251799813685248, 0, 18014398509481984, 549755813888, 18014398509481984, 549755813888, 0, 0, 0, 0, 0, 18014398509481984, 0, 18014398509481984, 0, 549755813888, 2251799813685248, 18014398509481984, 20266198323167232, 20266748078981120, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014948265295872, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 0, 18014398509481984, 0, 18014398509481984, 549755813888, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 0, 18014398509481984, 0, 18014398509481984, 2251799813685248, 18014398509481984, 18014398509481984],32331538708890640⟩,
.far true 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 4, 4, 5, 8, 7, 7, 4, 6],[0, 549755813888, 2097152, 512, 18014398509481984, 549755813888, 0, 0, 0, 2097152, 18014398509481984, 0, 0, 0, 549755813888, 512, 18014398509481984, 549755813888, 0, 18014398509481984, 2251799813685248, 549755813888, 18014398509481984, 0, 18014398509481984, 18014398509481984, 20301382697353216, 35184372088832, 18014398509481984, 18014948265295872, 18014398509481984, 18014398509481984, 2252349569499136, 134217728, 18014398509481984, 18014398509481984, 18014398509481984, 0, 20266198323167232, 2251799813685248, 18014398509481984, 18014398509481984, 20301932451069952, 20301932451069952, 20301932451069952, 35184372088832, 18014398509481984, 20301932451069952, 0, 18014398509481984, 0, 549755813888, 18014398509481984, 0, 18014398509481984],[2251799813685248, 549755813888, 0, 0, 2251799813685248, 18014398509481984, 2251799813685248, 0, 18014398509481984, 549755813888, 18014398509481984, 549755813888, 0, 0, 0, 0, 0, 18014398509481984, 0, 18014398509481984, 0, 549755813888, 2251799813685248, 18014398509481984, 20266198323167232, 20266748078981120, 18014398509481984, 18014398509481984, 20266198323167232, 18014398509481984, 18014398509481984, 18014948265295872, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 18014398509481984, 0, 18014398509481984, 0, 18014398509481984, 549755813888, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 20301932451069952, 0, 18014398509481984, 0, 18014398509481984, 2251799813685248, 18014398509481984, 18014398509481984],23326538469016592⟩,
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part911_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part911) = true := by rfl

def kid08_part912 : Audit := .split 30 (5,false) (byMove [
.last 90 (4,false),
.last 60 (4,false),
.cycle 29 2 true (7),
.cycle 0 32 true (0),
.cycle 19 12 true (4),
.last 32 (4,false),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 22 9 true (4),
.cycle 16 36 true (2),
.last 31 (4,false),
.cycle 30 1 true (8),
.last 51 (4,false),
.cycle 28 3 true (6),
.last 33 (4,false),
.last 66 (4,false),
.cycle 28 5 true (6),
.cycle 18 13 true (4),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.last 59 (4,false),
.last 31 (4,false),
.cycle 30 1 true (8)
])
theorem kid08_part912_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part912) = true := by rfl

def kid08_part913 : Audit := .split 22 (5,false) (byMove [
.last 47 (4,false),
.last 50 (4,false),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 19 8 true (4),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 46 (4,false),
.cycle 21 9 true (5),
.cycle 3 20 true (0),
.last 23 (4,false),
.cycle 22 1 true (6),
.last 35 (4,false),
.cycle 21 3 true (5),
.last 25 (4,false),
.cycle 17 30 true (3),
.last 27 (4,false),
.cycle 18 5 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 31 true (3),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part913_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part913) = true := by rfl

def kid08_part914 : Audit := .cycle 0 22 true (0)
theorem kid08_part914_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part914) = true := by rfl

def kid08_part915 : Audit := .cycle 25 1 false (7)
theorem kid08_part915_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part915) = true := by rfl

def kid08_part916 : Audit := .split 20 (4,false) (byMove [
.last 24 (5,false),
.cycle 0 24 true (0),
.last 22 (5,false),
.last 32 (5,false),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 47 (5,false),
.cycle 29 26 true (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 2 true (4),
.last 23 (5,false),
.last 24 (5,false),
.last 27 (5,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.cycle 22 1 false (2),
.last 24 (5,false),
.cycle 0 56 true (0),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 22 3 false (4),
.last 23 (5,false)
])
theorem kid08_part916_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part916) = true := by rfl

def kid08_part917 : Audit := .split 20 (5,false) (byMove [
.last 51 (4,false),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.cycle 0 34 true (0),
.last 23 (4,false),
.last 22 (4,false),
.cycle 0 48 true (0),
.last 32 (4,false),
.cycle 21 9 true (5),
.cycle 0 22 true (0),
.cycle 19 2 true (4),
.last 22 (4,false),
.cycle 28 1 false (8),
.last 24 (4,false),
.cycle 17 4 true (3),
.cycle 25 1 false (7),
.last 23 (4,false),
.cycle 23 1 false (3),
.last 55 (4,false),
.cycle 1 30 true (0),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 18 4 true (4),
.last 22 (4,false)
])
theorem kid08_part917_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part917) = true := by rfl

def kid08_part918 : Audit := .cycle 0 20 true (0)
theorem kid08_part918_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part918) = true := by rfl

def kid08_part919 : Audit := .cycle 1 19 true (0)
theorem kid08_part919_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part919) = true := by rfl

def kid08_part920 : Audit := .split 40 (5,false) (byMove [
.cycle 20 23 true (3),
.last 68 (4,false),
.cycle 39 2 true (9),
.cycle 0 42 true (0),
.cycle 2 40 true (0),
.last 42 (4,false),
.cycle 0 41 true (0),
.cycle 20 22 true (3),
.cycle 39 9 true (9),
.cycle 3 38 true (0),
.last 41 (4,false),
.cycle 40 1 true (10),
.last 53 (4,false),
.cycle 39 3 true (9),
.last 43 (4,false),
.last 66 (4,false),
.cycle 38 3 true (8),
.cycle 18 23 true (3),
.cycle 0 41 true (0),
.cycle 1 40 true (0),
.cycle 2 39 true (0),
.last 67 (4,false),
.last 41 (4,false),
.cycle 40 1 true (10)
])
theorem kid08_part920_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part920) = true := by rfl

def kid08_part921 : Audit := .cycle 5 40 true (0)
theorem kid08_part921_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part921) = true := by rfl

def kid08_part922 : Audit := .split 20 (4,false) (byMove [
.cycle 43 23 true (9),
.cycle 1 32 true (0),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (5,false),
.cycle 3 38 true (0),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 6 15 true (0),
.last 23 (5,false),
.cycle 0 26 true (0),
.cycle 45 26 true (9),
.cycle 19 3 true (5),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part922_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part922) = true := by rfl

def kid08_part923 : Audit := .split 20 (5,false) (byMove [
.cycle 18 25 true (3),
.last 32 (4,false),
.cycle 20 2 true (5),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 22 (4,false),
.cycle 0 21 true (0),
.last 42 (4,false),
.cycle 20 9 true (5),
.last 40 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 6 15 true (0),
.cycle 20 3 true (5),
.last 23 (4,false),
.last 48 (4,false),
.last 23 (4,false),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part923_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part923) = true := by rfl

def kid08_part899 : Audit := .split 19 (4,true) (byMove [(kid08_part900),(kid08_part901),(kid08_part902),(kid08_part903),(kid08_part904),(kid08_part905),(kid08_part906),(kid08_part907),(kid08_part908),(kid08_part909),(kid08_part910),(kid08_part911),(kid08_part912),(kid08_part913),(kid08_part914),(kid08_part915),(kid08_part916),(kid08_part917),(kid08_part918),(kid08_part919),(kid08_part920),(kid08_part921),(kid08_part922),(kid08_part923)])

theorem kid08_part899_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid08_part899) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part900),(kid08_part901),(kid08_part902),(kid08_part903),(kid08_part904),(kid08_part905),(kid08_part906),(kid08_part907),(kid08_part908),(kid08_part909),(kid08_part910),(kid08_part911),(kid08_part912),(kid08_part913),(kid08_part914),(kid08_part915),(kid08_part916),(kid08_part917),(kid08_part918),(kid08_part919),(kid08_part920),(kid08_part921),(kid08_part922),(kid08_part923)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part900_checked

  · exact kid08_part906_checked

  · exact kid08_part912_checked

  · exact kid08_part918_checked

  · exact kid08_part901_checked

  · exact kid08_part907_checked

  · exact kid08_part913_checked

  · exact kid08_part919_checked

  · exact kid08_part902_checked

  · exact kid08_part908_checked

  · exact kid08_part914_checked

  · exact kid08_part920_checked

  · exact kid08_part903_checked

  · exact kid08_part909_checked

  · exact kid08_part915_checked

  · exact kid08_part921_checked

  · exact kid08_part904_checked

  · exact kid08_part910_checked

  · exact kid08_part916_checked

  · exact kid08_part922_checked

  · exact kid08_part905_checked

  · exact kid08_part911_checked

  · exact kid08_part917_checked

  · exact kid08_part923_checked

def kid08_part924 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 4, 32, 1, 64, 32, 64],80⟩,
.cycle 28 2 true (6),
.cycle 27 1 false (7),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 2, 256, 128, 256, 32768, 524290, 8192, 16777216, 128, 256, 2097152, 4, 524288, 256, 128, 256, 8, 2048, 2, 256, 16777216],[2, 4, 2048, 1, 16777216, 32, 8192, 16384, 2048, 4096, 16777216, 131072, 524288, 1048576, 2048, 262144, 16777216, 8388608, 2, 4, 2048, 1, 16777216, 32, 16777216],18892800⟩,
.last 43 (4,true),
.last 30 (4,true),
.cycle 21 1 true (5),
.cycle 20 2 true (5),
.last 33 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 256, 32768, 128, 256, 32768, 524290, 256, 16777216, 128, 256, 2097152, 4, 256, 32768, 128, 256, 8, 2048, 256, 32768, 16777216],[2, 4, 2048, 1, 16777216, 32, 8192, 16384, 2048, 4096, 16777216, 131072, 524288, 1048576, 2048, 262144, 16777216, 8388608, 2, 4, 2048, 1, 16777216, 32, 16777216],18892800⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 512, 524290, 128, 256, 32768, 524290, 512, 16777216, 128, 256, 2097152, 4, 512, 524290, 128, 256, 8, 2048, 512, 524290, 16777216],[2, 4, 2048, 1, 16777216, 32, 8192, 16384, 2048, 4096, 16777216, 131072, 524288, 1048576, 2048, 262144, 16777216, 8388608, 2, 4, 2048, 1, 16777216, 32, 16777216],18892800⟩,
.cycle 21 1 true (5),
.last 23 (4,true)
]),
.cycle 24 1 false (4),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 2, 64],[2, 4, 32, 1, 64, 32, 64],80⟩,
.cycle 8 13 true (0),
.cycle 45 1 false (13),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.cycle 51 1 false (13),
.cycle 42 1 false (12),
.last 25 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 2, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.cycle 9 13 true (0),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 45 1 false (13),
.last 25 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 4, 32, 1, 64, 32, 64],80⟩,
.cycle 22 3 true (6),
.cycle 0 23 true (0),
.cycle 38 1 false (12),
.split 21 (4,false) (byMove [
.last 26 (4,true),
.cycle 0 25 true (0),
.last 30 (4,true),
.last 28 (4,true),
.last 23 (4,true),
.last 23 (4,true),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 1, 2, 128, 256, 32768, 524290, 4096, 16777216, 128, 256, 2097152, 4, 262144, 524288, 128, 256, 8, 2048, 1, 2, 16777216],[2, 4, 2048, 1, 16777216, 32, 8192, 16384, 2048, 4096, 16777216, 131072, 524288, 1048576, 2048, 262144, 16777216, 8388608, 2, 4, 2048, 1, 16777216, 32, 16777216],18892800⟩,
.cycle 7 15 true (0),
.last 24 (4,true),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5),
.last 26 (4,true),
.cycle 23 5 true (5),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 8519712, 1, 2, 128, 256, 32768, 524290, 131072, 16777216, 128, 256, 2097152, 4, 262144, 8388608, 128, 256, 8, 2048, 1, 2, 16777216],[2, 4, 2048, 1, 16777216, 32, 8192, 16384, 2048, 4096, 16777216, 131072, 524288, 1048576, 2048, 262144, 16777216, 8388608, 2, 4, 2048, 1, 16777216, 32, 16777216],18892800⟩,
.last 28 (4,true),
.last 23 (4,true),
.last 23 (4,true),
.cycle 18 24 true (4),
.last 32 (4,true),
.last 24 (4,true),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5)
]),
.cycle 27 1 false (7),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 4, 32, 1, 64, 32, 64],80⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 4, 32, 1, 64, 32, 64],80⟩,
.split 21 (4,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.cycle 7 15 true (0),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 38, 16, 64],[2, 4, 32, 1, 64, 32, 64],64⟩,
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part924_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid08_part924) = true := by rfl

def kid08_part925 : Audit := .split 22 (5,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.split 23 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.last 24 (4,false),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.last 24 (4,false),
.last 25 (4,false),
.cycle 19 12 true (3),
.cycle 20 8 true (4),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 24 (4,false),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 31 1 false (9),
.cycle 35 1 false (11),
.last 24 (4,false),
.cycle 22 2 true (5)
]),
.cycle 19 12 true (3),
.cycle 0 23 true (0),
.cycle 49 1 false (13),
.cycle 19 9 true (3),
.cycle 29 1 false (9),
.split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 31 1 false (9),
.cycle 35 1 false (11),
.last 25 (4,true),
.cycle 22 2 true (6),
.cycle 0 24 true (0),
.cycle 15 29 true (1),
.cycle 37 1 false (11),
.cycle 19 9 true (3),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 19 12 true (3),
.cycle 21 4 true (5),
.cycle 0 26 true (0),
.cycle 29 1 false (9),
.last 25 (4,true),
.last 25 (4,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 49 1 false (13),
.cycle 59 1 false (15),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6),
.cycle 26 1 false (8),
.cycle 20 3 true (4),
.cycle 28 1 false (8),
.cycle 33 1 false (11),
.split 23 (4,true) (byMove [
.cycle 25 5 true (5),
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.last 24 (4,false),
.last 25 (4,false),
.cycle 33 1 false (11),
.cycle 26 1 false (8),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 19 13 true (3),
.cycle 20 5 true (4),
.cycle 42 1 false (10),
.cycle 35 1 false (11),
.cycle 24 1 false (4),
.last 24 (4,false),
.last 25 (4,false),
.cycle 51 1 false (13),
.cycle 19 11 true (3),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 28 1 false (8)
]),
.cycle 20 5 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 31 true (1),
.split 23 (4,false) (byMove [
.cycle 51 1 false (13),
.cycle 19 11 true (3),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 28 1 false (8),
.cycle 0 24 true (0),
.cycle 15 53 true (1),
.cycle 19 10 true (3),
.cycle 3 21 true (0),
.cycle 23 1 true (7),
.cycle 22 2 true (6),
.cycle 39 1 false (11),
.cycle 20 4 true (4),
.cycle 41 1 false (11),
.cycle 15 31 true (1),
.last 24 (4,true),
.cycle 18 6 true (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 15 32 true (1),
.cycle 23 1 true (7),
.cycle 22 2 true (6)
]),
.cycle 22 1 true (6)
])
theorem kid08_part925_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid08_part925) = true := by rfl

def kid08_part926 : Audit := .split 24 (5,false) (byMove [
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 23 2 true (5),
.cycle 0 26 true (0),
.split 25 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 34 1 false (8),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.last 26 (4,false),
.last 27 (4,false),
.cycle 0 26 true (0),
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.last 26 (4,false),
.last 27 (4,false),
.cycle 22 12 true (4),
.cycle 22 8 true (4),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.last 26 (4,false),
.last 27 (4,false),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 33 1 false (9),
.cycle 37 1 false (11),
.last 26 (4,false),
.cycle 24 2 true (5)
]),
.cycle 21 8 true (4),
.cycle 0 25 true (0),
.cycle 16 28 true (2),
.cycle 22 9 true (4),
.cycle 31 1 false (9),
.split 25 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 33 1 false (9),
.cycle 37 1 false (11),
.last 27 (4,true),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.cycle 16 33 true (2),
.cycle 19 14 true (3),
.cycle 22 9 true (4),
.cycle 25 1 true (7),
.cycle 24 2 true (6),
.cycle 22 12 true (4),
.cycle 23 4 true (5),
.cycle 0 28 true (0),
.cycle 31 1 false (9),
.last 27 (4,true),
.last 27 (4,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 16 28 true (2),
.cycle 16 40 true (2),
.cycle 25 1 true (7),
.cycle 24 2 true (6)
]),
.cycle 24 1 true (6),
.cycle 28 1 false (8),
.cycle 22 3 true (4),
.cycle 20 5 true (4),
.cycle 35 1 false (11),
.split 25 (4,true) (byMove [
.cycle 27 5 true (5),
.cycle 0 29 true (0),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.last 26 (4,false),
.last 27 (4,false),
.cycle 35 1 false (11),
.cycle 28 1 false (8),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 27 (4,false),
.cycle 23 5 true (5),
.cycle 22 5 true (4),
.cycle 20 7 true (4),
.cycle 37 1 false (11),
.cycle 26 1 false (4),
.last 26 (4,false),
.last 27 (4,false),
.cycle 16 30 true (2),
.cycle 22 11 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 27 (4,false),
.cycle 21 5 true (4)
]),
.cycle 20 7 true (4),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 16 35 true (2),
.split 25 (4,false) (byMove [
.cycle 16 30 true (2),
.cycle 22 11 true (4),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 21 5 true (4),
.cycle 0 26 true (0),
.cycle 16 29 true (2),
.cycle 22 10 true (4),
.cycle 3 23 true (0),
.cycle 25 1 true (7),
.cycle 24 2 true (6),
.cycle 19 16 true (3),
.cycle 22 4 true (4),
.cycle 20 6 true (4),
.cycle 16 35 true (2),
.last 26 (4,true),
.cycle 18 8 true (3),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 16 36 true (2),
.cycle 25 1 true (7),
.cycle 24 2 true (6)
]),
.cycle 24 1 true (6)
])
theorem kid08_part926_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid08_part926) = true := by rfl

def kid08_part927 : Audit := .cycle 17 2 true (3)
theorem kid08_part927_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid08_part927) = true := by rfl

def kid08_part928 : Audit := .cycle 23 1 false (7)
theorem kid08_part928_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid08_part928) = true := by rfl

def kid08_part930 : Audit := .split 28 (5,false) (byMove [
.cycle 21 35 true (3),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 2, 64],[8, 8, 9, 8, 1, 16, 64],80⟩,
.cycle 27 2 true (5),
.cycle 0 30 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 16, 64],[8, 8, 1, 8, 1, 16, 64],112⟩,
.cycle 23 12 true (3),
.cycle 0 29 true (0),
.cycle 21 34 true (3),
.cycle 27 9 true (5),
.cycle 3 26 true (0),
.last 29 (4,false),
.cycle 28 1 true (6),
.cycle 26 17 true (4),
.cycle 27 3 true (5),
.cycle 22 7 true (3),
.cycle 21 42 true (3),
.cycle 24 5 true (3),
.cycle 18 11 true (2),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 21 43 true (3),
.last 29 (4,false),
.cycle 28 1 true (6)
])
theorem kid08_part930_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part930) = true := by rfl

def kid08_part931 : Audit := .cycle 0 57 true (0)
theorem kid08_part931_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part931) = true := by rfl

def kid08_part932 : Audit := .cycle 21 1 false (3)
theorem kid08_part932_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part932) = true := by rfl

def kid08_part933 : Audit := .cycle 20 1 false (2)
theorem kid08_part933_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part933) = true := by rfl

def kid08_part934 : Audit := .split 20 (4,false) (byMove [
.cycle 0 63 true (0),
.last 40 (5,false),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.cycle 0 30 true (0),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 26 1 true (4),
.last 21 (5,false),
.cycle 14 39 true (0),
.last 23 (5,false),
.last 26 (5,false),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.last 36 (5,false),
.cycle 0 57 true (0),
.last 26 (5,false),
.cycle 34 1 true (0),
.last 21 (5,false)
])
theorem kid08_part934_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part934) = true := by rfl

def kid08_part935 : Audit := .split 20 (5,false) (byMove [
.cycle 0 63 true (0),
.cycle 43 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.last 26 (4,false),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.last 23 (4,false),
.cycle 14 39 true (0),
.cycle 16 16 true (1),
.cycle 0 41 true (0),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 1 40 true (0),
.cycle 0 57 true (0),
.cycle 13 39 true (0),
.last 21 (4,false),
.last 25 (4,false)
])
theorem kid08_part935_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part935) = true := by rfl

def kid08_part936 : Audit := .cycle 23 1 false (7)
theorem kid08_part936_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part936) = true := by rfl

def kid08_part937 : Audit := .split 22 (5,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 32 1 false (10),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 49 1 false (13),
.cycle 20 9 true (4),
.cycle 29 1 false (9),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 26 1 false (8),
.cycle 20 3 true (4),
.cycle 28 1 false (8),
.cycle 33 1 false (11),
.cycle 26 1 false (8),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 16 31 true (2),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part937_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part937) = true := by rfl

def kid08_part938 : Audit := .split 24 (5,false) (byMove [
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 23 2 true (5),
.cycle 0 26 true (0),
.cycle 27 1 false (7),
.last 26 (4,false),
.cycle 0 25 true (0),
.cycle 17 28 true (3),
.cycle 23 9 true (5),
.cycle 31 1 false (9),
.last 25 (4,false),
.cycle 24 1 true (6),
.cycle 28 1 false (8),
.cycle 23 3 true (5),
.cycle 20 5 true (4),
.cycle 35 1 false (11),
.cycle 22 3 true (4),
.last 26 (4,false),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.last 25 (4,false),
.cycle 24 1 true (6)
])
theorem kid08_part938_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part938) = true := by rfl

def kid08_part939 : Audit := .cycle 30 1 false (10)
theorem kid08_part939_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part939) = true := by rfl

def kid08_part940 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 31 1 false (11),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 22 1 true (6),
.last 23 (5,false),
.last 33 (5,false),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (10),
.cycle 34 1 false (12),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part940_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part940) = true := by rfl

def kid08_part941 : Audit := .split 21 (4,false) (byMove [
.last 32 (5,false),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 22 (5,false),
.cycle 25 1 false (7),
.last 24 (5,false),
.last 28 (5,false),
.cycle 32 1 false (10),
.last 26 (5,false),
.cycle 20 2 true (3),
.last 32 (5,false),
.cycle 16 12 true (2),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 22 (5,false),
.last 63 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.last 51 (5,false),
.last 26 (5,false),
.cycle 18 4 true (3)
])
theorem kid08_part941_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part941) = true := by rfl

def kid08_part942 : Audit := .split 28 (5,false) (byMove [
.cycle 16 41 true (2),
.cycle 21 16 true (3),
.cycle 27 2 true (5),
.cycle 0 30 true (0),
.cycle 26 12 true (4),
.last 30 (4,false),
.cycle 0 29 true (0),
.cycle 16 34 true (2),
.cycle 26 9 true (4),
.cycle 16 32 true (2),
.last 29 (4,false),
.cycle 28 1 true (6),
.cycle 6 23 true (0),
.cycle 26 3 true (4),
.cycle 22 7 true (3),
.cycle 16 48 true (2),
.cycle 24 5 true (3),
.last 30 (4,false),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 16 43 true (2),
.last 29 (4,false),
.cycle 28 1 true (6)
])
theorem kid08_part942_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part942) = true := by rfl

def kid08_part943 : Audit := .cycle 16 8 true (2)
theorem kid08_part943_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part943) = true := by rfl

def kid08_part944 : Audit := .cycle 25 1 false (7)
theorem kid08_part944_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part944) = true := by rfl

def kid08_part945 : Audit := .cycle 20 1 false (2)
theorem kid08_part945_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part945) = true := by rfl

def kid08_part946 : Audit := .split 20 (4,false) (byMove [
.cycle 19 8 false (4),
.last 46 (5,false),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (2),
.cycle 20 2 true (2),
.cycle 15 12 true (1),
.cycle 19 6 false (3),
.last 26 (5,false),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 21 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.cycle 19 5 false (4),
.cycle 5 16 true (0),
.cycle 19 3 false (3),
.cycle 18 3 false (4)
])
theorem kid08_part946_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part946) = true := by rfl

def kid08_part947 : Audit := .split 20 (5,false) (byMove [
.cycle 18 8 false (4),
.cycle 14 87 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 16 34 true (2),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.cycle 19 2 true (2),
.last 22 (4,false),
.cycle 15 12 true (1),
.last 26 (4,false),
.cycle 36 1 false (8),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.last 25 (4,false),
.cycle 5 16 true (0),
.last 23 (4,false),
.cycle 18 3 false (4)
])
theorem kid08_part947_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part947) = true := by rfl

def kid08_part948 : Audit := .split 57 (5,false) (byMove [
.cycle 15 66 true (1),
.cycle 7 51 true (0),
.cycle 56 2 true (12),
.cycle 0 59 true (0),
.cycle 0 59 true (0),
.last 59 (4,false),
.cycle 0 58 true (0),
.cycle 34 24 true (6),
.cycle 54 9 true (10),
.cycle 28 49 true (4),
.last 58 (4,false),
.cycle 57 1 true (13),
.cycle 39 19 true (6),
.cycle 55 3 true (11),
.cycle 30 28 true (6),
.cycle 49 34 true (7),
.cycle 32 26 true (6),
.last 59 (4,false),
.cycle 0 58 true (0),
.cycle 1 57 true (0),
.cycle 2 56 true (0),
.cycle 28 54 true (4),
.last 58 (4,false),
.cycle 57 1 true (13)
])
theorem kid08_part948_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part948) = true := by rfl

def kid08_part949 : Audit := .split 22 (5,false) (byMove [
.cycle 16 29 true (2),
.cycle 47 1 false (11),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 20 34 true (4),
.cycle 20 9 true (4),
.cycle 16 64 true (2),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 6 17 true (0),
.cycle 20 3 true (4),
.cycle 20 13 true (4),
.cycle 16 84 true (2),
.cycle 20 11 true (4),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 16 31 true (2),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part949_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part949) = true := by rfl

def kid08_part950 : Audit := .split 24 (5,false) (byMove [
.cycle 17 29 true (3),
.cycle 17 32 true (3),
.cycle 23 2 true (5),
.cycle 0 26 true (0),
.cycle 2 24 true (0),
.cycle 21 4 true (4),
.cycle 0 25 true (0),
.cycle 17 28 true (3),
.cycle 23 9 true (5),
.cycle 3 22 true (0),
.last 25 (4,false),
.cycle 24 1 true (6),
.cycle 20 15 true (4),
.cycle 23 3 true (5),
.cycle 20 5 true (4),
.cycle 17 34 true (3),
.cycle 22 3 true (4),
.cycle 18 7 true (3),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 17 35 true (3),
.last 25 (4,false),
.cycle 24 1 true (6)
])
theorem kid08_part950_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part950) = true := by rfl

def kid08_part951 : Audit := .split 47 (5,false) (byMove [
.cycle 14 58 true (0),
.cycle 5 57 true (0),
.cycle 46 2 true (10),
.cycle 0 49 true (0),
.cycle 5 77 true (0),
.last 49 (4,false),
.cycle 0 48 true (0),
.cycle 5 63 true (0),
.cycle 43 9 true (7),
.cycle 0 75 true (0),
.last 48 (4,false),
.cycle 47 1 true (11),
.cycle 27 21 true (3),
.cycle 45 3 true (9),
.cycle 0 52 true (0),
.cycle 5 75 true (0),
.cycle 0 50 true (0),
.last 49 (4,false),
.cycle 0 48 true (0),
.cycle 1 47 true (0),
.cycle 2 46 true (0),
.cycle 20 29 true (3),
.last 48 (4,false),
.cycle 47 1 true (11)
])
theorem kid08_part951_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part951) = true := by rfl

def kid08_part952 : Audit := .split 22 (4,false) (byMove [
.cycle 19 25 true (3),
.last 32 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 21 2 true (5),
.cycle 20 4 true (4),
.cycle 0 23 true (0),
.cycle 19 24 true (3),
.last 31 (5,false),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 20 15 true (4),
.last 25 (5,false),
.cycle 20 5 true (4),
.cycle 19 28 true (3),
.cycle 20 3 true (4),
.cycle 18 5 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 19 29 true (3),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part952_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part952) = true := by rfl

def kid08_part953 : Audit := .cycle 18 2 true (3)
theorem kid08_part953_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part953) = true := by rfl

def kid08_part929 : Audit := .split 19 (4,true) (byMove [(kid08_part930),(kid08_part931),(kid08_part932),(kid08_part933),(kid08_part934),(kid08_part935),(kid08_part936),(kid08_part937),(kid08_part938),(kid08_part939),(kid08_part940),(kid08_part941),(kid08_part942),(kid08_part943),(kid08_part944),(kid08_part945),(kid08_part946),(kid08_part947),(kid08_part948),(kid08_part949),(kid08_part950),(kid08_part951),(kid08_part952),(kid08_part953)])

theorem kid08_part929_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid08_part929) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid08_part930),(kid08_part931),(kid08_part932),(kid08_part933),(kid08_part934),(kid08_part935),(kid08_part936),(kid08_part937),(kid08_part938),(kid08_part939),(kid08_part940),(kid08_part941),(kid08_part942),(kid08_part943),(kid08_part944),(kid08_part945),(kid08_part946),(kid08_part947),(kid08_part948),(kid08_part949),(kid08_part950),(kid08_part951),(kid08_part952),(kid08_part953)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part930_checked

  · exact kid08_part936_checked

  · exact kid08_part942_checked

  · exact kid08_part948_checked

  · exact kid08_part931_checked

  · exact kid08_part937_checked

  · exact kid08_part943_checked

  · exact kid08_part949_checked

  · exact kid08_part932_checked

  · exact kid08_part938_checked

  · exact kid08_part944_checked

  · exact kid08_part950_checked

  · exact kid08_part933_checked

  · exact kid08_part939_checked

  · exact kid08_part945_checked

  · exact kid08_part951_checked

  · exact kid08_part934_checked

  · exact kid08_part940_checked

  · exact kid08_part946_checked

  · exact kid08_part952_checked

  · exact kid08_part935_checked

  · exact kid08_part941_checked

  · exact kid08_part947_checked

  · exact kid08_part953_checked

def kid08_part954 : Audit := .split 20 (5,false) (byMove [
.cycle 18 8 false (4),
.cycle 14 87 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.split 21 (4,false) (byMove [
.last 51 (4,true),
.cycle 12 12 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.last 28 (4,true),
.cycle 18 7 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 23 (4,true),
.cycle 20 2 true (1),
.last 104 (4,true),
.last 25 (4,true),
.last 30 (4,true),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.last 28 (4,true),
.cycle 18 8 false (4),
.last 47 (4,true),
.last 37 (4,true),
.last 23 (4,true),
.last 23 (4,true)
]),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 16 34 true (2),
.cycle 17 4 true (2),
.cycle 25 1 false (7),
.split 21 (4,true) (byMove [
.cycle 18 9 false (5),
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 25 1 false (7),
.last 25 (4,false),
.last 29 (4,false),
.cycle 32 1 false (10),
.last 24 (4,false),
.last 29 (4,false),
.last 33 (4,false),
.cycle 18 7 false (4),
.cycle 27 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 20 2 true (2),
.last 64 (4,false),
.last 25 (4,false),
.cycle 18 6 true (2),
.last 52 (4,false),
.last 24 (4,false),
.cycle 18 4 true (2)
]),
.cycle 19 2 true (2),
.cycle 15 12 true (1),
.cycle 18 6 false (4),
.cycle 36 1 false (8),
.cycle 21 1 false (1),
.split 21 (4,false) (byMove [
.cycle 18 9 false (4),
.last 29 (4,true),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.last 33 (4,true),
.cycle 16 6 true (1),
.cycle 17 5 false (4),
.last 27 (4,true),
.last 22 (4,true),
.cycle 19 3 false (3),
.last 28 (4,true),
.cycle 18 7 false (4),
.last 37 (4,true),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.last 33 (4,true),
.last 27 (4,true),
.cycle 18 6 false (4),
.last 27 (4,true),
.last 22 (4,true),
.cycle 18 4 false (4)
]),
.cycle 20 1 false (2),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.cycle 18 5 false (4),
.cycle 5 16 true (0),
.split 21 (4,true) (byMove [
.cycle 18 8 true (2),
.cycle 34 1 false (10),
.last 30 (4,false),
.last 27 (4,false),
.last 23 (4,false),
.cycle 19 3 false (3),
.cycle 6 16 true (0),
.last 25 (4,false),
.last 29 (4,false),
.cycle 0 57 true (0),
.last 24 (4,false),
.last 29 (4,false),
.last 33 (4,false),
.cycle 16 6 true (2),
.cycle 17 5 false (4),
.last 27 (4,false),
.last 23 (4,false),
.cycle 19 3 false (3),
.last 64 (4,false),
.last 25 (4,false),
.cycle 18 7 false (5),
.last 52 (4,false),
.last 24 (4,false),
.cycle 18 5 false (4)
]),
.cycle 18 3 false (4)
])
theorem kid08_part954_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid08_part954) = true := by rfl

def kid08_part955 : Audit := .cycle 0 51 true (0)
theorem kid08_part955_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid08_part955) = true := by rfl

def kid08_part956 : Audit := .split 28 (5,false) (byMove [
.cycle 1 81 true (0),
.cycle 1 55 true (0),
.cycle 27 2 true (7),
.cycle 0 30 true (0),
.split 29 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 1 52 true (0),
.cycle 1 39 true (0),
.cycle 39 1 false (5),
.last 30 (4,false),
.last 31 (4,false),
.cycle 0 30 true (0),
.cycle 1 81 true (0),
.cycle 1 55 true (0),
.cycle 9 21 true (0),
.last 30 (4,false),
.last 31 (4,false),
.cycle 19 12 true (4),
.cycle 26 8 true (6),
.cycle 0 32 true (0),
.cycle 1 37 true (0),
.last 30 (4,false),
.last 31 (4,false),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 16 34 true (2),
.cycle 1 61 true (0),
.last 30 (4,false),
.cycle 28 2 true (7)
]),
.cycle 1 29 true (0),
.cycle 0 29 true (0),
.cycle 26 22 true (6),
.cycle 20 9 true (4),
.cycle 16 32 true (2),
.split 29 (4,false) (byMove [
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 16 34 true (2),
.cycle 1 61 true (0),
.last 31 (4,true),
.cycle 28 2 true (8),
.cycle 0 30 true (0),
.cycle 1 52 true (0),
.cycle 1 39 true (0),
.cycle 21 9 true (4),
.cycle 29 1 true (9),
.cycle 28 2 true (8),
.cycle 19 12 true (4),
.cycle 27 4 true (7),
.cycle 0 32 true (0),
.cycle 16 32 true (2),
.last 31 (4,true),
.last 31 (4,true),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 26 22 true (6),
.cycle 16 38 true (2),
.cycle 29 1 true (9),
.cycle 28 2 true (8)
]),
.cycle 28 1 true (8),
.cycle 1 46 true (0),
.cycle 26 3 true (6),
.cycle 1 30 true (0),
.cycle 1 59 true (0),
.split 29 (4,true) (byMove [
.cycle 31 5 true (7),
.cycle 0 33 true (0),
.cycle 10 21 true (0),
.cycle 39 1 false (5),
.last 30 (4,false),
.last 31 (4,false),
.cycle 1 59 true (0),
.cycle 1 46 true (0),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.last 31 (4,false),
.cycle 1 30 true (0),
.cycle 26 5 true (6),
.cycle 1 32 true (0),
.cycle 1 61 true (0),
.cycle 11 19 true (0),
.last 30 (4,false),
.last 31 (4,false),
.cycle 26 24 true (6),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.last 31 (4,false),
.cycle 1 30 true (0)
]),
.cycle 18 11 true (4),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 1 54 true (0),
.split 29 (4,false) (byMove [
.cycle 26 24 true (6),
.cycle 19 11 true (4),
.cycle 27 3 true (7),
.cycle 0 31 true (0),
.last 30 (4,true),
.cycle 1 30 true (0),
.cycle 0 30 true (0),
.cycle 26 23 true (6),
.cycle 20 10 true (4),
.cycle 3 27 true (0),
.cycle 29 1 true (9),
.cycle 28 2 true (8),
.cycle 1 41 true (0),
.cycle 26 4 true (6),
.cycle 1 31 true (0),
.cycle 1 54 true (0),
.last 30 (4,true),
.cycle 18 12 true (4),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 1 55 true (0),
.cycle 29 1 true (9),
.cycle 28 2 true (8)
]),
.cycle 28 1 true (8)
])
theorem kid08_part956_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid08_part956) = true := by rfl

def kid08_part957 : Audit := .split 20 (5,false) (byMove [
.cycle 2 41 true (0),
.cycle 2 44 true (0),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 2 42 true (0),
.cycle 41 1 false (9),
.cycle 29 1 false (3),
.cycle 0 23 true (0),
.last 24 (4,false),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 2 41 true (0),
.cycle 2 44 true (0),
.cycle 3 19 true (0),
.last 22 (4,false),
.last 23 (4,false),
.cycle 2 32 true (0),
.cycle 19 8 true (4),
.cycle 2 22 true (0),
.cycle 17 27 true (3),
.last 24 (4,false),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.last 22 (4,false),
.cycle 20 2 true (5)
]),
.cycle 2 20 true (0),
.cycle 0 21 true (0),
.cycle 2 40 true (0),
.cycle 19 9 true (5),
.cycle 3 18 true (0),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.last 23 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 2 30 true (0),
.cycle 19 9 true (5),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 12 true (5),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 40 true (0),
.cycle 2 48 true (0),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 2 31 true (0),
.cycle 19 3 true (5),
.cycle 2 21 true (0),
.cycle 17 26 true (3),
.split 21 (4,true) (byMove [
.cycle 19 5 true (4),
.cycle 0 25 true (0),
.cycle 29 1 false (3),
.cycle 0 46 true (0),
.last 24 (4,false),
.cycle 0 25 true (0),
.cycle 17 26 true (3),
.cycle 2 31 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 2 41 true (0),
.cycle 23 5 true (5),
.cycle 2 23 true (0),
.cycle 17 5 true (3),
.cycle 5 17 true (0),
.last 24 (4,false),
.cycle 2 23 true (0),
.cycle 2 42 true (0),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 2 21 true (0)
]),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.split 21 (4,false) (byMove [
.cycle 2 42 true (0),
.cycle 19 11 true (5),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 2 41 true (0),
.cycle 19 10 true (5),
.cycle 3 19 true (0),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 2 32 true (0),
.cycle 19 4 true (5),
.cycle 2 22 true (0),
.cycle 17 27 true (3),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part957_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid08_part957) = true := by rfl

def kid08_part958 : Audit := .cycle 0 20 true (0)
theorem kid08_part958_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid08_part958) = true := by rfl

def kid08_part960 : Audit := .split 44 (5,false) (byMove [
.cycle 20 25 true (3),
.last 74 (4,false),
.cycle 43 2 true (9),
.cycle 0 46 true (0),
.last 72 (4,false),
.last 46 (4,false),
.cycle 0 45 true (0),
.cycle 21 24 true (3),
.cycle 43 9 true (9),
.cycle 3 42 true (0),
.last 45 (4,false),
.cycle 44 1 true (10),
.last 57 (4,false),
.cycle 43 3 true (9),
.last 47 (4,false),
.last 72 (4,false),
.cycle 40 5 true (7),
.cycle 18 27 true (3),
.cycle 0 45 true (0),
.cycle 1 44 true (0),
.cycle 2 43 true (0),
.last 73 (4,false),
.last 45 (4,false),
.cycle 44 1 true (10)
])
theorem kid08_part960_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid08_part960) = true := by rfl

def kid08_part961 : Audit := .split 29 (5,false) (byMove [
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.cycle 28 2 true (6),
.cycle 0 31 true (0),
.cycle 39 1 false (9),
.last 31 (4,false),
.cycle 0 30 true (0),
.cycle 0 53 true (0),
.cycle 21 9 true (3),
.cycle 36 1 false (10),
.last 30 (4,false),
.cycle 29 1 true (7),
.cycle 33 1 false (9),
.cycle 27 3 true (5),
.last 32 (4,false),
.cycle 40 1 false (12),
.cycle 0 34 true (0),
.cycle 34 1 false (8),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 25 58 true (3),
.last 30 (4,false),
.cycle 29 1 true (7)
])
theorem kid08_part961_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid08_part961) = true := by rfl

def kid08_part962 : Audit := .split 21 (5,false) (byMove [
.cycle 20 27 true (3),
.cycle 34 1 false (8),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.cycle 27 1 false (3),
.last 23 (4,false),
.cycle 0 22 true (0),
.last 55 (4,false),
.cycle 20 9 true (4),
.cycle 3 19 true (0),
.last 22 (4,false),
.cycle 21 1 true (5),
.last 34 (4,false),
.cycle 20 3 true (4),
.last 24 (4,false),
.cycle 5 83 true (0),
.cycle 27 1 false (3),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 21 1 true (5)
])
theorem kid08_part962_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid08_part962) = true := by rfl

def kid08_part963 : Audit := .cycle 0 21 true (0)
theorem kid08_part963_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid08_part963) = true := by rfl

def kid08_part964 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 22 1 true (2),
.last 23 (5,false),
.last 33 (5,false),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 30 1 false (6),
.cycle 34 1 false (8),
.cycle 22 1 true (2),
.last 23 (5,false)
])
theorem kid08_part964_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid08_part964) = true := by rfl

def kid08_part965 : Audit := .split 21 (4,false) (byMove [
.last 48 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.last 26 (5,false),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 20 34 true (4),
.last 30 (5,false),
.cycle 3 19 true (0),
.cycle 21 1 true (5),
.last 22 (5,false),
.cycle 20 13 true (3),
.last 24 (5,false),
.cycle 20 3 true (4),
.last 51 (5,false),
.last 26 (5,false),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 21 1 true (5),
.last 22 (5,false)
])
theorem kid08_part965_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid08_part965) = true := by rfl

def kid08_part966 : Audit := .cycle 0 20 true (0)
theorem kid08_part966_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid08_part966) = true := by rfl

def kid08_part967 : Audit := .split 51 (4,false) (byMove [
.cycle 20 33 true (4),
.last 61 (5,false),
.last 53 (5,false),
.cycle 0 53 true (0),
.cycle 19 33 true (4),
.cycle 50 2 true (12),
.cycle 0 52 true (0),
.cycle 20 32 true (4),
.last 60 (5,false),
.cycle 3 49 true (0),
.cycle 51 1 true (13),
.last 52 (5,false),
.cycle 40 13 true (8),
.last 54 (5,false),
.cycle 49 3 true (11),
.last 77 (5,false),
.cycle 39 13 true (8),
.cycle 18 34 true (4),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.last 78 (5,false),
.cycle 51 1 true (13),
.last 52 (5,false)
])
theorem kid08_part967_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid08_part967) = true := by rfl

def kid08_part968 : Audit := .split 28 (5,false) (byMove [
.last 82 (4,false),
.last 56 (4,false),
.cycle 27 2 true (7),
.cycle 0 30 true (0),
.last 56 (4,false),
.last 30 (4,false),
.cycle 0 29 true (0),
.cycle 27 22 true (7),
.cycle 20 9 true (4),
.cycle 17 32 true (3),
.last 29 (4,false),
.cycle 28 1 true (8),
.last 47 (4,false),
.cycle 26 3 true (6),
.last 31 (4,false),
.last 60 (4,false),
.cycle 27 3 true (7),
.cycle 18 11 true (4),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.last 55 (4,false),
.last 29 (4,false),
.cycle 28 1 true (8)
])
theorem kid08_part968_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid08_part968) = true := by rfl

def kid08_part969 : Audit := .cycle 3 17 true (0)
theorem kid08_part969_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid08_part969) = true := by rfl

def kid08_part970 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 55 (5,false),
.cycle 26 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4260880, 2, 16777216, 128, 256, 32768, 524290, 8192, 16777216, 128, 256, 2097152, 4, 524288, 16777216, 128, 256, 8, 2048, 2, 16777216, 16777216],[2, 4, 2048, 1, 16, 1024, 8192, 16384, 2048, 4096, 65536, 1024, 524288, 1048576, 2048, 262144, 4194304, 1024, 2, 4, 2048, 1, 16, 1024, 16777216],27412512⟩,
.last 40 (5,false),
.last 28 (5,false),
.cycle 20 1 true (6),
.last 21 (5,false),
.last 31 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 4 17 true (0),
.cycle 34 1 false (8),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4260880, 256, 16777216, 128, 256, 32768, 524290, 256, 16777216, 128, 256, 2097152, 4, 256, 16777216, 128, 256, 8, 2048, 256, 16777216, 16777216],[2, 4, 2048, 1, 16, 1024, 8192, 16384, 2048, 4096, 65536, 1024, 524288, 1048576, 2048, 262144, 4194304, 1024, 2, 4, 2048, 1, 16, 1024, 16777216],27412512⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4260880, 512, 16777216, 128, 256, 32768, 524290, 512, 16777216, 128, 256, 2097152, 4, 512, 16777216, 128, 256, 8, 2048, 512, 16777216, 16777216],[2, 4, 2048, 1, 16, 1024, 8192, 16384, 2048, 4096, 65536, 1024, 524288, 1048576, 2048, 262144, 4194304, 1024, 2, 4, 2048, 1, 16, 1024, 16777216],27412512⟩,
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part970_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid08_part970) = true := by rfl

def kid08_part971 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 76 (4,false),
.last 21 (4,false),
.last 23 (4,false),
.cycle 0 21 true (0),
.cycle 18 24 true (4),
.last 31 (4,false),
.last 52 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6),
.cycle 18 30 true (4),
.cycle 22 3 true (6),
.cycle 0 23 true (0),
.cycle 4 17 true (0),
.last 21 (4,false),
.last 25 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 41 (4,false),
.last 49 (4,false),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part971_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid08_part971) = true := by rfl

def kid08_part972 : Audit := .split 32 (4,false) (byMove [
.last 57 (5,false),
.last 42 (5,false),
.last 34 (5,false),
.cycle 0 34 true (0),
.cycle 37 1 false (9),
.cycle 31 2 true (7),
.cycle 0 33 true (0),
.last 56 (5,false),
.last 41 (5,false),
.cycle 3 30 true (0),
.cycle 32 1 true (8),
.last 33 (5,false),
.cycle 20 13 true (3),
.last 35 (5,false),
.cycle 30 3 true (6),
.cycle 28 28 true (4),
.last 37 (5,false),
.cycle 18 15 true (3),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 2 31 true (0),
.cycle 28 29 true (4),
.cycle 32 1 true (8),
.last 33 (5,false)
])
theorem kid08_part972_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid08_part972) = true := by rfl

def kid08_part973 : Audit := .split 22 (5,false) (byMove [
.cycle 16 29 true (2),
.last 34 (4,false),
.cycle 21 2 true (5),
.cycle 0 24 true (0),
.cycle 19 8 true (4),
.last 24 (4,false),
.cycle 0 23 true (0),
.last 46 (4,false),
.cycle 20 9 true (4),
.last 44 (4,false),
.last 23 (4,false),
.cycle 22 1 true (6),
.cycle 6 17 true (0),
.cycle 20 3 true (4),
.last 25 (4,false),
.last 54 (4,false),
.last 27 (4,false),
.cycle 18 5 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 16 31 true (2),
.last 23 (4,false),
.cycle 22 1 true (6)
])
theorem kid08_part973_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid08_part973) = true := by rfl

def kid08_part974 : Audit := .split 22 (4,false) (byMove [
.cycle 17 27 true (3),
.last 32 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 19 4 true (4),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 17 26 true (3),
.last 31 (5,false),
.cycle 3 20 true (0),
.cycle 22 1 true (6),
.last 23 (5,false),
.cycle 20 13 true (4),
.last 25 (5,false),
.cycle 20 3 true (4),
.cycle 17 32 true (3),
.cycle 17 7 true (3),
.cycle 18 5 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 17 33 true (3),
.cycle 22 1 true (6),
.last 23 (5,false)
])
theorem kid08_part974_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid08_part974) = true := by rfl

def kid08_part975 : Audit := .split 47 (5,false) (byMove [
.cycle 14 58 true (0),
.cycle 5 57 true (0),
.cycle 46 2 true (10),
.cycle 0 49 true (0),
.last 57 (4,false),
.last 49 (4,false),
.cycle 0 48 true (0),
.cycle 5 63 true (0),
.cycle 43 9 true (7),
.last 73 (4,false),
.last 48 (4,false),
.cycle 47 1 true (11),
.cycle 27 21 true (3),
.cycle 45 3 true (9),
.last 50 (4,false),
.cycle 5 75 true (0),
.cycle 11 38 true (0),
.cycle 5 77 true (0),
.cycle 0 48 true (0),
.cycle 1 47 true (0),
.cycle 2 46 true (0),
.cycle 20 29 true (3),
.last 48 (4,false),
.cycle 47 1 true (11)
])
theorem kid08_part975_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid08_part975) = true := by rfl

def kid08_part976 : Audit := .split 22 (4,false) (byMove [
.cycle 19 10 false (5),
.last 50 (5,false),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 26 (5,false),
.cycle 16 34 true (2),
.cycle 17 6 true (2),
.cycle 27 1 false (7),
.cycle 21 2 true (2),
.cycle 20 4 true (2),
.cycle 15 16 true (1),
.cycle 19 8 false (5),
.last 28 (5,false),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 26 (5,false),
.cycle 1 26 true (0),
.cycle 19 7 false (5),
.cycle 5 18 true (0),
.cycle 20 3 false (4),
.cycle 18 5 false (5)
])
theorem kid08_part976_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid08_part976) = true := by rfl

def kid08_part977 : Audit := .cycle 18 2 true (4)
theorem kid08_part977_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid08_part977) = true := by rfl

def kid08_part978 : Audit := .cycle 0 20 true (0)
theorem kid08_part978_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid08_part978) = true := by rfl

def kid08_part979 : Audit := .cycle 1 19 true (0)
theorem kid08_part979_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid08_part979) = true := by rfl

def kid08_part980 : Audit := .cycle 2 18 true (0)
theorem kid08_part980_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid08_part980) = true := by rfl

def kid08_part981 : Audit := .cycle 21 23 true (4)
theorem kid08_part981_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid08_part981) = true := by rfl

def kid08_part982 : Audit := .split 20 (4,false) (byMove [
.cycle 19 23 true (4),
.last 30 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 20 2 true (5),
.cycle 0 21 true (0),
.cycle 19 22 true (5),
.last 29 (5,false),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.last 21 (5,false),
.cycle 20 13 true (4),
.last 23 (5,false),
.cycle 20 3 true (5),
.cycle 19 26 true (4),
.cycle 19 3 true (5),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 19 27 true (5),
.cycle 20 1 true (6),
.last 21 (5,false)
])
theorem kid08_part982_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid08_part982) = true := by rfl

def kid08_part983 : Audit := .split 20 (5,false) (byMove [
.last 43 (4,false),
.last 46 (4,false),
.cycle 20 2 true (5),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 22 (4,false),
.cycle 0 21 true (0),
.last 42 (4,false),
.cycle 20 9 true (5),
.cycle 3 18 true (0),
.last 21 (4,false),
.cycle 20 1 true (6),
.last 33 (4,false),
.cycle 20 3 true (5),
.last 23 (4,false),
.cycle 18 26 true (4),
.last 23 (4,false),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.last 21 (4,false),
.cycle 20 1 true (6)
])
theorem kid08_part983_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid08_part983) = true := by rfl

def kid08_part959 : Audit := .split 19 (4,true) (byMove [(kid08_part960),(kid08_part961),(kid08_part962),(kid08_part963),(kid08_part964),(kid08_part965),(kid08_part966),(kid08_part967),(kid08_part968),(kid08_part969),(kid08_part970),(kid08_part971),(kid08_part972),(kid08_part973),(kid08_part974),(kid08_part975),(kid08_part976),(kid08_part977),(kid08_part978),(kid08_part979),(kid08_part980),(kid08_part981),(kid08_part982),(kid08_part983)])

theorem kid08_part959_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid08_part959) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid08_part960),(kid08_part961),(kid08_part962),(kid08_part963),(kid08_part964),(kid08_part965),(kid08_part966),(kid08_part967),(kid08_part968),(kid08_part969),(kid08_part970),(kid08_part971),(kid08_part972),(kid08_part973),(kid08_part974),(kid08_part975),(kid08_part976),(kid08_part977),(kid08_part978),(kid08_part979),(kid08_part980),(kid08_part981),(kid08_part982),(kid08_part983)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part960_checked

  · exact kid08_part966_checked

  · exact kid08_part972_checked

  · exact kid08_part978_checked

  · exact kid08_part961_checked

  · exact kid08_part967_checked

  · exact kid08_part973_checked

  · exact kid08_part979_checked

  · exact kid08_part962_checked

  · exact kid08_part968_checked

  · exact kid08_part974_checked

  · exact kid08_part980_checked

  · exact kid08_part963_checked

  · exact kid08_part969_checked

  · exact kid08_part975_checked

  · exact kid08_part981_checked

  · exact kid08_part964_checked

  · exact kid08_part970_checked

  · exact kid08_part976_checked

  · exact kid08_part982_checked

  · exact kid08_part965_checked

  · exact kid08_part971_checked

  · exact kid08_part977_checked

  · exact kid08_part983_checked

def kid08_part984 : Audit := .split 20 (5,false) (byMove [
.cycle 18 23 true (4),
.cycle 18 26 true (3),
.cycle 20 2 true (5),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 18 24 true (3),
.cycle 41 1 false (9),
.cycle 29 1 false (3),
.cycle 0 23 true (0),
.last 24 (4,false),
.last 29 (4,false),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 18 26 true (3),
.cycle 3 19 true (0),
.last 22 (4,false),
.last 23 (4,false),
.cycle 39 1 false (9),
.cycle 20 8 true (4),
.cycle 19 4 true (4),
.cycle 18 27 true (3),
.last 24 (4,false),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.last 22 (4,false),
.cycle 20 2 true (5)
]),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 18 22 true (4),
.cycle 20 9 true (5),
.cycle 3 18 true (0),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.last 23 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 18 25 true (4),
.cycle 19 12 true (5),
.cycle 20 9 true (5),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 20 12 true (6),
.cycle 20 4 true (6),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 18 22 true (4),
.cycle 18 30 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 19 13 true (4),
.cycle 20 3 true (5),
.cycle 19 3 true (5),
.cycle 18 26 true (4),
.split 21 (4,true) (byMove [
.cycle 20 5 true (4),
.cycle 0 25 true (0),
.cycle 29 1 false (3),
.cycle 72 1 false (12),
.last 24 (4,false),
.last 29 (4,false),
.cycle 18 26 true (4),
.cycle 19 13 true (4),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 19 3 true (5),
.cycle 23 5 true (5),
.cycle 19 5 true (4),
.cycle 17 5 true (3),
.cycle 5 17 true (0),
.last 24 (4,false),
.cycle 18 5 true (4),
.cycle 18 24 true (4),
.cycle 20 11 true (5),
.cycle 20 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 19 3 true (5)
]),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.split 21 (4,false) (byMove [
.cycle 18 24 true (4),
.cycle 20 11 true (5),
.cycle 20 3 true (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 19 3 true (5),
.cycle 0 22 true (0),
.cycle 18 23 true (4),
.cycle 20 10 true (6),
.cycle 3 19 true (0),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 19 14 true (5),
.cycle 20 4 true (6),
.cycle 19 4 true (5),
.cycle 18 27 true (4),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 28 true (4),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid08_part984_checked : zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid08_part984) = true := by rfl

def kid08_part864 : Audit := .split 18 (5,true) (byMove [(kid08_part865),(kid08_part866),(kid08_part867),(kid08_part868),(kid08_part869),(kid08_part894),(kid08_part895),(kid08_part896),(kid08_part897),(kid08_part898),(kid08_part899),(kid08_part924),(kid08_part925),(kid08_part926),(kid08_part927),(kid08_part928),(kid08_part929),(kid08_part954),(kid08_part955),(kid08_part956),(kid08_part957),(kid08_part958),(kid08_part959),(kid08_part984)])

theorem kid08_part864_checked : zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (kid08_part864) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid08_part865),(kid08_part866),(kid08_part867),(kid08_part868),(kid08_part869),(kid08_part894),(kid08_part895),(kid08_part896),(kid08_part897),(kid08_part898),(kid08_part899),(kid08_part924),(kid08_part925),(kid08_part926),(kid08_part927),(kid08_part928),(kid08_part929),(kid08_part954),(kid08_part955),(kid08_part956),(kid08_part957),(kid08_part958),(kid08_part959),(kid08_part984)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part865_checked

  · exact kid08_part895_checked

  · exact kid08_part925_checked

  · exact kid08_part955_checked

  · exact kid08_part866_checked

  · exact kid08_part896_checked

  · exact kid08_part926_checked

  · exact kid08_part956_checked

  · exact kid08_part867_checked

  · exact kid08_part897_checked

  · exact kid08_part927_checked

  · exact kid08_part957_checked

  · exact kid08_part868_checked

  · exact kid08_part898_checked

  · exact kid08_part928_checked

  · exact kid08_part958_checked

  · exact kid08_part869_checked

  · exact kid08_part899_checked

  · exact kid08_part929_checked

  · exact kid08_part959_checked

  · exact kid08_part894_checked

  · exact kid08_part924_checked

  · exact kid08_part954_checked

  · exact kid08_part984_checked

def kid08 : Audit := .split 17 (2,true) (byMove [(kid08_part1),(kid08_part2),(kid08_part3),(kid08_part4),(kid08_part5),(kid08_part126),(kid08_part247),(kid08_part248),(kid08_part249),(kid08_part250),(kid08_part251),(kid08_part372),(kid08_part493),(kid08_part494),(kid08_part495),(kid08_part496),(kid08_part497),(kid08_part618),(kid08_part739),(kid08_part740),(kid08_part741),(kid08_part742),(kid08_part743),(kid08_part864)])

theorem check08 : zipCheck 1271 (child ⟨false,true,2⟩) (kid08) = true := by

  change (zipQueryOK 1271 (child ⟨false,true,2⟩) 17 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (child ⟨false,true,2⟩) (2,true) (some mv)) (byMove [(kid08_part1),(kid08_part2),(kid08_part3),(kid08_part4),(kid08_part5),(kid08_part126),(kid08_part247),(kid08_part248),(kid08_part249),(kid08_part250),(kid08_part251),(kid08_part372),(kid08_part493),(kid08_part494),(kid08_part495),(kid08_part496),(kid08_part497),(kid08_part618),(kid08_part739),(kid08_part740),(kid08_part741),(kid08_part742),(kid08_part743),(kid08_part864)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid08_part1_checked

  · exact kid08_part247_checked

  · exact kid08_part493_checked

  · exact kid08_part739_checked

  · exact kid08_part2_checked

  · exact kid08_part248_checked

  · exact kid08_part494_checked

  · exact kid08_part740_checked

  · exact kid08_part3_checked

  · exact kid08_part249_checked

  · exact kid08_part495_checked

  · exact kid08_part741_checked

  · exact kid08_part4_checked

  · exact kid08_part250_checked

  · exact kid08_part496_checked

  · exact kid08_part742_checked

  · exact kid08_part5_checked

  · exact kid08_part251_checked

  · exact kid08_part497_checked

  · exact kid08_part743_checked

  · exact kid08_part126_checked

  · exact kid08_part372_checked

  · exact kid08_part618_checked

  · exact kid08_part864_checked

end BB6.Agent11Raw39B0RB
