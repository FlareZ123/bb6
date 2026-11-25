import Raw39B0RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid22_part1 : Audit := .cycle 1 9 true (1)
theorem kid22_part1_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,0⟩)) (kid22_part1) = true := by rfl

def kid22_part2 : Audit := .cycle 7 2 true (3)
theorem kid22_part2_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,1⟩)) (kid22_part2) = true := by rfl

def kid22_part4 : Audit := .cycle 0 10 true (0)
theorem kid22_part4_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part4) = true := by rfl

def kid22_part5 : Audit := .cycle 1 9 true (1)
theorem kid22_part5_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part5) = true := by rfl

def kid22_part6 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 29 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 29 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.last 19 (5,false),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.last 19 (5,false)
]),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 10 8 true (0),
.cycle 26 1 false (4),
.cycle 28 1 false (4),
.split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 0 19 true (0),
.last 38 (5,true),
.last 28 (5,true),
.cycle 11 8 true (0),
.cycle 10 10 true (0),
.cycle 18 1 true (4),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.last 36 (5,true),
.last 42 (5,true),
.cycle 30 1 false (4),
.cycle 18 1 true (4)
]),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 30 1 false (6),
.cycle 21 1 false (1),
.split 18 (5,true) (byMove [
.cycle 25 1 false (1),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.last 20 (5,false),
.last 20 (5,false),
.cycle 15 8 true (1),
.cycle 23 1 false (1),
.cycle 32 1 false (6),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 52 1 false (6),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 17 2 true (2),
.last 20 (5,false)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 22 1 false (2),
.split 18 (5,false) (byMove [
.last 38 (5,true),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 17 2 true (3),
.last 19 (5,true),
.cycle 0 19 true (0),
.last 37 (5,true),
.cycle 10 9 true (0),
.cycle 3 16 true (0),
.cycle 2 18 true (0),
.cycle 18 1 true (4),
.cycle 32 1 false (4),
.cycle 16 3 true (2),
.cycle 22 1 false (2),
.last 40 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.last 41 (5,true),
.cycle 24 1 false (2),
.cycle 18 1 true (4)
])
])
theorem kid22_part6_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part6) = true := by rfl

def kid22_part7 : Audit := .cycle 17 1 false (1)
theorem kid22_part7_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part7) = true := by rfl

def kid22_part8 : Audit := .cycle 21 1 false (1)
theorem kid22_part8_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part8) = true := by rfl

def kid22_part10 : Audit := .cycle 0 11 true (0)
theorem kid22_part10_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part10) = true := by rfl

def kid22_part11 : Audit := .cycle 1 10 true (1)
theorem kid22_part11_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part11) = true := by rfl

def kid22_part12 : Audit := .cycle 21 1 false (1)
theorem kid22_part12_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part12) = true := by rfl

def kid22_part13 : Audit := .cycle 24 1 false (2)
theorem kid22_part13_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part13) = true := by rfl

def kid22_part14 : Audit := .cycle 16 1 false (-2)
theorem kid22_part14_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part14) = true := by rfl

def kid22_part15 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.cycle 12 5 false (1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 25 1 false (3),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part15_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part15) = true := by rfl

def kid22_part16 : Audit := .cycle 0 11 true (0)
theorem kid22_part16_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part16) = true := by rfl

def kid22_part17 : Audit := .cycle 1 10 true (1)
theorem kid22_part17_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part17) = true := by rfl

def kid22_part18 : Audit := .split 19 (4,true) (byMove [
.last 23 (5,true),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.last 25 (5,true),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.cycle 22 8 true (2),
.cycle 0 21 true (0),
.cycle 41 1 false (7),
.last 20 (5,true),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 54 true (0),
.last 23 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.last 23 (5,true),
.last 20 (5,true)
])
theorem kid22_part18_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part18) = true := by rfl

def kid22_part19 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 11 8 true (0),
.cycle 26 1 false (4),
.cycle 28 1 false (4),
.cycle 10 8 true (0),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 30 1 false (6),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.last 20 (5,true),
.cycle 3 16 true (0)
])
theorem kid22_part19_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part19) = true := by rfl

def kid22_part20 : Audit := .split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 56 1 false (6),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.cycle 32 1 false (4),
.cycle 10 10 true (0),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.cycle 24 1 false (2),
.cycle 34 1 false (6),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.last 22 (5,true),
.cycle 2 20 true (0)
])
theorem kid22_part20_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part20) = true := by rfl

def kid22_part21 : Audit := .cycle 10 1 true (2)
theorem kid22_part21_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part21) = true := by rfl

def kid22_part22 : Audit := .split 15 (5,true) (byMove [
.cycle 0 32 true (0),
.cycle 16 15 false (1),
.cycle 24 1 false (-2),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 16 6 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 23 (4,true),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 10 6 true (1),
.cycle 21 5 false (1),
.last 17 (4,true),
.cycle 14 13 false (2),
.cycle 33 1 false (1),
.last 16 (4,true),
.last 20 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 16 8 false (2),
.cycle 21 11 false (2)
])
theorem kid22_part22_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part22) = true := by rfl

def kid22_part23 : Audit := .split 13 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (1),
.cycle 20 1 false (-2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 29 1 false (1),
.cycle 10 4 true (1),
.cycle 20 5 false (0),
.last 15 (4,true),
.cycle 11 11 false (2),
.cycle 29 1 false (1),
.last 14 (4,true),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 15 6 false (1),
.last 16 (4,true)
])
theorem kid22_part23_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part23) = true := by rfl

def kid22_part24 : Audit := .cycle 0 13 true (0)
theorem kid22_part24_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part24) = true := by rfl

def kid22_part25 : Audit := .cycle 18 1 false (0)
theorem kid22_part25_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part25) = true := by rfl

def kid22_part26 : Audit := .cycle 16 1 false (-2)
theorem kid22_part26_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part26) = true := by rfl

def kid22_part27 : Audit := .split 12 (5,true) (byMove [
.cycle 0 21 true (-1),
.last 37 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 14 (4,true),
.cycle 14 1 false (0),
.cycle 24 1 false (4),
.last 13 (4,true),
.cycle 15 1 false (3),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 35 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.last 32 (4,true),
.last 13 (4,true),
.cycle 13 3 true (1)
])
theorem kid22_part27_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part27) = true := by rfl

def kid22_part28 : Audit := .cycle 0 11 true (0)
theorem kid22_part28_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part28) = true := by rfl

def kid22_part29 : Audit := .cycle 1 10 true (1)
theorem kid22_part29_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part29) = true := by rfl

def kid22_part30 : Audit := .cycle 2 9 true (1)
theorem kid22_part30_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part30) = true := by rfl

def kid22_part31 : Audit := .cycle 1 13 true (1)
theorem kid22_part31_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part31) = true := by rfl

def kid22_part32 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (4),
.cycle 24 3 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 17 3 false (0),
.cycle 0 17 true (0),
.cycle 24 3 false (4),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.cycle 17 3 false (2),
.cycle 14 5 false (2),
.cycle 15 3 false (1),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 18 (4,true),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 3 false (3),
.cycle 27 3 false (5),
.cycle 17 3 false (1),
.cycle 13 4 true (0)
])
theorem kid22_part32_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part32) = true := by rfl

def kid22_part33 : Audit := .cycle 10 1 true (2)
theorem kid22_part33_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part33) = true := by rfl

def kid22_part9 : Audit := .split 10 (5,false) (byMove [(kid22_part10),(kid22_part11),(kid22_part12),(kid22_part13),(kid22_part14),(kid22_part15),(kid22_part16),(kid22_part17),(kid22_part18),(kid22_part19),(kid22_part20),(kid22_part21),(kid22_part22),(kid22_part23),(kid22_part24),(kid22_part25),(kid22_part26),(kid22_part27),(kid22_part28),(kid22_part29),(kid22_part30),(kid22_part31),(kid22_part32),(kid22_part33)])

theorem kid22_part9_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part9) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part10),(kid22_part11),(kid22_part12),(kid22_part13),(kid22_part14),(kid22_part15),(kid22_part16),(kid22_part17),(kid22_part18),(kid22_part19),(kid22_part20),(kid22_part21),(kid22_part22),(kid22_part23),(kid22_part24),(kid22_part25),(kid22_part26),(kid22_part27),(kid22_part28),(kid22_part29),(kid22_part30),(kid22_part31),(kid22_part32),(kid22_part33)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part10_checked

  · exact kid22_part16_checked

  · exact kid22_part22_checked

  · exact kid22_part28_checked

  · exact kid22_part11_checked

  · exact kid22_part17_checked

  · exact kid22_part23_checked

  · exact kid22_part29_checked

  · exact kid22_part12_checked

  · exact kid22_part18_checked

  · exact kid22_part24_checked

  · exact kid22_part30_checked

  · exact kid22_part13_checked

  · exact kid22_part19_checked

  · exact kid22_part25_checked

  · exact kid22_part31_checked

  · exact kid22_part14_checked

  · exact kid22_part20_checked

  · exact kid22_part26_checked

  · exact kid22_part32_checked

  · exact kid22_part15_checked

  · exact kid22_part21_checked

  · exact kid22_part27_checked

  · exact kid22_part33_checked

def kid22_part34 : Audit := .cycle 0 10 true (0)
theorem kid22_part34_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part34) = true := by rfl

def kid22_part35 : Audit := .cycle 1 9 true (1)
theorem kid22_part35_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part35) = true := by rfl

def kid22_part36 : Audit := .split 19 (4,true) (byMove [
.cycle 55 1 false (13),
.cycle 36 1 false (10),
.cycle 34 1 false (10),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.split 20 (5,true) (byMove [
.cycle 0 61 true (0),
.cycle 49 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 55 1 false (13),
.cycle 34 1 false (10),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.last 21 (5,false),
.cycle 16 41 true (0),
.cycle 16 37 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 1 44 true (0),
.cycle 0 55 true (0),
.cycle 40 1 false (10),
.cycle 36 1 false (10),
.last 21 (5,false)
]),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.cycle 9 12 true (0),
.cycle 0 49 true (0),
.cycle 52 1 false (10),
.split 20 (5,true) (byMove [
.last 32 (5,false),
.cycle 0 24 true (0),
.last 28 (5,false),
.last 34 (5,false),
.cycle 24 1 false (4),
.last 21 (5,false),
.cycle 0 49 true (0),
.cycle 7 14 true (0),
.cycle 9 12 true (0),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 24 (5,false),
.last 44 (5,false),
.cycle 0 55 true (0),
.last 26 (5,false),
.cycle 36 1 false (10),
.last 21 (5,false),
.cycle 0 57 true (0),
.last 32 (5,false),
.last 30 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false)
]),
.cycle 31 1 false (7),
.cycle 18 2 true (2),
.cycle 25 1 false (7),
.cycle 36 1 false (10),
.cycle 23 1 false (1),
.split 20 (5,true) (byMove [
.cycle 9 16 true (0),
.cycle 0 50 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 36 1 false (10),
.cycle 31 1 false (7),
.cycle 25 1 false (7),
.cycle 27 1 false (7),
.last 22 (5,false),
.last 24 (5,false),
.cycle 17 8 true (1),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 4, 64, 64],[8, 10, 8, 8, 32, 2, 64],96⟩,
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 47 14 true (7),
.cycle 24 12 true (4),
.cycle 9 14 true (0),
.cycle 5 16 true (0),
.cycle 19 2 true (2),
.last 24 (5,false)
]),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.cycle 2 38 true (0),
.cycle 20 28 true (3),
.cycle 21 10 true (4),
.split 20 (5,true) (byMove [
.last 32 (5,false),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.last 34 (5,false),
.last 22 (5,false),
.last 23 (5,false),
.last 47 (5,false),
.last 57 (5,false),
.last 40 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 24 (5,false),
.last 26 (5,false),
.cycle 9 14 true (0),
.cycle 5 16 true (0),
.cycle 19 2 true (3),
.last 23 (5,false),
.cycle 0 57 true (0),
.last 32 (5,false),
.last 30 (5,false),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 22 (5,false)
])
])
theorem kid22_part36_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part36) = true := by rfl

def kid22_part37 : Audit := .split 17 (4,true) (byMove [
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.cycle 19 1 false (3),
.cycle 30 1 false (6),
.cycle 21 1 false (1),
.split 18 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 30 1 false (6),
.cycle 28 1 false (6),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.last 19 (5,false),
.cycle 41 1 false (5),
.cycle 37 1 false (5),
.cycle 32 1 false (6),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 3 20 true (0),
.cycle 3 18 true (0),
.cycle 0 21 true (0),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.last 19 (5,false)
]),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.cycle 19 8 true (2),
.cycle 0 19 true (0),
.cycle 37 1 false (7),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.cycle 21 1 false (3),
.last 19 (5,false),
.cycle 0 19 true (0),
.last 41 (5,false),
.cycle 10 10 true (0),
.last 26 (5,false),
.last 28 (5,false),
.last 19 (5,false),
.cycle 3 20 true (0),
.cycle 3 18 true (0),
.cycle 0 21 true (0),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 20 18 true (2),
.cycle 5 38 true (0),
.last 28 (5,false),
.last 19 (5,false)
]),
.cycle 25 1 false (5),
.cycle 16 2 true (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 21 1 false (1),
.split 18 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 14 32 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 23 1 false (5),
.cycle 25 1 false (5),
.cycle 0 21 true (0),
.cycle 30 1 false (8),
.last 20 (5,false),
.last 21 (5,false),
.cycle 15 8 true (1),
.cycle 14 32 true (0),
.cycle 25 1 false (5),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 27 24 true (3),
.cycle 3 22 true (0),
.cycle 0 21 true (0),
.cycle 0 47 true (0),
.cycle 17 2 true (2),
.last 21 (5,false)
]),
.cycle 0 48 true (0),
.cycle 3 18 true (0),
.cycle 3 16 true (0),
.cycle 0 19 true (0),
.cycle 3 18 true (0),
.split 18 (5,true) (byMove [
.cycle 22 20 true (2),
.cycle 29 1 false (5),
.cycle 27 1 false (5),
.cycle 0 20 true (0),
.last 20 (5,false),
.last 21 (5,false),
.cycle 0 19 true (0),
.last 48 (5,false),
.last 27 (5,false),
.cycle 3 16 true (0),
.cycle 2 18 true (0),
.last 19 (5,false),
.last 30 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.last 45 (5,false),
.cycle 17 2 true (3),
.last 21 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 3 18 true (0),
.last 19 (5,false)
])
])
theorem kid22_part37_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part37) = true := by rfl

def kid22_part38 : Audit := .split 19 (4,true) (byMove [
.cycle 34 1 false (6),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.cycle 36 1 false (6),
.cycle 23 1 false (1),
.split 20 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 36 1 false (6),
.cycle 34 1 false (6),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.last 21 (5,false),
.cycle 49 1 false (5),
.cycle 45 1 false (5),
.cycle 38 1 false (6),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 2 24 true (0),
.cycle 2 22 true (0),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 21 (5,false)
]),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.cycle 22 8 true (2),
.cycle 0 21 true (0),
.cycle 41 1 false (7),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.cycle 25 1 false (3),
.last 21 (5,false),
.cycle 0 21 true (0),
.last 45 (5,false),
.cycle 11 10 true (0),
.last 28 (5,false),
.last 30 (5,false),
.last 21 (5,false),
.cycle 2 24 true (0),
.cycle 2 22 true (0),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 21 22 true (2),
.cycle 5 42 true (0),
.last 32 (5,false),
.last 21 (5,false)
]),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 23 1 false (1),
.split 20 (5,true) (byMove [
.last 25 (5,false),
.cycle 16 34 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 27 1 false (5),
.cycle 29 1 false (5),
.last 23 (5,false),
.cycle 34 1 false (8),
.last 22 (5,false),
.last 23 (5,false),
.cycle 17 8 true (1),
.last 24 (5,false),
.cycle 29 1 false (5),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.last 21 (5,false),
.cycle 31 26 true (3),
.cycle 2 26 true (0),
.last 23 (5,false),
.cycle 0 51 true (0),
.cycle 19 2 true (2),
.last 23 (5,false)
]),
.cycle 0 54 true (0),
.cycle 2 22 true (0),
.cycle 2 20 true (0),
.cycle 0 21 true (0),
.cycle 2 22 true (0),
.split 20 (5,true) (byMove [
.cycle 23 24 true (2),
.cycle 35 1 false (5),
.cycle 33 1 false (5),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 23 (5,false),
.cycle 0 21 true (0),
.last 54 (5,false),
.last 29 (5,false),
.cycle 3 18 true (0),
.cycle 2 20 true (0),
.last 21 (5,false),
.last 34 (5,false),
.last 23 (5,false),
.last 23 (5,false),
.last 49 (5,false),
.cycle 19 2 true (3),
.last 23 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 2 22 true (0),
.last 21 (5,false)
])
])
theorem kid22_part38_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part38) = true := by rfl

def kid22_part40 : Audit := .cycle 0 11 true (0)
theorem kid22_part40_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part40) = true := by rfl

def kid22_part41 : Audit := .cycle 1 10 true (1)
theorem kid22_part41_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part41) = true := by rfl

def kid22_part42 : Audit := .split 19 (4,true) (byMove [
.cycle 34 1 false (6),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.cycle 36 1 false (6),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.cycle 22 8 true (2),
.cycle 0 21 true (0),
.cycle 41 1 false (7),
.last 20 (5,true),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.last 21 (5,true),
.cycle 27 1 false (5),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 54 true (0),
.cycle 2 22 true (0),
.cycle 2 20 true (0),
.cycle 0 21 true (0),
.cycle 2 22 true (0),
.last 20 (5,true)
])
theorem kid22_part42_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part42) = true := by rfl

def kid22_part43 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 11 8 true (0),
.cycle 26 1 false (4),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.last 19 (5,true),
.cycle 30 1 false (6),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 34 1 false (6),
.cycle 0 20 true (0)
])
theorem kid22_part43_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part43) = true := by rfl

def kid22_part44 : Audit := .split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 56 1 false (6),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.cycle 32 1 false (4),
.cycle 26 1 false (2),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.last 21 (5,true),
.cycle 34 1 false (6),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.cycle 28 1 false (2),
.cycle 19 2 true (3)
])
theorem kid22_part44_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part44) = true := by rfl

def kid22_part45 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 24 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 12 7 false (2),
.cycle 12 5 false (2),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 27 1 false (5),
.cycle 17 1 false (1),
.cycle 13 2 true (0)
])
theorem kid22_part45_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part45) = true := by rfl

def kid22_part46 : Audit := .cycle 0 11 true (0)
theorem kid22_part46_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part46) = true := by rfl

def kid22_part47 : Audit := .cycle 1 10 true (1)
theorem kid22_part47_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part47) = true := by rfl

def kid22_part48 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.last 27 (5,true),
.last 25 (5,true),
.cycle 24 15 true (4),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 0 25 true (0),
.cycle 36 26 true (6),
.last 23 (5,true),
.cycle 44 30 true (4),
.cycle 69 1 false (13),
.last 22 (5,true),
.cycle 37 1 false (9),
.cycle 20 2 true (2),
.last 23 (5,true),
.cycle 33 1 false (9),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 23 (5,true),
.cycle 5 17 true (0),
.cycle 23 13 true (5),
.last 22 (5,true)
])
theorem kid22_part48_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part48) = true := by rfl

def kid22_part49 : Audit := .split 19 (4,true) (byMove [
.last 23 (5,true),
.cycle 36 1 false (10),
.cycle 34 1 false (10),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.last 21 (5,true),
.cycle 0 49 true (0),
.cycle 52 1 false (10),
.last 20 (5,true),
.cycle 31 1 false (7),
.cycle 18 2 true (2),
.last 21 (5,true),
.cycle 36 1 false (10),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 21 (5,true),
.cycle 20 28 true (3),
.cycle 21 10 true (4),
.last 20 (5,true)
])
theorem kid22_part49_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part49) = true := by rfl

def kid22_part50 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.cycle 0 30 true (0),
.cycle 26 1 false (4),
.cycle 0 27 true (0),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 6 16 true (0),
.cycle 46 14 true (8),
.last 23 (5,true),
.cycle 0 53 true (0),
.cycle 56 1 false (10),
.last 22 (5,true),
.cycle 35 1 false (7),
.cycle 20 2 true (2),
.last 23 (5,true),
.cycle 40 1 false (10),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 23 (5,true),
.cycle 22 30 true (3),
.cycle 23 12 true (4),
.last 22 (5,true)
])
theorem kid22_part50_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part50) = true := by rfl

def kid22_part51 : Audit := .cycle 10 1 true (4)
theorem kid22_part51_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part51) = true := by rfl

def kid22_part52 : Audit := .cycle 7 5 true (3)
theorem kid22_part52_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part52) = true := by rfl

def kid22_part53 : Audit := .cycle 9 3 true (3)
theorem kid22_part53_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part53) = true := by rfl

def kid22_part54 : Audit := .cycle 0 13 true (0)
theorem kid22_part54_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part54) = true := by rfl

def kid22_part55 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.cycle 20 8 true (2),
.cycle 0 19 true (0),
.cycle 38 1 false (6),
.last 18 (5,true),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.last 19 (5,true),
.cycle 24 1 false (4),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 48 true (0),
.cycle 4 18 true (0),
.cycle 4 16 true (0),
.cycle 0 19 true (0),
.cycle 4 18 true (0),
.last 18 (5,true)
])
theorem kid22_part55_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part55) = true := by rfl

def kid22_part56 : Audit := .split 19 (4,true) (byMove [
.cycle 29 1 false (3),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 31 1 false (3),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.cycle 24 8 true (2),
.cycle 0 21 true (0),
.cycle 42 1 false (6),
.last 20 (5,true),
.cycle 30 1 false (4),
.cycle 18 2 true (2),
.last 21 (5,true),
.cycle 28 1 false (4),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 54 true (0),
.cycle 32 1 false (2),
.cycle 30 1 false (2),
.cycle 0 21 true (0),
.cycle 32 1 false (2),
.last 20 (5,true)
])
theorem kid22_part56_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part56) = true := by rfl

def kid22_part57 : Audit := .split 14 (5,true) (byMove [
.cycle 16 23 true (0),
.last 20 (4,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 16 (4,true),
.cycle 20 1 false (6),
.last 18 (4,true),
.last 15 (4,true),
.cycle 19 1 false (5),
.last 17 (4,true),
.last 33 (4,true),
.last 19 (4,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 16 (4,true),
.cycle 16 24 true (2),
.last 18 (4,true),
.last 15 (4,true),
.cycle 17 3 true (3)
])
theorem kid22_part57_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part57) = true := by rfl

def kid22_part58 : Audit := .cycle 0 11 true (0)
theorem kid22_part58_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part58) = true := by rfl

def kid22_part59 : Audit := .cycle 1 10 true (1)
theorem kid22_part59_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part59) = true := by rfl

def kid22_part60 : Audit := .cycle 2 9 true (1)
theorem kid22_part60_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part60) = true := by rfl

def kid22_part61 : Audit := .cycle 1 13 true (1)
theorem kid22_part61_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part61) = true := by rfl

def kid22_part62 : Audit := .cycle 8 3 true (3)
theorem kid22_part62_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part62) = true := by rfl

def kid22_part63 : Audit := .cycle 10 1 true (4)
theorem kid22_part63_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part63) = true := by rfl

def kid22_part39 : Audit := .split 10 (5,false) (byMove [(kid22_part40),(kid22_part41),(kid22_part42),(kid22_part43),(kid22_part44),(kid22_part45),(kid22_part46),(kid22_part47),(kid22_part48),(kid22_part49),(kid22_part50),(kid22_part51),(kid22_part52),(kid22_part53),(kid22_part54),(kid22_part55),(kid22_part56),(kid22_part57),(kid22_part58),(kid22_part59),(kid22_part60),(kid22_part61),(kid22_part62),(kid22_part63)])

theorem kid22_part39_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part39) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part40),(kid22_part41),(kid22_part42),(kid22_part43),(kid22_part44),(kid22_part45),(kid22_part46),(kid22_part47),(kid22_part48),(kid22_part49),(kid22_part50),(kid22_part51),(kid22_part52),(kid22_part53),(kid22_part54),(kid22_part55),(kid22_part56),(kid22_part57),(kid22_part58),(kid22_part59),(kid22_part60),(kid22_part61),(kid22_part62),(kid22_part63)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part40_checked

  · exact kid22_part46_checked

  · exact kid22_part52_checked

  · exact kid22_part58_checked

  · exact kid22_part41_checked

  · exact kid22_part47_checked

  · exact kid22_part53_checked

  · exact kid22_part59_checked

  · exact kid22_part42_checked

  · exact kid22_part48_checked

  · exact kid22_part54_checked

  · exact kid22_part60_checked

  · exact kid22_part43_checked

  · exact kid22_part49_checked

  · exact kid22_part55_checked

  · exact kid22_part61_checked

  · exact kid22_part44_checked

  · exact kid22_part50_checked

  · exact kid22_part56_checked

  · exact kid22_part62_checked

  · exact kid22_part45_checked

  · exact kid22_part51_checked

  · exact kid22_part57_checked

  · exact kid22_part63_checked

def kid22_part64 : Audit := .cycle 6 8 true (2)
theorem kid22_part64_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part64) = true := by rfl

def kid22_part65 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 23 7 false (1),
.cycle 19 5 false (1),
.cycle 0 15 true (0),
.cycle 24 1 false (-2),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 32 1 false (2),
.cycle 24 1 false (-2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 27 true (0),
.cycle 23 1 false (3),
.cycle 27 1 false (3),
.last 15 (5,false),
.cycle 27 7 false (1),
.cycle 20 5 false (1),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 24 1 false (-2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 23 7 false (1),
.last 15 (5,false)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.cycle 2 13 true (1),
.split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 23 7 false (2),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 24 (5,true),
.cycle 12 8 true (2),
.cycle 12 10 true (2),
.cycle 14 1 true (4),
.cycle 11 7 true (2),
.cycle 10 5 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 23 7 false (2),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (2),
.cycle 14 1 true (4)
]),
.cycle 6 8 true (2),
.cycle 12 2 true (2),
.cycle 19 5 false (1),
.cycle 1 15 true (1),
.cycle 24 1 false (-2),
.split 14 (5,true) (byMove [
.cycle 10 12 true (1),
.cycle 0 18 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 24 1 false (-2),
.last 15 (5,false),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 9 6 true (2),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 12 8 true (1),
.cycle 20 5 false (1),
.cycle 1 17 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (-2),
.last 15 (5,false),
.cycle 1 15 true (1),
.cycle 11 6 true (2),
.cycle 11 4 true (2),
.cycle 0 16 true (0),
.cycle 13 2 true (2),
.last 16 (5,false)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 4 true (2),
.split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 11 6 true (2),
.cycle 11 4 true (2),
.cycle 0 16 true (0),
.cycle 13 2 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (2),
.cycle 3 12 true (1),
.cycle 2 14 true (1),
.cycle 14 1 true (4),
.cycle 6 9 true (2),
.cycle 12 3 true (2),
.last 18 (5,true),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 5 true (2),
.cycle 14 1 true (4)
])
])
theorem kid22_part65_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part65) = true := by rfl

def kid22_part66 : Audit := .cycle 0 12 true (0)
theorem kid22_part66_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part66) = true := by rfl

def kid22_part67 : Audit := .split 15 (4,true) (byMove [
.cycle 26 1 false (4),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 0 17 true (0),
.cycle 19 1 false (1),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 26 1 false (2),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 26 1 false (4),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 19 1 false (3),
.last 17 (5,false),
.cycle 32 1 false (4),
.cycle 30 1 false (4),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.last 17 (5,false)
]),
.cycle 0 16 true (0),
.cycle 41 1 false (5),
.cycle 10 8 true (0),
.cycle 23 1 false (3),
.cycle 25 1 false (3),
.split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.last 18 (5,true),
.cycle 0 17 true (0),
.last 34 (5,true),
.last 26 (5,true),
.cycle 10 8 true (0),
.cycle 10 10 true (0),
.cycle 16 1 true (4),
.last 40 (5,true),
.last 38 (5,true),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 19 1 false (1),
.last 18 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 32 (5,true),
.last 38 (5,true),
.cycle 25 1 false (3),
.cycle 16 1 true (4)
]),
.cycle 20 1 false (2),
.cycle 14 2 true (2),
.cycle 17 1 false (1),
.cycle 27 1 false (5),
.cycle 19 1 false (1),
.split 16 (5,true) (byMove [
.cycle 12 31 true (0),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 0 18 true (0),
.last 18 (5,false),
.last 18 (5,false),
.cycle 13 8 true (1),
.cycle 24 1 false (2),
.cycle 29 1 false (5),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 45 1 false (5),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.cycle 0 18 true (0),
.cycle 15 2 true (2),
.last 18 (5,false)
]),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 17 19 true (2),
.cycle 29 1 false (5),
.split 16 (5,false) (byMove [
.last 34 (5,true),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.cycle 0 18 true (0),
.cycle 15 2 true (3),
.last 17 (5,true),
.cycle 0 17 true (0),
.last 33 (5,true),
.cycle 10 9 true (0),
.cycle 3 14 true (0),
.cycle 2 16 true (0),
.cycle 16 1 true (4),
.cycle 27 1 false (3),
.cycle 14 3 true (2),
.cycle 23 1 false (3),
.last 36 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.last 37 (5,true),
.last 38 (5,true),
.cycle 16 1 true (4)
])
])
theorem kid22_part67_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part67) = true := by rfl

def kid22_part68 : Audit := .split 17 (4,true) (byMove [
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 30 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 30 1 false (4),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.last 19 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 29 1 false (3),
.cycle 33 1 false (5),
.cycle 23 1 false (1),
.last 19 (5,false)
]),
.cycle 0 18 true (0),
.cycle 43 1 false (3),
.cycle 12 8 true (0),
.cycle 27 1 false (3),
.cycle 29 1 false (3),
.split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 29 1 false (3),
.cycle 33 1 false (5),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 19 true (0),
.last 38 (5,true),
.last 28 (5,true),
.cycle 12 8 true (0),
.cycle 12 10 true (0),
.cycle 18 1 true (4),
.last 24 (5,true),
.last 22 (5,true),
.cycle 0 21 true (0),
.cycle 27 1 false (3),
.cycle 23 1 false (1),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.last 36 (5,true),
.last 42 (5,true),
.cycle 25 1 false (1),
.cycle 18 1 true (4)
]),
.cycle 24 1 false (2),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.split 18 (5,true) (byMove [
.cycle 17 5 false (3),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.last 20 (5,false),
.last 20 (5,false),
.cycle 15 8 true (1),
.last 22 (5,false),
.cycle 33 1 false (5),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 47 1 false (3),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 20 true (0),
.cycle 17 2 true (2),
.last 20 (5,false)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 17 4 true (2),
.split 18 (5,false) (byMove [
.last 38 (5,true),
.last 23 (5,true),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 17 2 true (3),
.last 19 (5,true),
.cycle 0 19 true (0),
.last 37 (5,true),
.cycle 12 9 true (0),
.cycle 3 16 true (0),
.cycle 2 18 true (0),
.cycle 18 1 true (4),
.cycle 27 1 false (1),
.cycle 16 3 true (2),
.last 21 (5,true),
.last 40 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.last 41 (5,true),
.last 22 (5,true),
.cycle 18 1 true (4)
])
])
theorem kid22_part68_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part68) = true := by rfl

def kid22_part70 : Audit := .split 14 (5,true) (byMove [
.cycle 11 8 true (1),
.cycle 0 30 true (-1),
.cycle 18 1 false (0),
.cycle 27 1 false (1),
.last 15 (4,true),
.cycle 0 18 false (4),
.cycle 1 15 true (1),
.cycle 7 16 true (1),
.cycle 9 12 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 17 true (0),
.last 17 (4,true),
.last 16 (4,true),
.last 21 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.cycle 15 6 false (1),
.cycle 1 15 true (1),
.cycle 13 4 true (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 17 true (1)
])
theorem kid22_part70_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part70) = true := by rfl

def kid22_part71 : Audit := .cycle 0 14 true (0)
theorem kid22_part71_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part71) = true := by rfl

def kid22_part72 : Audit := .split 17 (4,true) (byMove [
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 43 1 false (3),
.cycle 12 8 true (0),
.cycle 27 1 false (3),
.cycle 29 1 false (3),
.cycle 29 1 false (3),
.cycle 24 1 false (2),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.last 20 (5,true),
.last 20 (5,true)
])
theorem kid22_part72_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part72) = true := by rfl

def kid22_part73 : Audit := .split 16 (5,true) (byMove [
.cycle 13 8 true (1),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 28 1 false (4),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 19 1 false (3),
.last 19 (4,true),
.cycle 14 3 false (3),
.cycle 30 1 false (4),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 36 1 false (2),
.cycle 15 4 true (2),
.cycle 15 2 true (2),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 0 20 true (0)
])
theorem kid22_part73_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part73) = true := by rfl

def kid22_part74 : Audit := .cycle 16 1 false (-2)
theorem kid22_part74_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part74) = true := by rfl

def kid22_part75 : Audit := .split 12 (5,true) (byMove [
.last 21 (4,true),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 40 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.last 20 (4,true),
.cycle 12 3 false (0),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 35 true (0),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 20 true (0),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part75_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part75) = true := by rfl

def kid22_part76 : Audit := .cycle 1 11 true (1)
theorem kid22_part76_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part76) = true := by rfl

def kid22_part77 : Audit := .cycle 7 4 true (2)
theorem kid22_part77_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part77) = true := by rfl

def kid22_part78 : Audit := .cycle 9 2 true (2)
theorem kid22_part78_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part78) = true := by rfl

def kid22_part79 : Audit := .cycle 0 12 true (0)
theorem kid22_part79_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part79) = true := by rfl

def kid22_part80 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 16 true (0),
.cycle 0 21 true (0),
.cycle 45 1 false (7),
.last 24 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.cycle 23 1 false (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 2 12 true (1)
])
theorem kid22_part80_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part80) = true := by rfl

def kid22_part81 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 21 (4,true),
.cycle 12 1 true (4),
.last 19 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 19 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 12 1 true (4)
])
theorem kid22_part81_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part81) = true := by rfl

def kid22_part82 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 19 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.cycle 2 13 true (1),
.last 19 (5,true),
.cycle 6 16 true (1),
.cycle 12 2 true (2),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 19 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.cycle 12 9 true (2)
])
theorem kid22_part82_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part82) = true := by rfl

def kid22_part83 : Audit := .split 13 (5,true) (byMove [
.cycle 11 8 true (0),
.cycle 25 17 true (0),
.cycle 20 1 false (-2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 14 4 false (0),
.cycle 6 8 true (1),
.last 15 (4,true),
.last 17 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 5 true (2),
.last 16 (4,true),
.last 15 (4,true),
.last 23 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 14 4 false (0),
.last 20 (4,true),
.last 15 (4,true),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 18 (4,true)
])
theorem kid22_part83_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part83) = true := by rfl

def kid22_part84 : Audit := .cycle 1 13 true (1)
theorem kid22_part84_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part84) = true := by rfl

def kid22_part85 : Audit := .split 15 (4,true) (byMove [
.cycle 27 1 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 19 1 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 42 1 false (4),
.cycle 11 8 true (0),
.cycle 24 1 false (2),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 14 2 true (2),
.cycle 18 1 false (0),
.cycle 28 1 false (4),
.cycle 19 1 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 17 19 true (2),
.last 18 (5,true),
.last 36 (5,true)
])
theorem kid22_part85_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part85) = true := by rfl

def kid22_part86 : Audit := .cycle 16 1 false (-2)
theorem kid22_part86_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part86) = true := by rfl

def kid22_part87 : Audit := .split 12 (5,true) (byMove [
.cycle 12 8 true (-1),
.last 29 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 14 1 false (0),
.cycle 18 1 false (2),
.last 13 (4,true),
.cycle 16 1 false (4),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 5 8 true (0),
.last 13 (4,true),
.cycle 14 3 true (2)
])
theorem kid22_part87_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part87) = true := by rfl

def kid22_part88 : Audit := .cycle 1 11 true (1)
theorem kid22_part88_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part88) = true := by rfl

def kid22_part89 : Audit := .split 14 (5,true) (byMove [
.cycle 13 8 true (1),
.cycle 0 18 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.cycle 24 1 false (-2),
.last 29 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 9 6 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (1),
.last 17 (4,true),
.last 19 (4,true),
.cycle 1 17 true (1),
.last 19 (4,true),
.cycle 24 1 false (-2),
.last 17 (4,true),
.cycle 1 15 true (1),
.cycle 11 4 true (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (1)
])
theorem kid22_part89_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part89) = true := by rfl

def kid22_part90 : Audit := .split 12 (5,true) (byMove [
.cycle 11 8 true (1),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 19 1 false (1),
.cycle 20 1 false (-2),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 13 true (1),
.last 15 (4,true),
.last 17 (4,true),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 20 1 false (-2),
.cycle 16 3 false (0),
.cycle 1 13 true (1),
.cycle 11 4 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 13 true (1)
])
theorem kid22_part90_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part90) = true := by rfl

def kid22_part91 : Audit := .cycle 0 12 true (0)
theorem kid22_part91_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part91) = true := by rfl

def kid22_part92 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.last 20 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 20 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 8 5 true (2),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 16 (5,true),
.cycle 1 13 true (1),
.cycle 20 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 15 (5,true)
])
theorem kid22_part92_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part92) = true := by rfl

def kid22_part93 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 24 true (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 13 (4,true),
.last 21 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 15 (4,true),
.cycle 12 1 true (4)
])
theorem kid22_part93_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part93) = true := by rfl

def kid22_part69 : Audit := .split 10 (5,false) (byMove [(kid22_part70),(kid22_part71),(kid22_part72),(kid22_part73),(kid22_part74),(kid22_part75),(kid22_part76),(kid22_part77),(kid22_part78),(kid22_part79),(kid22_part80),(kid22_part81),(kid22_part82),(kid22_part83),(kid22_part84),(kid22_part85),(kid22_part86),(kid22_part87),(kid22_part88),(kid22_part89),(kid22_part90),(kid22_part91),(kid22_part92),(kid22_part93)])

theorem kid22_part69_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part69) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part70),(kid22_part71),(kid22_part72),(kid22_part73),(kid22_part74),(kid22_part75),(kid22_part76),(kid22_part77),(kid22_part78),(kid22_part79),(kid22_part80),(kid22_part81),(kid22_part82),(kid22_part83),(kid22_part84),(kid22_part85),(kid22_part86),(kid22_part87),(kid22_part88),(kid22_part89),(kid22_part90),(kid22_part91),(kid22_part92),(kid22_part93)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part70_checked

  · exact kid22_part76_checked

  · exact kid22_part82_checked

  · exact kid22_part88_checked

  · exact kid22_part71_checked

  · exact kid22_part77_checked

  · exact kid22_part83_checked

  · exact kid22_part89_checked

  · exact kid22_part72_checked

  · exact kid22_part78_checked

  · exact kid22_part84_checked

  · exact kid22_part90_checked

  · exact kid22_part73_checked

  · exact kid22_part79_checked

  · exact kid22_part85_checked

  · exact kid22_part91_checked

  · exact kid22_part74_checked

  · exact kid22_part80_checked

  · exact kid22_part86_checked

  · exact kid22_part92_checked

  · exact kid22_part75_checked

  · exact kid22_part81_checked

  · exact kid22_part87_checked

  · exact kid22_part93_checked

def kid22_part94 : Audit := .cycle 0 10 true (0)
theorem kid22_part94_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part94) = true := by rfl

def kid22_part95 : Audit := .cycle 1 9 true (1)
theorem kid22_part95_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part95) = true := by rfl

def kid22_part96 : Audit := .cycle 2 8 true (1)
theorem kid22_part96_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part96) = true := by rfl

def kid22_part97 : Audit := .cycle 1 12 true (1)
theorem kid22_part97_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part97) = true := by rfl

def kid22_part98 : Audit := .cycle 8 2 true (3)
theorem kid22_part98_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part98) = true := by rfl

def kid22_part100 : Audit := .cycle 1 11 true (1)
theorem kid22_part100_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part100) = true := by rfl

def kid22_part101 : Audit := .cycle 7 4 true (3)
theorem kid22_part101_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part101) = true := by rfl

def kid22_part102 : Audit := .cycle 9 2 true (3)
theorem kid22_part102_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part102) = true := by rfl

def kid22_part103 : Audit := .cycle 0 12 true (0)
theorem kid22_part103_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part103) = true := by rfl

def kid22_part104 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 20 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.cycle 0 21 true (0),
.cycle 45 1 false (7),
.cycle 30 1 false (2),
.cycle 6 12 true (2),
.cycle 15 2 true (2),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.cycle 23 1 false (1),
.cycle 20 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
])
theorem kid22_part104_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part104) = true := by rfl

def kid22_part105 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 21 (4,true),
.cycle 17 1 false (1),
.cycle 6 12 true (2),
.last 17 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 19 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
])
theorem kid22_part105_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part105) = true := by rfl

def kid22_part106 : Audit := .cycle 0 11 true (0)
theorem kid22_part106_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part106) = true := by rfl

def kid22_part107 : Audit := .cycle 1 10 true (1)
theorem kid22_part107_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part107) = true := by rfl

def kid22_part108 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 9 10 true (3),
.cycle 0 20 true (0),
.cycle 33 1 false (1),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.cycle 2 18 true (1),
.last 29 (5,true),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 33 1 false (1),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 10 9 true (3)
])
theorem kid22_part108_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part108) = true := by rfl

def kid22_part109 : Audit := .cycle 3 8 true (1)
theorem kid22_part109_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part109) = true := by rfl

def kid22_part110 : Audit := .cycle 2 10 true (1)
theorem kid22_part110_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part110) = true := by rfl

def kid22_part111 : Audit := .cycle 10 1 true (4)
theorem kid22_part111_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part111) = true := by rfl

def kid22_part112 : Audit := .cycle 6 5 true (2)
theorem kid22_part112_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part112) = true := by rfl

def kid22_part113 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 9 4 true (3),
.cycle 0 14 true (0),
.cycle 29 1 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 9 6 true (3),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 25 1 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid22_part113_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part113) = true := by rfl

def kid22_part114 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 9 4 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 5 11 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid22_part114_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part114) = true := by rfl

def kid22_part115 : Audit := .cycle 1 12 true (1)
theorem kid22_part115_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part115) = true := by rfl

def kid22_part116 : Audit := .split 11 (4,true) (byMove [
.cycle 13 5 true (3),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 20 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.cycle 60 1 false (10),
.last 12 (5,true),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 23 1 false (1),
.cycle 20 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.last 12 (5,true)
])
theorem kid22_part116_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part116) = true := by rfl

def kid22_part117 : Audit := .split 11 (5,true) (byMove [
.cycle 13 5 true (3),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 24 1 false (6),
.last 14 (4,true),
.last 16 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 19 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 3 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (3)
])
theorem kid22_part117_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part117) = true := by rfl

def kid22_part118 : Audit := .cycle 0 11 true (0)
theorem kid22_part118_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part118) = true := by rfl

def kid22_part119 : Audit := .cycle 1 10 true (1)
theorem kid22_part119_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part119) = true := by rfl

def kid22_part120 : Audit := .cycle 2 9 true (1)
theorem kid22_part120_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part120) = true := by rfl

def kid22_part121 : Audit := .cycle 1 13 true (1)
theorem kid22_part121_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part121) = true := by rfl

def kid22_part122 : Audit := .cycle 8 3 true (3)
theorem kid22_part122_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part122) = true := by rfl

def kid22_part123 : Audit := .cycle 10 1 true (4)
theorem kid22_part123_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part123) = true := by rfl

def kid22_part99 : Audit := .split 10 (5,false) (byMove [(kid22_part100),(kid22_part101),(kid22_part102),(kid22_part103),(kid22_part104),(kid22_part105),(kid22_part106),(kid22_part107),(kid22_part108),(kid22_part109),(kid22_part110),(kid22_part111),(kid22_part112),(kid22_part113),(kid22_part114),(kid22_part115),(kid22_part116),(kid22_part117),(kid22_part118),(kid22_part119),(kid22_part120),(kid22_part121),(kid22_part122),(kid22_part123)])

theorem kid22_part99_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part99) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part100),(kid22_part101),(kid22_part102),(kid22_part103),(kid22_part104),(kid22_part105),(kid22_part106),(kid22_part107),(kid22_part108),(kid22_part109),(kid22_part110),(kid22_part111),(kid22_part112),(kid22_part113),(kid22_part114),(kid22_part115),(kid22_part116),(kid22_part117),(kid22_part118),(kid22_part119),(kid22_part120),(kid22_part121),(kid22_part122),(kid22_part123)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part100_checked

  · exact kid22_part106_checked

  · exact kid22_part112_checked

  · exact kid22_part118_checked

  · exact kid22_part101_checked

  · exact kid22_part107_checked

  · exact kid22_part113_checked

  · exact kid22_part119_checked

  · exact kid22_part102_checked

  · exact kid22_part108_checked

  · exact kid22_part114_checked

  · exact kid22_part120_checked

  · exact kid22_part103_checked

  · exact kid22_part109_checked

  · exact kid22_part115_checked

  · exact kid22_part121_checked

  · exact kid22_part104_checked

  · exact kid22_part110_checked

  · exact kid22_part116_checked

  · exact kid22_part122_checked

  · exact kid22_part105_checked

  · exact kid22_part111_checked

  · exact kid22_part117_checked

  · exact kid22_part123_checked

def kid22_part3 : Audit := .split 9 (2,true) (byMove [(kid22_part4),(kid22_part5),(kid22_part6),(kid22_part7),(kid22_part8),(kid22_part9),(kid22_part34),(kid22_part35),(kid22_part36),(kid22_part37),(kid22_part38),(kid22_part39),(kid22_part64),(kid22_part65),(kid22_part66),(kid22_part67),(kid22_part68),(kid22_part69),(kid22_part94),(kid22_part95),(kid22_part96),(kid22_part97),(kid22_part98),(kid22_part99)])

theorem kid22_part3_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (kid22_part3) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) 9 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid22_part4),(kid22_part5),(kid22_part6),(kid22_part7),(kid22_part8),(kid22_part9),(kid22_part34),(kid22_part35),(kid22_part36),(kid22_part37),(kid22_part38),(kid22_part39),(kid22_part64),(kid22_part65),(kid22_part66),(kid22_part67),(kid22_part68),(kid22_part69),(kid22_part94),(kid22_part95),(kid22_part96),(kid22_part97),(kid22_part98),(kid22_part99)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part4_checked

  · exact kid22_part34_checked

  · exact kid22_part64_checked

  · exact kid22_part94_checked

  · exact kid22_part5_checked

  · exact kid22_part35_checked

  · exact kid22_part65_checked

  · exact kid22_part95_checked

  · exact kid22_part6_checked

  · exact kid22_part36_checked

  · exact kid22_part66_checked

  · exact kid22_part96_checked

  · exact kid22_part7_checked

  · exact kid22_part37_checked

  · exact kid22_part67_checked

  · exact kid22_part97_checked

  · exact kid22_part8_checked

  · exact kid22_part38_checked

  · exact kid22_part68_checked

  · exact kid22_part98_checked

  · exact kid22_part9_checked

  · exact kid22_part39_checked

  · exact kid22_part69_checked

  · exact kid22_part99_checked

def kid22_part124 : Audit := .cycle 0 10 true (0)
theorem kid22_part124_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,3⟩)) (kid22_part124) = true := by rfl

def kid22_part126 : Audit := .cycle 0 10 true (0)
theorem kid22_part126_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part126) = true := by rfl

def kid22_part127 : Audit := .cycle 1 9 true (1)
theorem kid22_part127_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part127) = true := by rfl

def kid22_part128 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 29 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 true (1),
.cycle 17 6 false (3),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (3),
.cycle 33 1 false (5),
.cycle 23 1 false (1),
.cycle 19 1 true (1)
]),
.cycle 0 19 true (0),
.cycle 29 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 20 1 false (4),
.cycle 19 1 true (3),
.cycle 17 6 true (2),
.cycle 18 3 true (2),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 33 1 false (7),
.cycle 23 1 false (3),
.cycle 19 1 true (3)
]),
.cycle 17 5 false (3),
.cycle 16 5 false (3),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.split 19 (5,false) (byMove [
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 18 2 true (1),
.cycle 0 21 true (0),
.cycle 22 1 false (2),
.last 20 (5,true),
.last 24 (5,true),
.last 22 (5,true),
.cycle 33 1 false (5),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.last 44 (5,true),
.cycle 17 5 false (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 17 3 false (3),
.last 20 (5,true)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.split 19 (5,false) (byMove [
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 18 2 true (2),
.cycle 0 21 true (0),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 52 1 false (6),
.cycle 10 10 true (0),
.cycle 28 1 false (4),
.cycle 24 1 false (2),
.cycle 19 1 true (3),
.cycle 25 1 false (3),
.cycle 16 4 true (2),
.last 21 (5,true),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.cycle 17 4 true (2),
.cycle 19 1 true (3)
])
])
theorem kid22_part128_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part128) = true := by rfl

def kid22_part129 : Audit := .cycle 17 1 false (1)
theorem kid22_part129_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part129) = true := by rfl

def kid22_part130 : Audit := .cycle 13 1 false (-1)
theorem kid22_part130_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part130) = true := by rfl

def kid22_part132 : Audit := .cycle 0 11 true (0)
theorem kid22_part132_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part132) = true := by rfl

def kid22_part133 : Audit := .cycle 1 10 true (1)
theorem kid22_part133_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part133) = true := by rfl

def kid22_part134 : Audit := .cycle 21 1 false (1)
theorem kid22_part134_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part134) = true := by rfl

def kid22_part135 : Audit := .cycle 24 1 false (2)
theorem kid22_part135_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part135) = true := by rfl

def kid22_part136 : Audit := .cycle 14 1 false (-2)
theorem kid22_part136_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part136) = true := by rfl

def kid22_part137 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 12 5 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 25 1 false (3),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part137_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part137) = true := by rfl

def kid22_part138 : Audit := .cycle 0 11 true (0)
theorem kid22_part138_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part138) = true := by rfl

def kid22_part139 : Audit := .cycle 1 10 true (1)
theorem kid22_part139_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part139) = true := by rfl

def kid22_part140 : Audit := .split 20 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.last 22 (2,true),
.cycle 19 5 false (3),
.last 22 (2,true),
.cycle 0 30 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.last 22 (2,true),
.cycle 0 26 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 22 (2,true)
])
theorem kid22_part140_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part140) = true := by rfl

def kid22_part141 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 29 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 29 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 20 1 false (4),
.cycle 17 5 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.cycle 28 1 false (4)
])
theorem kid22_part141_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part141) = true := by rfl

def kid22_part142 : Audit := .cycle 16 1 false (0)
theorem kid22_part142_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part142) = true := by rfl

def kid22_part143 : Audit := .cycle 10 1 true (2)
theorem kid22_part143_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part143) = true := by rfl

def kid22_part144 : Audit := .split 15 (5,true) (byMove [
.cycle 0 32 true (0),
.cycle 16 15 false (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 23 1 false (-3),
.cycle 16 6 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 26 1 false (4),
.cycle 29 1 false (1),
.cycle 25 1 false (-1),
.cycle 10 6 true (1),
.cycle 21 5 false (1),
.last 20 (2,true),
.last 16 (2,true),
.cycle 33 1 false (1),
.cycle 23 1 false (-3),
.cycle 14 6 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 16 8 false (2),
.cycle 21 11 false (2)
])
theorem kid22_part144_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part144) = true := by rfl

def kid22_part145 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 16 (5,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.cycle 3 10 true (1),
.last 16 (5,true),
.cycle 10 3 true (1),
.last 20 (5,true),
.last 15 (5,true),
.cycle 16 16 true (-1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 16 (5,true)
])
theorem kid22_part145_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part145) = true := by rfl

def kid22_part146 : Audit := .cycle 0 13 true (0)
theorem kid22_part146_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part146) = true := by rfl

def kid22_part147 : Audit := .cycle 18 1 false (0)
theorem kid22_part147_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part147) = true := by rfl

def kid22_part148 : Audit := .cycle 14 1 false (-2)
theorem kid22_part148_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part148) = true := by rfl

def kid22_part149 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 17 31 false (6),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 25 1 false (3),
.last 13 (2,true),
.cycle 24 1 false (4),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 21 1 false (-1),
.last 14 (2,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 37 true (0),
.cycle 1 15 true (0),
.last 13 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1026, 1290, 1026, 128, 256, 8, 2, 1290, 1, 4096],[2, 1024, 4096, 1, 1418, 512, 2, 1024, 4096, 1, 2, 512, 4096],4096⟩,
.cycle 17 1 false (-1),
.cycle 13 3 true (1)
])
theorem kid22_part149_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part149) = true := by rfl

def kid22_part150 : Audit := .cycle 0 11 true (0)
theorem kid22_part150_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part150) = true := by rfl

def kid22_part151 : Audit := .cycle 1 10 true (1)
theorem kid22_part151_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part151) = true := by rfl

def kid22_part152 : Audit := .cycle 2 9 true (1)
theorem kid22_part152_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part152) = true := by rfl

def kid22_part153 : Audit := .cycle 1 13 true (1)
theorem kid22_part153_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part153) = true := by rfl

def kid22_part154 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (4),
.cycle 24 3 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 0 17 true (0),
.cycle 24 3 false (4),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 17 3 false (2),
.cycle 14 5 false (2),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 3 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 3 false (3),
.cycle 27 3 false (5),
.cycle 17 3 false (1),
.cycle 13 4 true (0)
])
theorem kid22_part154_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part154) = true := by rfl

def kid22_part155 : Audit := .cycle 10 1 true (2)
theorem kid22_part155_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part155) = true := by rfl

def kid22_part131 : Audit := .split 10 (5,false) (byMove [(kid22_part132),(kid22_part133),(kid22_part134),(kid22_part135),(kid22_part136),(kid22_part137),(kid22_part138),(kid22_part139),(kid22_part140),(kid22_part141),(kid22_part142),(kid22_part143),(kid22_part144),(kid22_part145),(kid22_part146),(kid22_part147),(kid22_part148),(kid22_part149),(kid22_part150),(kid22_part151),(kid22_part152),(kid22_part153),(kid22_part154),(kid22_part155)])

theorem kid22_part131_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part131) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part132),(kid22_part133),(kid22_part134),(kid22_part135),(kid22_part136),(kid22_part137),(kid22_part138),(kid22_part139),(kid22_part140),(kid22_part141),(kid22_part142),(kid22_part143),(kid22_part144),(kid22_part145),(kid22_part146),(kid22_part147),(kid22_part148),(kid22_part149),(kid22_part150),(kid22_part151),(kid22_part152),(kid22_part153),(kid22_part154),(kid22_part155)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part132_checked

  · exact kid22_part138_checked

  · exact kid22_part144_checked

  · exact kid22_part150_checked

  · exact kid22_part133_checked

  · exact kid22_part139_checked

  · exact kid22_part145_checked

  · exact kid22_part151_checked

  · exact kid22_part134_checked

  · exact kid22_part140_checked

  · exact kid22_part146_checked

  · exact kid22_part152_checked

  · exact kid22_part135_checked

  · exact kid22_part141_checked

  · exact kid22_part147_checked

  · exact kid22_part153_checked

  · exact kid22_part136_checked

  · exact kid22_part142_checked

  · exact kid22_part148_checked

  · exact kid22_part154_checked

  · exact kid22_part137_checked

  · exact kid22_part143_checked

  · exact kid22_part149_checked

  · exact kid22_part155_checked

def kid22_part156 : Audit := .cycle 0 10 true (0)
theorem kid22_part156_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part156) = true := by rfl

def kid22_part157 : Audit := .cycle 1 9 true (1)
theorem kid22_part157_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part157) = true := by rfl

def kid22_part158 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 30, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 0 24 true (0),
.cycle 22 8 true (2),
.cycle 0 27 true (0),
.cycle 24 1 false (4),
.split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (1),
.last 26 (5,true),
.cycle 24 1 false (4),
.last 22 (5,true),
.cycle 25 8 true (4),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 22 8 true (2),
.cycle 26 1 false (4),
.last 23 (5,true),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.last 26 (5,true),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 25 8 true (4),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 0 26 true (0),
.last 23 (5,true)
]),
.cycle 0 49 true (0),
.cycle 7 14 true (0),
.cycle 10 12 true (0),
.cycle 0 22 true (0),
.cycle 9 12 true (0),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 0 47 true (0),
.cycle 22 8 true (2),
.cycle 30 1 false (6),
.cycle 26 1 false (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.last 49 (5,false),
.cycle 10 12 true (0),
.last 31 (5,false),
.cycle 28 1 false (4),
.last 22 (5,false),
.cycle 25 8 true (4),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 8 true (2),
.cycle 26 1 false (4),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 68 (5,false),
.cycle 50 8 true (8),
.cycle 8 14 true (0),
.last 22 (5,false)
]),
.cycle 22 8 true (4),
.cycle 28 8 true (4),
.cycle 0 55 true (0),
.cycle 21 8 true (2),
.cycle 36 1 false (10),
.split 21 (5,false) (byMove [
.last 25 (5,true),
.cycle 38 1 false (10),
.cycle 25 1 false (1),
.cycle 24 8 true (4),
.cycle 36 1 false (10),
.last 22 (5,true),
.cycle 6 16 true (0),
.cycle 22 8 true (4),
.cycle 20 2 true (3),
.cycle 0 55 true (0),
.cycle 9 16 true (0),
.last 22 (5,true),
.cycle 27 8 true (3),
.cycle 18 4 true (2),
.cycle 34 8 true (2),
.cycle 22 8 true (2),
.cycle 25 1 false (1),
.last 22 (5,true),
.cycle 60 8 true (10),
.cycle 22 8 true (4),
.last 23 (5,true),
.cycle 47 8 true (7),
.cycle 25 8 true (4),
.last 22 (5,true)
]),
.cycle 0 57 true (0),
.cycle 23 8 true (4),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 21 8 true (4),
.split 21 (5,true) (byMove [
.last 76 (5,false),
.last 35 (5,false),
.last 23 (5,false),
.cycle 0 23 true (0),
.last 33 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.last 57 (5,false),
.cycle 22 8 true (4),
.cycle 0 43 true (0),
.last 35 (5,false),
.last 22 (5,false),
.cycle 6 16 true (0),
.cycle 22 8 true (4),
.cycle 20 2 true (4),
.last 53 (5,false),
.last 24 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.cycle 23 8 true (4),
.last 22 (5,false)
])
])
theorem kid22_part158_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part158) = true := by rfl

def kid22_part159 : Audit := .cycle 0 19 true (0)
theorem kid22_part159_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part159) = true := by rfl

def kid22_part160 : Audit := .cycle 15 1 false (1)
theorem kid22_part160_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part160) = true := by rfl

def kid22_part162 : Audit := .cycle 0 11 true (0)
theorem kid22_part162_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part162) = true := by rfl

def kid22_part163 : Audit := .cycle 1 10 true (1)
theorem kid22_part163_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part163) = true := by rfl

def kid22_part164 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.cycle 25 1 false (3),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 22 24 true (2),
.cycle 11 10 true (0),
.cycle 39 1 false (7),
.cycle 27 1 false (3),
.cycle 41 1 false (7),
.cycle 2 24 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 41 (2,true),
.cycle 5 42 true (0),
.cycle 43 1 false (7),
.last 22 (2,true)
])
theorem kid22_part164_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part164) = true := by rfl

def kid22_part165 : Audit := .cycle 32 1 false (6)
theorem kid22_part165_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part165) = true := by rfl

def kid22_part166 : Audit := .cycle 16 1 false (0)
theorem kid22_part166_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part166) = true := by rfl

def kid22_part167 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 24 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 12 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 27 1 false (5),
.cycle 17 1 false (1),
.cycle 13 2 true (0)
])
theorem kid22_part167_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part167) = true := by rfl

def kid22_part168 : Audit := .cycle 0 11 true (0)
theorem kid22_part168_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part168) = true := by rfl

def kid22_part169 : Audit := .cycle 1 10 true (1)
theorem kid22_part169_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part169) = true := by rfl

def kid22_part170 : Audit := .split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 1 58 true (0),
.cycle 41 1 false (9),
.last 27 (2,true),
.cycle 40 1 false (12),
.cycle 0 63 true (0),
.cycle 0 55 true (0),
.cycle 7 56 true (0),
.last 23 (2,true),
.cycle 0 57 true (0),
.cycle 33 1 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 62, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 24 15 true (4),
.last 24 (2,true),
.cycle 0 61 true (0),
.cycle 37 1 false (9),
.last 26 (2,true),
.last 24 (2,true),
.cycle 0 77 true (0),
.cycle 1 35 true (0),
.last 23 (2,true),
.cycle 59 33 true (11),
.cycle 23 26 true (4),
.cycle 24 20 true (6)
])
theorem kid22_part170_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part170) = true := by rfl

def kid22_part171 : Audit := .split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 8 true (2),
.last 25 (2,true),
.cycle 24 1 false (4),
.cycle 22 8 true (2),
.cycle 0 49 true (0),
.cycle 7 14 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 9 12 true (0),
.cycle 10 12 true (0),
.cycle 22 8 true (4),
.last 22 (2,true),
.cycle 0 55 true (0),
.cycle 21 8 true (2),
.cycle 36 1 false (10),
.cycle 0 55 true (0),
.cycle 0 57 true (0),
.cycle 23 8 true (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 21 8 true (4),
.cycle 3 20 true (0)
])
theorem kid22_part171_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part171) = true := by rfl

def kid22_part172 : Audit := .cycle 18 1 false (2)
theorem kid22_part172_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part172) = true := by rfl

def kid22_part173 : Audit := .cycle 10 1 true (4)
theorem kid22_part173_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part173) = true := by rfl

def kid22_part174 : Audit := .cycle 7 5 true (3)
theorem kid22_part174_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part174) = true := by rfl

def kid22_part175 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 28 1 false (2),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 11 true (3),
.cycle 3 10 true (1),
.cycle 8 6 true (3),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.cycle 9 5 true (3),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 9 6 true (3)
])
theorem kid22_part175_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part175) = true := by rfl

def kid22_part176 : Audit := .cycle 0 13 true (0)
theorem kid22_part176_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part176) = true := by rfl

def kid22_part177 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.cycle 32 1 false (6),
.cycle 0 19 true (0),
.cycle 22 20 true (2),
.cycle 11 10 true (0),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 34 1 false (6),
.cycle 4 20 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.cycle 26 1 false (4),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.last 37 (2,true),
.cycle 5 38 true (0),
.cycle 36 1 false (6),
.cycle 43 25 true (7)
])
theorem kid22_part177_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part177) = true := by rfl

def kid22_part178 : Audit := .cycle 16 1 false (0)
theorem kid22_part178_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part178) = true := by rfl

def kid22_part179 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 138 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 19 true (0),
.cycle 7 11 true (0),
.last 15 (2,true),
.cycle 33 1 false (9),
.cycle 19 1 false (5),
.cycle 19 1 false (5),
.cycle 20 11 true (2),
.last 16 (2,true),
.cycle 0 23 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 19 true (0),
.cycle 20 5 true (3),
.last 15 (2,true),
.cycle 0 46 true (0),
.cycle 16 14 true (2),
.cycle 17 3 true (3)
])
theorem kid22_part179_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part179) = true := by rfl

def kid22_part180 : Audit := .cycle 0 11 true (0)
theorem kid22_part180_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part180) = true := by rfl

def kid22_part181 : Audit := .cycle 1 10 true (1)
theorem kid22_part181_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part181) = true := by rfl

def kid22_part182 : Audit := .cycle 2 9 true (1)
theorem kid22_part182_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part182) = true := by rfl

def kid22_part183 : Audit := .cycle 1 13 true (1)
theorem kid22_part183_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part183) = true := by rfl

def kid22_part184 : Audit := .cycle 8 3 true (3)
theorem kid22_part184_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part184) = true := by rfl

def kid22_part185 : Audit := .cycle 10 1 true (4)
theorem kid22_part185_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part185) = true := by rfl

def kid22_part161 : Audit := .split 10 (5,false) (byMove [(kid22_part162),(kid22_part163),(kid22_part164),(kid22_part165),(kid22_part166),(kid22_part167),(kid22_part168),(kid22_part169),(kid22_part170),(kid22_part171),(kid22_part172),(kid22_part173),(kid22_part174),(kid22_part175),(kid22_part176),(kid22_part177),(kid22_part178),(kid22_part179),(kid22_part180),(kid22_part181),(kid22_part182),(kid22_part183),(kid22_part184),(kid22_part185)])

theorem kid22_part161_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part161) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part162),(kid22_part163),(kid22_part164),(kid22_part165),(kid22_part166),(kid22_part167),(kid22_part168),(kid22_part169),(kid22_part170),(kid22_part171),(kid22_part172),(kid22_part173),(kid22_part174),(kid22_part175),(kid22_part176),(kid22_part177),(kid22_part178),(kid22_part179),(kid22_part180),(kid22_part181),(kid22_part182),(kid22_part183),(kid22_part184),(kid22_part185)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part162_checked

  · exact kid22_part168_checked

  · exact kid22_part174_checked

  · exact kid22_part180_checked

  · exact kid22_part163_checked

  · exact kid22_part169_checked

  · exact kid22_part175_checked

  · exact kid22_part181_checked

  · exact kid22_part164_checked

  · exact kid22_part170_checked

  · exact kid22_part176_checked

  · exact kid22_part182_checked

  · exact kid22_part165_checked

  · exact kid22_part171_checked

  · exact kid22_part177_checked

  · exact kid22_part183_checked

  · exact kid22_part166_checked

  · exact kid22_part172_checked

  · exact kid22_part178_checked

  · exact kid22_part184_checked

  · exact kid22_part167_checked

  · exact kid22_part173_checked

  · exact kid22_part179_checked

  · exact kid22_part185_checked

def kid22_part186 : Audit := .cycle 6 8 true (2)
theorem kid22_part186_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part186) = true := by rfl

def kid22_part187 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 19 2 true (0),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 15 2 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 20 2 true (2),
.cycle 18 2 true (2),
.cycle 20 1 false (0),
.last 13 (5,false),
.cycle 16 2 true (1),
.cycle 16 2 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 19 2 true (0),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 18 2 true (4),
.cycle 3 9 true (1),
.cycle 19 2 true (0),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 19 2 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 20 2 true (4),
.cycle 18 2 true (4),
.cycle 23 2 true (0),
.cycle 12 1 true (4),
.cycle 16 2 true (3),
.cycle 10 3 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 19 2 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 12 2 true (2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 15 2 true (0),
.split 12 (5,true) (byMove [
.cycle 10 8 true (1),
.cycle 0 16 true (0),
.cycle 18 2 true (2),
.cycle 19 1 false (1),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 14 (5,false),
.cycle 14 2 true (2),
.cycle 16 2 true (0),
.cycle 1 15 true (1),
.cycle 16 2 true (2),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 15 2 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 13 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 2 true (2),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 15 2 true (2),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 13 2 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 2 true (5),
.cycle 3 10 true (1),
.cycle 15 2 true (2),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 13 2 true (3),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 13 2 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 14 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid22_part187_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part187) = true := by rfl

def kid22_part188 : Audit := .cycle 0 12 true (0)
theorem kid22_part188_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part188) = true := by rfl

def kid22_part189 : Audit := .cycle 27 1 false (5)
theorem kid22_part189_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part189) = true := by rfl

def kid22_part190 : Audit := .cycle 13 1 false (-1)
theorem kid22_part190_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part190) = true := by rfl

def kid22_part192 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 22 (5,true),
.cycle 3 11 true (1),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 6 16 true (1),
.last 16 (5,true),
.last 22 (5,true),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.cycle 1 15 true (1)
])
theorem kid22_part192_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part192) = true := by rfl

def kid22_part193 : Audit := .cycle 0 14 true (0)
theorem kid22_part193_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part193) = true := by rfl

def kid22_part194 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (4),
.cycle 15 8 true (1),
.last 20 (2,true),
.cycle 33 1 false (5),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 44 (2,true),
.cycle 17 4 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 17 2 true (2),
.last 21 (2,true)
])
theorem kid22_part194_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part194) = true := by rfl

def kid22_part195 : Audit := .split 15 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 34 1 false (2),
.last 24 (5,true),
.cycle 24 1 false (2),
.cycle 20 1 false (0),
.cycle 30 1 false (4),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 30 1 false (4),
.cycle 28 1 false (4),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.last 36 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0)
])
theorem kid22_part195_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part195) = true := by rfl

def kid22_part196 : Audit := .cycle 14 1 false (-2)
theorem kid22_part196_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part196) = true := by rfl

def kid22_part197 : Audit := .split 12 (5,true) (byMove [
.last 25 (2,true),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 16 8 true (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 21 (2,true),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part197_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part197) = true := by rfl

def kid22_part198 : Audit := .cycle 1 11 true (1)
theorem kid22_part198_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part198) = true := by rfl

def kid22_part199 : Audit := .cycle 7 4 true (2)
theorem kid22_part199_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part199) = true := by rfl

def kid22_part200 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 22 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 19 1 false (1),
.last 24 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.last 18 (5,true),
.cycle 17 1 false (-1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.last 21 (5,true)
])
theorem kid22_part200_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part200) = true := by rfl

def kid22_part201 : Audit := .cycle 0 12 true (0)
theorem kid22_part201_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part201) = true := by rfl

def kid22_part202 : Audit := .cycle 9 2 true (2)
theorem kid22_part202_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part202) = true := by rfl

def kid22_part203 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 34 1 false (8),
.cycle 19 1 false (1),
.cycle 12 1 true (4),
.cycle 15 8 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 12 1 true (4)
])
theorem kid22_part203_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part203) = true := by rfl

def kid22_part204 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 30 true (-1),
.last 15 (2,true),
.last 25 (2,true),
.cycle 17 1 false (-1),
.cycle 16 6 false (0),
.cycle 1 15 true (1),
.cycle 7 16 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 9 12 true (1),
.cycle 13 7 true (2),
.cycle 11 8 true (1),
.last 22 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 17 1 false (-1),
.cycle 15 6 false (1),
.cycle 1 15 true (1),
.cycle 13 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 2 true (2),
.cycle 12 11 true (2)
])
theorem kid22_part204_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part204) = true := by rfl

def kid22_part205 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 16 (5,true),
.cycle 16 1 false (0),
.last 18 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.last 19 (5,true),
.last 23 (5,true),
.cycle 0 14 true (0),
.last 17 (5,true),
.last 13 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.last 16 (5,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid22_part205_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part205) = true := by rfl

def kid22_part206 : Audit := .cycle 1 13 true (1)
theorem kid22_part206_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part206) = true := by rfl

def kid22_part207 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 28 1 false (4),
.cycle 21 1 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 19 1 false (1),
.cycle 19 1 false (3),
.cycle 13 8 true (1),
.last 18 (2,true),
.cycle 30 1 false (4),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 46 1 false (4),
.cycle 15 4 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 15 2 true (2),
.cycle 16 24 true (2)
])
theorem kid22_part207_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part207) = true := by rfl

def kid22_part208 : Audit := .cycle 14 1 false (-2)
theorem kid22_part208_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part208) = true := by rfl

def kid22_part209 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 34 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 27 1 false (5),
.cycle 22 1 false (2),
.last 13 (2,true),
.cycle 18 1 false (2),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 12 8 true (-1),
.last 14 (2,true),
.cycle 31 1 false (5),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 34 6 true (4),
.cycle 17 4 true (2),
.last 13 (2,true),
.cycle 5 8 true (0),
.cycle 12 2 true (0),
.cycle 14 3 true (2)
])
theorem kid22_part209_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part209) = true := by rfl

def kid22_part210 : Audit := .cycle 1 11 true (1)
theorem kid22_part210_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part210) = true := by rfl

def kid22_part211 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 24 1 false (2),
.last 19 (2,true),
.cycle 22 1 false (-2),
.last 17 (2,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 9 6 true (2),
.cycle 1 16 true (1),
.cycle 13 8 true (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 21 1 false (1),
.cycle 22 1 false (-2),
.cycle 19 5 false (1),
.cycle 1 15 true (1),
.cycle 11 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 2 true (2),
.cycle 1 16 true (1)
])
theorem kid22_part211_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part211) = true := by rfl

def kid22_part212 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.cycle 3 9 true (1),
.last 20 (5,true),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.last 14 (5,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.cycle 2 11 true (1)
])
theorem kid22_part212_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part212) = true := by rfl

def kid22_part213 : Audit := .cycle 0 12 true (0)
theorem kid22_part213_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part213) = true := by rfl

def kid22_part214 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 22 1 false (2),
.last 17 (2,true),
.cycle 18 1 false (-2),
.cycle 15 6 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 8 7 true (2),
.cycle 11 8 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.cycle 18 1 false (-2),
.cycle 16 3 false (0),
.cycle 1 13 true (1),
.cycle 11 4 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 11 5 true (2)
])
theorem kid22_part214_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part214) = true := by rfl

def kid22_part215 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 24 true (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 1 false (-1),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (2,true),
.cycle 3 9 true (1),
.cycle 21 5 false (2),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 17 1 false (-1),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 2 true (2),
.cycle 12 1 true (4)
])
theorem kid22_part215_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part215) = true := by rfl

def kid22_part191 : Audit := .split 10 (5,false) (byMove [(kid22_part192),(kid22_part193),(kid22_part194),(kid22_part195),(kid22_part196),(kid22_part197),(kid22_part198),(kid22_part199),(kid22_part200),(kid22_part201),(kid22_part202),(kid22_part203),(kid22_part204),(kid22_part205),(kid22_part206),(kid22_part207),(kid22_part208),(kid22_part209),(kid22_part210),(kid22_part211),(kid22_part212),(kid22_part213),(kid22_part214),(kid22_part215)])

theorem kid22_part191_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part191) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part192),(kid22_part193),(kid22_part194),(kid22_part195),(kid22_part196),(kid22_part197),(kid22_part198),(kid22_part199),(kid22_part200),(kid22_part201),(kid22_part202),(kid22_part203),(kid22_part204),(kid22_part205),(kid22_part206),(kid22_part207),(kid22_part208),(kid22_part209),(kid22_part210),(kid22_part211),(kid22_part212),(kid22_part213),(kid22_part214),(kid22_part215)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part192_checked

  · exact kid22_part198_checked

  · exact kid22_part204_checked

  · exact kid22_part210_checked

  · exact kid22_part193_checked

  · exact kid22_part199_checked

  · exact kid22_part205_checked

  · exact kid22_part211_checked

  · exact kid22_part194_checked

  · exact kid22_part200_checked

  · exact kid22_part206_checked

  · exact kid22_part212_checked

  · exact kid22_part195_checked

  · exact kid22_part201_checked

  · exact kid22_part207_checked

  · exact kid22_part213_checked

  · exact kid22_part196_checked

  · exact kid22_part202_checked

  · exact kid22_part208_checked

  · exact kid22_part214_checked

  · exact kid22_part197_checked

  · exact kid22_part203_checked

  · exact kid22_part209_checked

  · exact kid22_part215_checked

def kid22_part216 : Audit := .cycle 0 10 true (0)
theorem kid22_part216_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part216) = true := by rfl

def kid22_part217 : Audit := .cycle 1 9 true (1)
theorem kid22_part217_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part217) = true := by rfl

def kid22_part218 : Audit := .cycle 2 8 true (1)
theorem kid22_part218_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part218) = true := by rfl

def kid22_part219 : Audit := .cycle 1 12 true (1)
theorem kid22_part219_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part219) = true := by rfl

def kid22_part220 : Audit := .cycle 8 2 true (3)
theorem kid22_part220_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part220) = true := by rfl

def kid22_part221 : Audit := .split 10 (5,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 19 1 false (1),
.last 22 (5,true),
.cycle 6 12 true (2),
.cycle 13 4 true (2),
.cycle 0 14 true (0),
.cycle 33 1 false (5),
.cycle 17 1 false (-1),
.last 22 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
]),
.cycle 0 12 true (0),
.cycle 9 2 true (3),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 18 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 33 1 false (5),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 9 true (3),
.cycle 3 8 true (1),
.cycle 8 4 true (3),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.cycle 9 3 true (3),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 20 (5,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 21 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 24 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 13 5 true (3),
.last 16 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 17 1 false (-1),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true)
]),
.cycle 1 12 true (1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 11 true (3),
.cycle 3 10 true (1),
.cycle 8 6 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 6 7 true (2),
.cycle 9 5 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
]),
.split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.last 21 (2,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 24 1 false (6),
.cycle 13 5 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 25 22 true (2),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.cycle 10 1 true (4)
])
theorem kid22_part221_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part221) = true := by rfl

def kid22_part125 : Audit := .split 9 (4,true) (byMove [(kid22_part126),(kid22_part127),(kid22_part128),(kid22_part129),(kid22_part130),(kid22_part131),(kid22_part156),(kid22_part157),(kid22_part158),(kid22_part159),(kid22_part160),(kid22_part161),(kid22_part186),(kid22_part187),(kid22_part188),(kid22_part189),(kid22_part190),(kid22_part191),(kid22_part216),(kid22_part217),(kid22_part218),(kid22_part219),(kid22_part220),(kid22_part221)])

theorem kid22_part125_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (kid22_part125) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) 9 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid22_part126),(kid22_part127),(kid22_part128),(kid22_part129),(kid22_part130),(kid22_part131),(kid22_part156),(kid22_part157),(kid22_part158),(kid22_part159),(kid22_part160),(kid22_part161),(kid22_part186),(kid22_part187),(kid22_part188),(kid22_part189),(kid22_part190),(kid22_part191),(kid22_part216),(kid22_part217),(kid22_part218),(kid22_part219),(kid22_part220),(kid22_part221)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part126_checked

  · exact kid22_part156_checked

  · exact kid22_part186_checked

  · exact kid22_part216_checked

  · exact kid22_part127_checked

  · exact kid22_part157_checked

  · exact kid22_part187_checked

  · exact kid22_part217_checked

  · exact kid22_part128_checked

  · exact kid22_part158_checked

  · exact kid22_part188_checked

  · exact kid22_part218_checked

  · exact kid22_part129_checked

  · exact kid22_part159_checked

  · exact kid22_part189_checked

  · exact kid22_part219_checked

  · exact kid22_part130_checked

  · exact kid22_part160_checked

  · exact kid22_part190_checked

  · exact kid22_part220_checked

  · exact kid22_part131_checked

  · exact kid22_part161_checked

  · exact kid22_part191_checked

  · exact kid22_part221_checked

def kid22_part223 : Audit := .cycle 0 10 true (0)
theorem kid22_part223_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part223) = true := by rfl

def kid22_part224 : Audit := .cycle 1 9 true (1)
theorem kid22_part224_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part224) = true := by rfl

def kid22_part226 : Audit := .cycle 29 1 false (5)
theorem kid22_part226_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part226) = true := by rfl

def kid22_part227 : Audit := .cycle 22 1 false (2)
theorem kid22_part227_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part227) = true := by rfl

def kid22_part228 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 29 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 29 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.last 20 (5,false),
.last 19 (5,false),
.cycle 18 5 false (3),
.cycle 16 5 false (3),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.last 19 (5,false)
])
theorem kid22_part228_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part228) = true := by rfl

def kid22_part229 : Audit := .cycle 0 19 true (0)
theorem kid22_part229_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part229) = true := by rfl

def kid22_part230 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 false (4),
.cycle 31 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 21 true (0),
.cycle 31 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 true (0),
.cycle 20 1 true (0),
.last 25 (2,true),
.last 22 (2,true),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (2),
.cycle 34 1 false (4),
.cycle 24 1 false (0),
.cycle 20 1 true (0)
])
theorem kid22_part230_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part230) = true := by rfl

def kid22_part231 : Audit := .cycle 20 1 false (2)
theorem kid22_part231_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part231) = true := by rfl

def kid22_part232 : Audit := .cycle 0 18 true (0)
theorem kid22_part232_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part232) = true := by rfl

def kid22_part233 : Audit := .cycle 48 1 false (6)
theorem kid22_part233_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part233) = true := by rfl

def kid22_part234 : Audit := .cycle 10 8 true (0)
theorem kid22_part234_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part234) = true := by rfl

def kid22_part235 : Audit := .cycle 26 1 false (4)
theorem kid22_part235_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part235) = true := by rfl

def kid22_part236 : Audit := .split 19 (5,false) (byMove [
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 2 false (3),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 1040, 256, 2, 8192, 16384, 8, 2, 256, 2, 8192, 16384, 8, 2, 262144, 2, 262144],[2, 1024, 262144, 1, 16, 1040, 2, 65536, 262144, 1, 16, 262144, 2, 65536, 262144, 1, 16, 262144, 262144],327680⟩,
.cycle 10 10 true (0),
.cycle 28 1 false (4),
.cycle 18 2 true (3),
.cycle 19 1 true (3),
.cycle 25 1 false (3),
.cycle 16 4 true (2),
.last 20 (2,true),
.cycle 32 1 false (6),
.cycle 22 2 false (4),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 1040, 2, 512, 8192, 16384, 8, 2, 2, 32768, 8192, 16384, 8, 2, 262144, 32768, 262144],[2, 1024, 262144, 1, 16, 1040, 2, 65536, 262144, 1, 16, 262144, 2, 65536, 262144, 1, 16, 262144, 262144],327680⟩,
.last 22 (2,true),
.cycle 19 1 true (3)
])
theorem kid22_part236_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part236) = true := by rfl

def kid22_part237 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 12 28 true (0),
.cycle 38 1 false (6),
.cycle 11 8 true (0),
.cycle 18 2 true (4),
.cycle 18 1 true (4),
.last 23 (2,true),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 46 1 false (6),
.cycle 60 1 false (8),
.cycle 30 1 false (4),
.cycle 18 1 true (4)
])
theorem kid22_part237_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part237) = true := by rfl

def kid22_part238 : Audit := .cycle 23 1 false (3)
theorem kid22_part238_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part238) = true := by rfl

def kid22_part239 : Audit := .cycle 16 2 true (2)
theorem kid22_part239_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part239) = true := by rfl

def kid22_part240 : Audit := .split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 32, 64, 64],[9, 5, 1, 9, 4, 4, 64],112⟩,
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.cycle 21 1 false (5),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.cycle 21 1 false (3),
.cycle 15 8 true (1),
.cycle 16 5 false (3),
.cycle 32 1 false (6),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 52 1 false (6),
.cycle 1 22 true (0),
.cycle 2 18 true (0),
.cycle 0 20 true (0),
.cycle 17 2 true (2),
.last 21 (5,false)
])
theorem kid22_part240_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part240) = true := by rfl

def kid22_part241 : Audit := .cycle 30 1 false (6)
theorem kid22_part241_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part241) = true := by rfl

def kid22_part242 : Audit := .split 20 (5,false) (byMove [
.cycle 52 40 true (1),
.cycle 12 11 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 17 7 false (3),
.last 22 (2,true),
.cycle 34 1 false (6),
.cycle 21 1 false (1),
.cycle 19 2 true (0),
.cycle 24 1 false (2),
.last 25 (2,true),
.last 22 (2,true),
.cycle 17 9 false (3),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 17 8 false (3),
.last 22 (2,true),
.cycle 48 18 true (2),
.cycle 13 8 true (0),
.cycle 24 1 false (0),
.last 23 (2,true)
])
theorem kid22_part242_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part242) = true := by rfl

def kid22_part243 : Audit := .cycle 20 1 false (2)
theorem kid22_part243_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part243) = true := by rfl

def kid22_part244 : Audit := .cycle 0 18 true (0)
theorem kid22_part244_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part244) = true := by rfl

def kid22_part245 : Audit := .cycle 1 17 true (0)
theorem kid22_part245_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part245) = true := by rfl

def kid22_part246 : Audit := .cycle 2 16 true (0)
theorem kid22_part246_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part246) = true := by rfl

def kid22_part247 : Audit := .cycle 19 21 true (2)
theorem kid22_part247_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part247) = true := by rfl

def kid22_part248 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 31 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 31 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 22 (5,false),
.last 21 (5,false),
.cycle 18 5 false (4),
.cycle 16 7 false (4),
.cycle 0 23 true (0),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (4),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.last 21 (5,false)
])
theorem kid22_part248_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part248) = true := by rfl

def kid22_part249 : Audit := .split 18 (5,false) (byMove [
.last 39 (2,true),
.last 22 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 17 2 true (3),
.last 20 (2,true),
.cycle 0 19 true (0),
.last 38 (2,true),
.cycle 10 9 true (0),
.cycle 3 16 true (0),
.cycle 18 2 true (4),
.cycle 18 1 true (4),
.cycle 32 1 false (4),
.cycle 16 3 true (2),
.last 19 (2,true),
.last 41 (2,true),
.last 21 (2,true),
.last 20 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.last 42 (2,true),
.last 21 (2,true),
.cycle 18 1 true (4)
])
theorem kid22_part249_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part249) = true := by rfl

def kid22_part225 : Audit := .split 17 (4,true) (byMove [(kid22_part226),(kid22_part227),(kid22_part228),(kid22_part229),(kid22_part230),(kid22_part231),(kid22_part232),(kid22_part233),(kid22_part234),(kid22_part235),(kid22_part236),(kid22_part237),(kid22_part238),(kid22_part239),(kid22_part240),(kid22_part241),(kid22_part242),(kid22_part243),(kid22_part244),(kid22_part245),(kid22_part246),(kid22_part247),(kid22_part248),(kid22_part249)])

theorem kid22_part225_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part225) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some mv)) (byMove [(kid22_part226),(kid22_part227),(kid22_part228),(kid22_part229),(kid22_part230),(kid22_part231),(kid22_part232),(kid22_part233),(kid22_part234),(kid22_part235),(kid22_part236),(kid22_part237),(kid22_part238),(kid22_part239),(kid22_part240),(kid22_part241),(kid22_part242),(kid22_part243),(kid22_part244),(kid22_part245),(kid22_part246),(kid22_part247),(kid22_part248),(kid22_part249)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part226_checked

  · exact kid22_part232_checked

  · exact kid22_part238_checked

  · exact kid22_part244_checked

  · exact kid22_part227_checked

  · exact kid22_part233_checked

  · exact kid22_part239_checked

  · exact kid22_part245_checked

  · exact kid22_part228_checked

  · exact kid22_part234_checked

  · exact kid22_part240_checked

  · exact kid22_part246_checked

  · exact kid22_part229_checked

  · exact kid22_part235_checked

  · exact kid22_part241_checked

  · exact kid22_part247_checked

  · exact kid22_part230_checked

  · exact kid22_part236_checked

  · exact kid22_part242_checked

  · exact kid22_part248_checked

  · exact kid22_part231_checked

  · exact kid22_part237_checked

  · exact kid22_part243_checked

  · exact kid22_part249_checked

def kid22_part250 : Audit := .cycle 17 1 false (1)
theorem kid22_part250_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part250) = true := by rfl

def kid22_part252 : Audit := .cycle 0 24 true (0)
theorem kid22_part252_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part252) = true := by rfl

def kid22_part253 : Audit := .cycle 12 11 false (1)
theorem kid22_part253_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part253) = true := by rfl

def kid22_part254 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 17 (4,true),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 28 1 false (2),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid22_part254_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part254) = true := by rfl

def kid22_part255 : Audit := .cycle 0 13 true (0)
theorem kid22_part255_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part255) = true := by rfl

def kid22_part256 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (4),
.cycle 22 2 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 22 2 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 12 5 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 2 false (1),
.cycle 25 2 false (3),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part256_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part256) = true := by rfl

def kid22_part257 : Audit := .cycle 14 1 false (-2)
theorem kid22_part257_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part257) = true := by rfl

def kid22_part258 : Audit := .cycle 0 12 true (0)
theorem kid22_part258_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part258) = true := by rfl

def kid22_part259 : Audit := .cycle 1 11 true (1)
theorem kid22_part259_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part259) = true := by rfl

def kid22_part260 : Audit := .split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 24 1 false (2),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.cycle 48 1 false (4),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.cycle 10 10 true (0),
.cycle 36 1 false (4),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 34 1 false (6),
.cycle 38 1 false (6),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.cycle 28 1 false (2),
.cycle 11 9 true (0)
])
theorem kid22_part260_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part260) = true := by rfl

def kid22_part261 : Audit := .cycle 21 1 false (1)
theorem kid22_part261_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part261) = true := by rfl

def kid22_part262 : Audit := .cycle 10 2 true (1)
theorem kid22_part262_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part262) = true := by rfl

def kid22_part263 : Audit := .cycle 11 1 true (1)
theorem kid22_part263_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part263) = true := by rfl

def kid22_part264 : Audit := .split 22 (4,true) (byMove [
.cycle 0 23 false (4),
.cycle 12 16 false (2),
.cycle 24 1 false (-2),
.cycle 23 1 false (-3),
.cycle 16 7 false (0),
.cycle 17 6 false (0),
.cycle 0 23 false (4),
.cycle 12 16 true (-2),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 16 7 false (0),
.cycle 17 6 true (-2),
.cycle 18 5 false (0),
.last 24 (2,true),
.cycle 0 25 false (4),
.cycle 23 1 false (-3),
.cycle 16 7 false (0),
.cycle 21 6 false (-1),
.cycle 14 25 false (3),
.cycle 1 22 false (4),
.cycle 12 15 false (2),
.cycle 12 19 true (-2),
.cycle 14 9 false (2),
.cycle 11 12 false (2)
])
theorem kid22_part264_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part264) = true := by rfl

def kid22_part265 : Audit := .split 13 (4,true) (byMove [
.last 27 (2,true),
.last 20 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 18 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.last 26 (2,true),
.cycle 12 8 true (0),
.last 24 (2,true),
.cycle 10 4 true (0),
.last 16 (2,true),
.last 21 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.last 28 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.last 29 (2,true),
.last 22 (2,true),
.cycle 11 3 true (0)
])
theorem kid22_part265_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part265) = true := by rfl

def kid22_part266 : Audit := .split 12 (2,true) (byMove [
.cycle 0 30 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 20 (4,true),
.cycle 0 27 true (0),
.cycle 0 20 true (-2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 18 true (-2),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 29 true (-1),
.cycle 13 1 false (-1),
.last 19 (4,true),
.cycle 0 24 true (-2),
.cycle 0 27 true (0),
.last 16 (4,true),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid22_part266_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part266) = true := by rfl

def kid22_part267 : Audit := .cycle 25 1 false (1)
theorem kid22_part267_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part267) = true := by rfl

def kid22_part268 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 23 2 false (3),
.cycle 16 2 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 2 false (2),
.cycle 14 2 false (0),
.cycle 22 2 false (-2),
.last 14 (2,true),
.cycle 25 2 false (3),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 27 2 false (-1),
.cycle 1 16 true (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 2 false (-1),
.cycle 11 4 true (0)
])
theorem kid22_part268_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part268) = true := by rfl

def kid22_part269 : Audit := .cycle 14 1 false (-2)
theorem kid22_part269_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part269) = true := by rfl

def kid22_part270 : Audit := .cycle 0 12 true (0)
theorem kid22_part270_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part270) = true := by rfl

def kid22_part271 : Audit := .cycle 1 11 true (1)
theorem kid22_part271_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part271) = true := by rfl

def kid22_part272 : Audit := .cycle 2 10 true (1)
theorem kid22_part272_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part272) = true := by rfl

def kid22_part273 : Audit := .cycle 1 14 true (1)
theorem kid22_part273_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part273) = true := by rfl

def kid22_part274 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 22 4 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 15 4 false (0),
.cycle 0 15 true (0),
.cycle 22 4 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 4 false (1),
.cycle 15 4 false (2),
.cycle 12 5 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 17 4 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 4 false (3),
.cycle 25 4 false (5),
.cycle 15 4 false (1),
.cycle 11 4 true (0)
])
theorem kid22_part274_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part274) = true := by rfl

def kid22_part275 : Audit := .cycle 11 1 true (1)
theorem kid22_part275_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part275) = true := by rfl

def kid22_part251 : Audit := .split 11 (5,false) (byMove [(kid22_part252),(kid22_part253),(kid22_part254),(kid22_part255),(kid22_part256),(kid22_part257),(kid22_part258),(kid22_part259),(kid22_part260),(kid22_part261),(kid22_part262),(kid22_part263),(kid22_part264),(kid22_part265),(kid22_part266),(kid22_part267),(kid22_part268),(kid22_part269),(kid22_part270),(kid22_part271),(kid22_part272),(kid22_part273),(kid22_part274),(kid22_part275)])

theorem kid22_part251_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part251) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some mv)) (byMove [(kid22_part252),(kid22_part253),(kid22_part254),(kid22_part255),(kid22_part256),(kid22_part257),(kid22_part258),(kid22_part259),(kid22_part260),(kid22_part261),(kid22_part262),(kid22_part263),(kid22_part264),(kid22_part265),(kid22_part266),(kid22_part267),(kid22_part268),(kid22_part269),(kid22_part270),(kid22_part271),(kid22_part272),(kid22_part273),(kid22_part274),(kid22_part275)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part252_checked

  · exact kid22_part258_checked

  · exact kid22_part264_checked

  · exact kid22_part270_checked

  · exact kid22_part253_checked

  · exact kid22_part259_checked

  · exact kid22_part265_checked

  · exact kid22_part271_checked

  · exact kid22_part254_checked

  · exact kid22_part260_checked

  · exact kid22_part266_checked

  · exact kid22_part272_checked

  · exact kid22_part255_checked

  · exact kid22_part261_checked

  · exact kid22_part267_checked

  · exact kid22_part273_checked

  · exact kid22_part256_checked

  · exact kid22_part262_checked

  · exact kid22_part268_checked

  · exact kid22_part274_checked

  · exact kid22_part257_checked

  · exact kid22_part263_checked

  · exact kid22_part269_checked

  · exact kid22_part275_checked

def kid22_part276 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 13 2 false (-1),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 25 1 false (3),
.last 20 (2,true),
.cycle 28 1 false (4),
.cycle 24 1 false (2),
.cycle 23 1 false (3),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 12 true (0),
.cycle 10 20 true (0),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 27 1 false (5),
.cycle 31 1 false (5),
.cycle 36 1 false (8),
.cycle 0 54 true (0),
.cycle 27 1 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 27 1 false (3),
.cycle 25 1 false (3)
]),
.split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 11 8 true (0),
.cycle 26 1 false (4),
.cycle 28 1 false (4),
.cycle 10 8 true (0),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 30 1 false (6),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 22 1 false (2),
.cycle 3 16 true (0)
]),
.cycle 10 2 true (2),
.cycle 10 1 true (2),
.cycle 15 6 false (1),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 16 6 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.last 16 (4,true),
.cycle 10 3 true (1),
.last 19 (4,true),
.last 14 (4,true),
.cycle 16 16 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 14 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 6 false (1),
.last 15 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 2 false (-1),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.cycle 10 1 true (2)
])
theorem kid22_part276_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part276) = true := by rfl

def kid22_part277 : Audit := .cycle 0 10 true (0)
theorem kid22_part277_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part277) = true := by rfl

def kid22_part278 : Audit := .cycle 1 9 true (1)
theorem kid22_part278_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part278) = true := by rfl

def kid22_part280 : Audit := .split 22 (2,true) (byMove [
.cycle 37 1 false (9),
.cycle 0 28 true (0),
.cycle 25 1 false (3),
.cycle 47 1 false (11),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 0 83 true (0),
.cycle 33 55 true (5),
.cycle 55 1 false (13),
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.last 36 (5,false),
.cycle 37 1 false (9),
.cycle 41 1 false (9),
.cycle 31 1 false (7),
.cycle 29 1 false (7),
.cycle 19 8 true (2),
.last 25 (5,false),
.cycle 0 63 true (0),
.cycle 18 42 true (2),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.cycle 19 74 true (2),
.last 62 (5,false)
])
theorem kid22_part280_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part280) = true := by rfl

def kid22_part281 : Audit := .cycle 36 1 false (10)
theorem kid22_part281_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part281) = true := by rfl

def kid22_part282 : Audit := .split 20 (2,true) (byMove [
.cycle 0 61 true (0),
.cycle 49 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 33 55 true (5),
.cycle 34 1 false (10),
.cycle 21 1 false (3),
.last 22 (5,false),
.last 21 (5,false),
.cycle 16 41 true (0),
.cycle 18 5 false (3),
.cycle 41 1 false (9),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 1 34 true (0),
.cycle 0 55 true (0),
.cycle 40 1 false (10),
.cycle 36 1 false (10),
.last 21 (5,false)
])
theorem kid22_part282_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part282) = true := by rfl

def kid22_part283 : Audit := .cycle 0 25 true (0)
theorem kid22_part283_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part283) = true := by rfl

def kid22_part284 : Audit := .split 22 (5,false) (byMove [
.cycle 0 100 true (-2),
.cycle 33 1 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 0 67 true (0),
.cycle 55 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 21 2 true (0),
.last 27 (2,true),
.cycle 13 15 false (3),
.last 24 (2,true),
.last 55 (2,true),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 0 67 true (0),
.cycle 1 44 true (0),
.cycle 44 1 false (10),
.cycle 0 73 true (0),
.cycle 26 1 false (2),
.last 27 (2,true)
])
theorem kid22_part284_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part284) = true := by rfl

def kid22_part285 : Audit := .cycle 34 1 false (10)
theorem kid22_part285_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part285) = true := by rfl

def kid22_part286 : Audit := .cycle 6 14 true (0)
theorem kid22_part286_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part286) = true := by rfl

def kid22_part287 : Audit := .cycle 42 12 true (8)
theorem kid22_part287_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part287) = true := by rfl

def kid22_part288 : Audit := .split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 8, 1, 8, 8, 8, 64],112⟩,
.cycle 0 24 true (0),
.cycle 22 8 true (2),
.cycle 0 27 true (0),
.cycle 24 1 false (4),
.last 21 (5,false),
.cycle 0 49 true (0),
.cycle 7 14 true (0),
.cycle 10 12 true (0),
.cycle 0 22 true (0),
.cycle 10 12 true (0),
.cycle 9 12 true (0),
.cycle 22 8 true (4),
.cycle 28 8 true (4),
.cycle 0 55 true (0),
.cycle 21 8 true (2),
.cycle 36 1 false (10),
.last 21 (5,false),
.cycle 0 57 true (0),
.cycle 24 8 true (4),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 21 8 true (4),
.cycle 22 8 true (4)
])
theorem kid22_part288_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part288) = true := by rfl

def kid22_part289 : Audit := .cycle 0 49 true (0)
theorem kid22_part289_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part289) = true := by rfl

def kid22_part290 : Audit := .split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 30, 30, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.last 34 (2,true),
.cycle 32 1 false (6),
.cycle 27 2 false (3),
.cycle 28 1 false (4),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 12, 2, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.cycle 10 14 true (0),
.cycle 52 1 false (10),
.cycle 22 2 true (5),
.cycle 23 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 16, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 44 1 false (10),
.cycle 28 2 false (4),
.last 27 (2,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 4, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 26, 8, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.cycle 8 16 true (0),
.cycle 23 1 true (5)
])
theorem kid22_part290_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part290) = true := by rfl

def kid22_part291 : Audit := .split 21 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 0 47 true (0),
.last 30 (5,false),
.cycle 30 1 false (6),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 46 10 true (8),
.cycle 10 12 true (0),
.cycle 22 10 true (2),
.last 23 (5,false),
.last 22 (5,false),
.last 34 (5,false),
.last 26 (5,false),
.cycle 0 24 true (0),
.last 28 (5,false),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 44 true (0),
.last 54 (5,false),
.cycle 8 14 true (0),
.last 22 (5,false)
])
theorem kid22_part291_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part291) = true := by rfl

def kid22_part292 : Audit := .cycle 31 1 false (7)
theorem kid22_part292_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part292) = true := by rfl

def kid22_part293 : Audit := .cycle 18 2 true (2)
theorem kid22_part293_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part293) = true := by rfl

def kid22_part294 : Audit := .split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 9, 1, 8, 4, 8, 64],112⟩,
.cycle 0 50 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 36 1 false (10),
.cycle 31 1 false (7),
.cycle 25 1 false (7),
.cycle 27 1 false (7),
.cycle 29 1 false (7),
.cycle 25 1 false (7),
.cycle 17 8 true (1),
.cycle 18 5 false (3),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 47 14 true (7),
.cycle 24 12 true (4),
.cycle 2 22 true (0),
.cycle 5 16 true (0),
.cycle 19 2 true (2),
.cycle 22 10 true (4)
])
theorem kid22_part294_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part294) = true := by rfl

def kid22_part295 : Audit := .cycle 36 1 false (10)
theorem kid22_part295_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part295) = true := by rfl

def kid22_part296 : Audit := .split 22 (5,false) (byMove [
.cycle 74 32 true (4),
.cycle 14 11 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 19 7 false (3),
.last 24 (2,true),
.cycle 44 1 false (10),
.cycle 23 1 false (1),
.cycle 21 2 true (0),
.last 25 (2,true),
.cycle 16 69 true (-1),
.last 24 (2,true),
.cycle 19 9 false (3),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 19 8 false (3),
.last 24 (2,true),
.cycle 60 28 true (4),
.cycle 15 8 true (0),
.cycle 48 1 false (10),
.last 25 (2,true)
])
theorem kid22_part296_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part296) = true := by rfl

def kid22_part297 : Audit := .split 21 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 8, 1, 8, 32, 8, 64],112⟩,
.cycle 0 61 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 27 1 false (7),
.cycle 36 1 false (10),
.cycle 25 1 false (7),
.cycle 34 1 false (10),
.last 23 (5,false),
.last 24 (5,false),
.cycle 28 14 true (4),
.cycle 18 6 true (2),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 65 true (0),
.cycle 1 25 true (0),
.cycle 2 22 true (0),
.cycle 5 83 true (0),
.cycle 31 1 false (7),
.last 24 (5,false)
])
theorem kid22_part297_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part297) = true := by rfl

def kid22_part298 : Audit := .cycle 0 57 true (0)
theorem kid22_part298_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part298) = true := by rfl

def kid22_part299 : Audit := .cycle 1 21 true (0)
theorem kid22_part299_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part299) = true := by rfl

def kid22_part300 : Audit := .split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 8, 1, 8, 8, 8, 64],112⟩,
.cycle 0 26 true (0),
.cycle 24 1 false (2),
.cycle 2 32 true (0),
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.cycle 2 45 true (0),
.cycle 2 55 true (0),
.cycle 2 38 true (0),
.cycle 0 22 true (0),
.last 45 (5,false),
.last 32 (5,false),
.cycle 2 22 true (0),
.cycle 2 24 true (0),
.cycle 2 26 true (0),
.cycle 5 16 true (0),
.cycle 19 2 true (3),
.last 23 (5,false),
.cycle 0 57 true (0),
.cycle 2 30 true (0),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 2 20 true (0),
.cycle 2 28 true (0)
])
theorem kid22_part300_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part300) = true := by rfl

def kid22_part301 : Audit := .cycle 20 28 true (3)
theorem kid22_part301_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part301) = true := by rfl

def kid22_part302 : Audit := .cycle 21 10 true (4)
theorem kid22_part302_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part302) = true := by rfl

def kid22_part303 : Audit := .split 21 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.last 66 (5,false),
.last 32 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.last 47 (5,false),
.last 40 (5,false),
.last 29 (5,false),
.last 23 (5,false),
.last 22 (5,false),
.last 34 (5,false),
.last 26 (5,false),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 0 26 true (0),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 42 true (0),
.cycle 5 44 true (0),
.last 42 (5,false),
.last 22 (5,false)
])
theorem kid22_part303_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part303) = true := by rfl

def kid22_part279 : Audit := .split 19 (4,true) (byMove [(kid22_part280),(kid22_part281),(kid22_part282),(kid22_part283),(kid22_part284),(kid22_part285),(kid22_part286),(kid22_part287),(kid22_part288),(kid22_part289),(kid22_part290),(kid22_part291),(kid22_part292),(kid22_part293),(kid22_part294),(kid22_part295),(kid22_part296),(kid22_part297),(kid22_part298),(kid22_part299),(kid22_part300),(kid22_part301),(kid22_part302),(kid22_part303)])

theorem kid22_part279_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part279) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid22_part280),(kid22_part281),(kid22_part282),(kid22_part283),(kid22_part284),(kid22_part285),(kid22_part286),(kid22_part287),(kid22_part288),(kid22_part289),(kid22_part290),(kid22_part291),(kid22_part292),(kid22_part293),(kid22_part294),(kid22_part295),(kid22_part296),(kid22_part297),(kid22_part298),(kid22_part299),(kid22_part300),(kid22_part301),(kid22_part302),(kid22_part303)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part280_checked

  · exact kid22_part286_checked

  · exact kid22_part292_checked

  · exact kid22_part298_checked

  · exact kid22_part281_checked

  · exact kid22_part287_checked

  · exact kid22_part293_checked

  · exact kid22_part299_checked

  · exact kid22_part282_checked

  · exact kid22_part288_checked

  · exact kid22_part294_checked

  · exact kid22_part300_checked

  · exact kid22_part283_checked

  · exact kid22_part289_checked

  · exact kid22_part295_checked

  · exact kid22_part301_checked

  · exact kid22_part284_checked

  · exact kid22_part290_checked

  · exact kid22_part296_checked

  · exact kid22_part302_checked

  · exact kid22_part285_checked

  · exact kid22_part291_checked

  · exact kid22_part297_checked

  · exact kid22_part303_checked

def kid22_part305 : Audit := .split 20 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.cycle 22 1 false (4),
.cycle 0 21 true (0),
.cycle 62 1 false (12),
.cycle 39 1 false (9),
.cycle 28 1 false (6),
.last 22 (5,false),
.last 21 (5,false),
.cycle 25 1 false (5),
.cycle 33 1 false (7),
.cycle 34 1 false (8),
.cycle 32 1 false (8),
.cycle 17 8 true (2),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 30 1 false (6),
.last 21 (5,false)
])
theorem kid22_part305_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part305) = true := by rfl

def kid22_part306 : Audit := .cycle 21 1 false (3)
theorem kid22_part306_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part306) = true := by rfl

def kid22_part307 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 30 1 false (6),
.cycle 62 1 false (12),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.last 20 (5,false),
.last 19 (5,false),
.cycle 41 1 false (5),
.cycle 16 5 false (3),
.cycle 32 1 false (6),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 3 20 true (0),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.last 19 (5,false)
])
theorem kid22_part307_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part307) = true := by rfl

def kid22_part308 : Audit := .cycle 30 1 false (6)
theorem kid22_part308_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part308) = true := by rfl

def kid22_part309 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 false (4),
.cycle 30 1 false (2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 true (0),
.cycle 25 1 false (5),
.cycle 32 1 false (2),
.last 22 (2,true),
.cycle 0 27 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 25 true (0),
.cycle 1 31 true (0),
.cycle 29 1 false (3),
.cycle 0 27 true (0),
.cycle 23 1 false (1),
.cycle 3 22 true (0)
])
theorem kid22_part309_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part309) = true := by rfl

def kid22_part310 : Audit := .cycle 19 1 false (3)
theorem kid22_part310_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part310) = true := by rfl

def kid22_part311 : Audit := .cycle 0 41 true (0)
theorem kid22_part311_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part311) = true := by rfl

def kid22_part312 : Audit := .cycle 26 20 true (4)
theorem kid22_part312_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part312) = true := by rfl

def kid22_part313 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.cycle 21 1 false (3),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 39 8 true (7),
.cycle 10 10 true (0),
.cycle 19 8 true (2),
.last 20 (5,false),
.last 19 (5,false),
.cycle 3 20 true (0),
.cycle 21 8 true (3),
.cycle 0 21 true (0),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 36 true (0),
.cycle 5 38 true (0),
.cycle 21 8 true (2),
.last 19 (5,false)
])
theorem kid22_part313_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part313) = true := by rfl

def kid22_part314 : Audit := .cycle 0 19 true (0)
theorem kid22_part314_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part314) = true := by rfl

def kid22_part315 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 29 1 false (5),
.cycle 33 1 false (7),
.cycle 23 1 false (3),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 22, 2, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 10 12 true (0),
.cycle 37 1 false (7),
.cycle 19 2 true (4),
.cycle 20 1 true (4),
.cycle 3 22 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 27 1 false (5),
.cycle 23 1 false (3),
.cycle 34 1 false (8),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 26, 4, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 8, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 41 1 false (7),
.cycle 20 1 true (4)
])
theorem kid22_part315_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part315) = true := by rfl

def kid22_part316 : Audit := .split 26 (5,false) (byMove [
.cycle 0 27 true (0),
.cycle 1 26 true (0),
.cycle 35 1 false (7),
.cycle 39 1 false (9),
.cycle 29 1 false (5),
.cycle 29 1 false (5),
.cycle 0 27 true (0),
.cycle 22 49 true (2),
.cycle 10 18 true (0),
.cycle 19 8 true (2),
.cycle 26 2 true (6),
.cycle 26 1 true (6),
.cycle 3 28 true (0),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 40 1 false (10),
.cycle 0 27 true (0),
.cycle 1 26 true (0),
.cycle 0 46 true (0),
.cycle 22 69 true (2),
.cycle 18 10 true (2),
.cycle 26 1 true (6)
])
theorem kid22_part316_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part316) = true := by rfl

def kid22_part317 : Audit := .cycle 25 1 false (5)
theorem kid22_part317_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part317) = true := by rfl

def kid22_part318 : Audit := .cycle 16 2 true (2)
theorem kid22_part318_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part318) = true := by rfl

def kid22_part319 : Audit := .split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 9, 1, 8, 4, 8, 64],112⟩,
.cycle 14 32 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 23 1 false (5),
.cycle 25 1 false (5),
.cycle 22 1 false (6),
.cycle 30 1 false (8),
.cycle 32 1 false (8),
.cycle 0 21 true (0),
.cycle 15 8 true (1),
.cycle 16 5 false (3),
.cycle 25 1 false (5),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 27 24 true (3),
.cycle 3 22 true (0),
.cycle 2 19 true (0),
.cycle 0 47 true (0),
.cycle 17 2 true (2),
.cycle 0 21 true (0)
])
theorem kid22_part319_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part319) = true := by rfl

def kid22_part320 : Audit := .cycle 23 1 false (5)
theorem kid22_part320_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part320) = true := by rfl

def kid22_part321 : Audit := .split 20 (5,false) (byMove [
.cycle 42 48 true (0),
.cycle 12 11 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 17 7 false (3),
.last 22 (2,true),
.cycle 27 1 false (5),
.cycle 21 1 false (1),
.cycle 19 2 true (0),
.cycle 34 1 false (8),
.cycle 12 13 false (3),
.last 22 (2,true),
.cycle 17 9 false (3),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 17 8 false (3),
.last 22 (2,true),
.cycle 32 42 true (0),
.cycle 13 8 true (0),
.cycle 23 1 false (1),
.cycle 14 36 true (0)
])
theorem kid22_part321_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part321) = true := by rfl

def kid22_part322 : Audit := .cycle 30 1 false (8)
theorem kid22_part322_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part322) = true := by rfl

def kid22_part323 : Audit := .cycle 0 48 true (0)
theorem kid22_part323_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part323) = true := by rfl

def kid22_part324 : Audit := .cycle 3 18 true (0)
theorem kid22_part324_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part324) = true := by rfl

def kid22_part325 : Audit := .split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 8, 1, 8, 8, 8, 64],112⟩,
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 2 18 true (0),
.cycle 27 1 false (5),
.cycle 0 19 true (0),
.cycle 2 46 true (0),
.cycle 2 25 true (0),
.cycle 3 16 true (0),
.last 20 (5,false),
.last 19 (5,false),
.cycle 2 28 true (0),
.cycle 2 19 true (0),
.cycle 27 1 false (5),
.cycle 2 43 true (0),
.cycle 17 2 true (3),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 3 18 true (0),
.last 19 (5,false)
])
theorem kid22_part325_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part325) = true := by rfl

def kid22_part326 : Audit := .cycle 0 19 true (0)
theorem kid22_part326_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part326) = true := by rfl

def kid22_part327 : Audit := .cycle 3 18 true (0)
theorem kid22_part327_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part327) = true := by rfl

def kid22_part328 : Audit := .cycle 3 16 true (0)
theorem kid22_part328_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part328) = true := by rfl

def kid22_part304 : Audit := .split 17 (4,true) (byMove [(kid22_part305),(kid22_part306),(kid22_part307),(kid22_part308),(kid22_part309),(kid22_part310),(kid22_part311),(kid22_part312),(kid22_part313),(kid22_part314),(kid22_part315),(kid22_part316),(kid22_part317),(kid22_part318),(kid22_part319),(kid22_part320),(kid22_part321),(kid22_part322),(kid22_part323),(kid22_part324),(kid22_part325),(kid22_part326),(kid22_part327),(kid22_part328)])

theorem kid22_part304_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part304) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (4,true) (some mv)) (byMove [(kid22_part305),(kid22_part306),(kid22_part307),(kid22_part308),(kid22_part309),(kid22_part310),(kid22_part311),(kid22_part312),(kid22_part313),(kid22_part314),(kid22_part315),(kid22_part316),(kid22_part317),(kid22_part318),(kid22_part319),(kid22_part320),(kid22_part321),(kid22_part322),(kid22_part323),(kid22_part324),(kid22_part325),(kid22_part326),(kid22_part327),(kid22_part328)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part305_checked

  · exact kid22_part311_checked

  · exact kid22_part317_checked

  · exact kid22_part323_checked

  · exact kid22_part306_checked

  · exact kid22_part312_checked

  · exact kid22_part318_checked

  · exact kid22_part324_checked

  · exact kid22_part307_checked

  · exact kid22_part313_checked

  · exact kid22_part319_checked

  · exact kid22_part325_checked

  · exact kid22_part308_checked

  · exact kid22_part314_checked

  · exact kid22_part320_checked

  · exact kid22_part326_checked

  · exact kid22_part309_checked

  · exact kid22_part315_checked

  · exact kid22_part321_checked

  · exact kid22_part327_checked

  · exact kid22_part310_checked

  · exact kid22_part316_checked

  · exact kid22_part322_checked

  · exact kid22_part328_checked

def kid22_part330 : Audit := .cycle 0 12 true (0)
theorem kid22_part330_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part330) = true := by rfl

def kid22_part331 : Audit := .cycle 1 11 true (1)
theorem kid22_part331_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part331) = true := by rfl

def kid22_part332 : Audit := .split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 24 1 false (0),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.cycle 56 1 false (6),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.last 22 (2,true),
.cycle 32 1 false (4),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 34 1 false (6),
.cycle 24 1 false (0),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.last 24 (2,true),
.last 21 (2,true)
])
theorem kid22_part332_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part332) = true := by rfl

def kid22_part333 : Audit := .cycle 21 1 false (1)
theorem kid22_part333_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part333) = true := by rfl

def kid22_part334 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 2 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 24 2 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 2 false (1),
.cycle 15 2 false (1),
.cycle 12 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 2 false (3),
.cycle 27 2 false (5),
.cycle 17 2 false (1),
.cycle 13 2 true (0)
])
theorem kid22_part334_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part334) = true := by rfl

def kid22_part335 : Audit := .cycle 16 1 false (0)
theorem kid22_part335_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part335) = true := by rfl

def kid22_part336 : Audit := .cycle 0 12 true (0)
theorem kid22_part336_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part336) = true := by rfl

def kid22_part337 : Audit := .cycle 1 11 true (1)
theorem kid22_part337_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part337) = true := by rfl

def kid22_part338 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 42 1 false (10),
.last 22 (2,true),
.cycle 0 27 true (0),
.cycle 26 1 false (2),
.cycle 40 1 false (10),
.cycle 6 16 true (0),
.cycle 46 14 true (8),
.last 22 (2,true),
.cycle 0 53 true (0),
.cycle 10 14 true (0),
.cycle 24 16 true (2),
.cycle 35 1 false (7),
.cycle 20 2 true (2),
.last 22 (2,true),
.cycle 40 1 false (10),
.cycle 48 1 false (10),
.last 25 (2,true),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 22 (2,true),
.cycle 22 30 true (3),
.cycle 23 12 true (4),
.cycle 23 9 true (5)
])
theorem kid22_part338_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part338) = true := by rfl

def kid22_part339 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 25 1 false (3),
.last 20 (2,true),
.cycle 36 1 false (6),
.cycle 23 1 false (1),
.cycle 23 1 false (3),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 41 1 false (7),
.cycle 22 8 true (2),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 27 1 false (5),
.cycle 23 1 false (1),
.cycle 36 1 false (8),
.cycle 0 54 true (0),
.cycle 3 22 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 3 22 true (0),
.cycle 3 20 true (0)
])
theorem kid22_part339_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part339) = true := by rfl

def kid22_part340 : Audit := .cycle 10 2 true (3)
theorem kid22_part340_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part340) = true := by rfl

def kid22_part341 : Audit := .cycle 11 1 true (3)
theorem kid22_part341_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part341) = true := by rfl

def kid22_part342 : Audit := .cycle 6 12 true (2)
theorem kid22_part342_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part342) = true := by rfl

def kid22_part343 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 27 (4,true),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 23 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.last 17 (4,true),
.cycle 11 3 true (2),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 19 (4,true),
.last 16 (4,true)
])
theorem kid22_part343_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part343) = true := by rfl

def kid22_part344 : Audit := .cycle 0 14 true (0)
theorem kid22_part344_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part344) = true := by rfl

def kid22_part345 : Audit := .split 17 (4,true) (byMove [
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 21 1 false (-1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 49 1 false (5),
.cycle 12 8 true (0),
.cycle 27 1 false (3),
.cycle 33 1 false (5),
.cycle 27 1 false (3),
.cycle 24 1 false (2),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 31 1 false (5),
.cycle 21 1 false (-1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 35 1 false (5),
.cycle 42 27 true (5)
])
theorem kid22_part345_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part345) = true := by rfl

def kid22_part346 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 28 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 17 (2,true),
.cycle 18 2 false (2),
.last 15 (2,true),
.cycle 0 24 true (0),
.cycle 16 2 false (2),
.cycle 16 2 false (2),
.cycle 26 2 false (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 17 (2,true),
.cycle 12 6 true (0),
.last 15 (2,true),
.cycle 0 24 true (0),
.cycle 12 6 true (0),
.cycle 12 4 true (0)
])
theorem kid22_part346_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part346) = true := by rfl

def kid22_part347 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 44 14 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 21 1 false (3),
.cycle 48 1 false (6),
.last 16 (2,true),
.cycle 28 1 false (6),
.cycle 19 1 false (3),
.cycle 18 1 false (4),
.cycle 6 16 true (0),
.last 17 (2,true),
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 45 true (0),
.cycle 1 17 true (0),
.last 16 (2,true),
.cycle 16 24 true (1),
.cycle 41 1 false (3),
.cycle 16 3 true (2)
])
theorem kid22_part347_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part347) = true := by rfl

def kid22_part348 : Audit := .cycle 0 12 true (0)
theorem kid22_part348_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part348) = true := by rfl

def kid22_part349 : Audit := .cycle 1 11 true (1)
theorem kid22_part349_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part349) = true := by rfl

def kid22_part350 : Audit := .cycle 2 10 true (1)
theorem kid22_part350_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part350) = true := by rfl

def kid22_part351 : Audit := .cycle 1 14 true (1)
theorem kid22_part351_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part351) = true := by rfl

def kid22_part352 : Audit := .cycle 8 4 true (3)
theorem kid22_part352_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part352) = true := by rfl

def kid22_part353 : Audit := .cycle 11 1 true (3)
theorem kid22_part353_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part353) = true := by rfl

def kid22_part329 : Audit := .split 11 (5,false) (byMove [(kid22_part330),(kid22_part331),(kid22_part332),(kid22_part333),(kid22_part334),(kid22_part335),(kid22_part336),(kid22_part337),(kid22_part338),(kid22_part339),(kid22_part340),(kid22_part341),(kid22_part342),(kid22_part343),(kid22_part344),(kid22_part345),(kid22_part346),(kid22_part347),(kid22_part348),(kid22_part349),(kid22_part350),(kid22_part351),(kid22_part352),(kid22_part353)])

theorem kid22_part329_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part329) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some mv)) (byMove [(kid22_part330),(kid22_part331),(kid22_part332),(kid22_part333),(kid22_part334),(kid22_part335),(kid22_part336),(kid22_part337),(kid22_part338),(kid22_part339),(kid22_part340),(kid22_part341),(kid22_part342),(kid22_part343),(kid22_part344),(kid22_part345),(kid22_part346),(kid22_part347),(kid22_part348),(kid22_part349),(kid22_part350),(kid22_part351),(kid22_part352),(kid22_part353)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part330_checked

  · exact kid22_part336_checked

  · exact kid22_part342_checked

  · exact kid22_part348_checked

  · exact kid22_part331_checked

  · exact kid22_part337_checked

  · exact kid22_part343_checked

  · exact kid22_part349_checked

  · exact kid22_part332_checked

  · exact kid22_part338_checked

  · exact kid22_part344_checked

  · exact kid22_part350_checked

  · exact kid22_part333_checked

  · exact kid22_part339_checked

  · exact kid22_part345_checked

  · exact kid22_part351_checked

  · exact kid22_part334_checked

  · exact kid22_part340_checked

  · exact kid22_part346_checked

  · exact kid22_part352_checked

  · exact kid22_part335_checked

  · exact kid22_part341_checked

  · exact kid22_part347_checked

  · exact kid22_part353_checked

def kid22_part354 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 25 1 false (3),
.last 20 (2,true),
.cycle 36 1 false (6),
.cycle 24 1 false (0),
.cycle 23 1 false (3),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 33 1 false (5),
.cycle 41 1 false (7),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 27 1 false (5),
.cycle 24 1 false (0),
.cycle 25 1 false (5),
.cycle 0 54 true (0),
.cycle 2 22 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 2 22 true (0),
.cycle 2 20 true (0)
]),
.split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 11 8 true (0),
.cycle 26 1 false (4),
.cycle 0 21 true (0),
.cycle 32 1 false (6),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 30 1 false (6),
.cycle 21 1 false (-1),
.cycle 21 1 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 34 1 false (6),
.cycle 0 20 true (0)
]),
.cycle 15 2 false (1),
.cycle 15 1 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 21 (4,true) (byMove [
.last 24 (2,true),
.last 26 (2,true),
.last 22 (2,true),
.cycle 24 15 true (4),
.cycle 26 1 false (2),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 36 26 true (6),
.last 22 (2,true),
.cycle 44 30 true (4),
.cycle 10 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 12, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 37 1 false (9),
.cycle 20 2 true (2),
.last 22 (2,true),
.cycle 33 1 false (9),
.cycle 41 1 false (9),
.cycle 29 1 false (9),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 23 13 true (5),
.cycle 9 15 true (0)
]),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 36 1 false (10),
.last 20 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.cycle 34 1 false (10),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.last 20 (2,true),
.cycle 0 49 true (0),
.cycle 52 1 false (10),
.cycle 9 12 true (0),
.cycle 31 1 false (7),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 36 1 false (10),
.cycle 23 1 false (1),
.cycle 25 1 false (7),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 20 28 true (3),
.cycle 21 10 true (4),
.cycle 3 38 true (0)
]),
.cycle 10 2 true (4),
.cycle 10 1 true (4),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 21 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.last 16 (4,true),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 9 5 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 15 (4,true)
]),
.cycle 0 13 true (0),
.split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 22 1 false (2),
.last 18 (2,true),
.cycle 31 1 false (5),
.cycle 21 1 false (-1),
.cycle 20 1 false (2),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 28 1 false (4),
.cycle 34 1 false (6),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 24 1 false (4),
.cycle 21 1 false (-1),
.cycle 22 1 false (4),
.cycle 0 48 true (0),
.cycle 4 18 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 4 18 true (0),
.cycle 4 16 true (0)
]),
.cycle 15 2 false (1),
.cycle 19 1 false (5),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.cycle 10 1 true (4)
])
theorem kid22_part354_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part354) = true := by rfl

def kid22_part355 : Audit := .cycle 6 8 true (2)
theorem kid22_part355_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part355) = true := by rfl

def kid22_part357 : Audit := .cycle 1 12 true (1)
theorem kid22_part357_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part357) = true := by rfl

def kid22_part358 : Audit := .split 21 (4,true) (byMove [
.cycle 29 5 false (4),
.cycle 22 5 false (1),
.cycle 29 5 false (2),
.cycle 0 23 true (0),
.last 24 (5,false),
.cycle 22 5 false (0),
.cycle 0 22 true (0),
.cycle 7 26 true (0),
.cycle 20 8 true (0),
.cycle 26 5 false (3),
.last 23 (5,false),
.last 22 (5,false),
.cycle 23 5 false (2),
.cycle 20 2 true (0),
.cycle 0 26 true (-1),
.cycle 30 5 false (5),
.last 24 (5,false),
.cycle 22 5 false (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 7 34 true (0),
.cycle 18 4 true (0),
.last 22 (5,false)
])
theorem kid22_part358_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part358) = true := by rfl

def kid22_part359 : Audit := .cycle 25 1 false (1)
theorem kid22_part359_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part359) = true := by rfl

def kid22_part360 : Audit := .cycle 0 13 true (0)
theorem kid22_part360_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part360) = true := by rfl

def kid22_part361 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 19 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (3),
.cycle 30 1 false (4),
.last 14 (5,false),
.last 13 (5,false),
.cycle 25 13 false (2),
.cycle 15 2 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 19 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 17 4 true (0),
.last 13 (5,false)
])
theorem kid22_part361_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part361) = true := by rfl

def kid22_part362 : Audit := .split 17 (4,true) (byMove [
.cycle 27 3 false (3),
.cycle 20 3 false (0),
.last 19 (5,false),
.cycle 0 19 true (0),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 18 true (0),
.cycle 9 20 true (0),
.cycle 16 8 true (0),
.cycle 24 3 false (2),
.last 19 (5,false),
.last 18 (5,false),
.cycle 21 3 false (1),
.cycle 16 2 true (0),
.last 19 (5,false),
.cycle 28 3 false (4),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 9 26 true (0),
.cycle 15 4 true (0),
.last 18 (5,false)
])
theorem kid22_part362_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part362) = true := by rfl

def kid22_part363 : Audit := .cycle 0 12 true (0)
theorem kid22_part363_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part363) = true := by rfl

def kid22_part364 : Audit := .cycle 1 11 true (1)
theorem kid22_part364_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part364) = true := by rfl

def kid22_part365 : Audit := .split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 51 1 false (9),
.cycle 0 21 true (0),
.last 22 (5,false),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (2),
.cycle 3 17 true (1),
.last 21 (5,false),
.last 20 (5,false),
.cycle 6 14 true (2),
.cycle 18 2 true (4),
.cycle 41 1 false (9),
.cycle 1 21 true (1),
.last 22 (5,false),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 32, 64, 64],[0, 2, 8, 0, 32, 2, 64],112⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 4 true (4),
.last 20 (5,false)
])
theorem kid22_part365_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part365) = true := by rfl

def kid22_part366 : Audit := .cycle 3 9 true (1)
theorem kid22_part366_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part366) = true := by rfl

def kid22_part367 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.last 25 (4,true),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 21 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 12 2 true (3),
.cycle 13 1 true (3),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 17 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 17 (4,true),
.cycle 13 1 true (3)
])
theorem kid22_part367_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part367) = true := by rfl

def kid22_part368 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 21 (4,true),
.last 21 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.last 18 (4,true),
.cycle 10 3 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 21 (4,true),
.last 27 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid22_part368_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part368) = true := by rfl

def kid22_part369 : Audit := .cycle 6 6 true (2)
theorem kid22_part369_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part369) = true := by rfl

def kid22_part370 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 24 7 false (1),
.cycle 19 5 false (1),
.cycle 0 15 true (0),
.last 23 (5,false),
.cycle 20 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 12 2 true (2),
.cycle 19 5 false (1),
.cycle 1 15 true (1),
.last 23 (5,false),
.cycle 20 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 4 true (2),
.last 14 (5,false)
])
theorem kid22_part370_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part370) = true := by rfl

def kid22_part371 : Audit := .cycle 1 15 true (1)
theorem kid22_part371_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part371) = true := by rfl

def kid22_part372 : Audit := .cycle 1 13 true (1)
theorem kid22_part372_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part372) = true := by rfl

def kid22_part373 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (1),
.cycle 0 16 true (0),
.last 22 (5,false),
.cycle 19 1 false (1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 9 4 true (2),
.cycle 6 20 true (1),
.cycle 15 2 true (0),
.cycle 1 15 true (1),
.cycle 32 1 false (4),
.last 19 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.last 16 (5,false)
])
theorem kid22_part373_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part373) = true := by rfl

def kid22_part374 : Audit := .split 17 (4,true) (byMove [
.cycle 19 3 false (2),
.cycle 20 3 false (0),
.last 19 (5,false),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 6 12 true (0),
.cycle 40 8 true (4),
.last 19 (5,false),
.cycle 0 51 true (0),
.last 21 (5,false),
.cycle 12 6 true (0),
.cycle 27 3 false (3),
.cycle 16 2 true (0),
.last 19 (5,false),
.cycle 32 3 false (6),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.cycle 14 4 true (0),
.cycle 18 30 true (1),
.cycle 19 4 true (2),
.last 24 (5,false)
])
theorem kid22_part374_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part374) = true := by rfl

def kid22_part375 : Audit := .cycle 0 12 true (0)
theorem kid22_part375_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part375) = true := by rfl

def kid22_part376 : Audit := .cycle 1 11 true (1)
theorem kid22_part376_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part376) = true := by rfl

def kid22_part377 : Audit := .cycle 2 10 true (1)
theorem kid22_part377_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part377) = true := by rfl

def kid22_part378 : Audit := .cycle 1 14 true (1)
theorem kid22_part378_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part378) = true := by rfl

def kid22_part379 : Audit := .split 15 (4,true) (byMove [
.cycle 1 16 true (1),
.cycle 26 9 false (2),
.cycle 25 9 false (2),
.cycle 0 17 true (0),
.last 27 (5,false),
.cycle 23 7 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 14 8 true (2),
.cycle 3 13 true (1),
.last 17 (5,false),
.last 16 (5,false),
.cycle 6 10 true (2),
.cycle 14 2 true (2),
.cycle 15 2 true (2),
.cycle 1 17 true (1),
.last 27 (5,false),
.cycle 22 7 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 12 4 true (2),
.last 16 (5,false)
])
theorem kid22_part379_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part379) = true := by rfl

def kid22_part380 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.last 17 (4,true),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 16 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.cycle 12 1 true (4)
])
theorem kid22_part380_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part380) = true := by rfl

def kid22_part356 : Audit := .split 11 (2,true) (byMove [(kid22_part357),(kid22_part358),(kid22_part359),(kid22_part360),(kid22_part361),(kid22_part362),(kid22_part363),(kid22_part364),(kid22_part365),(kid22_part366),(kid22_part367),(kid22_part368),(kid22_part369),(kid22_part370),(kid22_part371),(kid22_part372),(kid22_part373),(kid22_part374),(kid22_part375),(kid22_part376),(kid22_part377),(kid22_part378),(kid22_part379),(kid22_part380)])

theorem kid22_part356_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part356) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid22_part357),(kid22_part358),(kid22_part359),(kid22_part360),(kid22_part361),(kid22_part362),(kid22_part363),(kid22_part364),(kid22_part365),(kid22_part366),(kid22_part367),(kid22_part368),(kid22_part369),(kid22_part370),(kid22_part371),(kid22_part372),(kid22_part373),(kid22_part374),(kid22_part375),(kid22_part376),(kid22_part377),(kid22_part378),(kid22_part379),(kid22_part380)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part357_checked

  · exact kid22_part363_checked

  · exact kid22_part369_checked

  · exact kid22_part375_checked

  · exact kid22_part358_checked

  · exact kid22_part364_checked

  · exact kid22_part370_checked

  · exact kid22_part376_checked

  · exact kid22_part359_checked

  · exact kid22_part365_checked

  · exact kid22_part371_checked

  · exact kid22_part377_checked

  · exact kid22_part360_checked

  · exact kid22_part366_checked

  · exact kid22_part372_checked

  · exact kid22_part378_checked

  · exact kid22_part361_checked

  · exact kid22_part367_checked

  · exact kid22_part373_checked

  · exact kid22_part379_checked

  · exact kid22_part362_checked

  · exact kid22_part368_checked

  · exact kid22_part374_checked

  · exact kid22_part380_checked

def kid22_part381 : Audit := .cycle 0 12 true (0)
theorem kid22_part381_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part381) = true := by rfl

def kid22_part383 : Audit := .cycle 26 1 false (4)
theorem kid22_part383_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part383) = true := by rfl

def kid22_part384 : Audit := .cycle 19 1 false (1)
theorem kid22_part384_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part384) = true := by rfl

def kid22_part385 : Audit := .split 16 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 26 1 false (2),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 26 1 false (4),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.last 18 (5,false),
.last 17 (5,false),
.cycle 32 1 false (4),
.cycle 14 5 false (3),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.last 17 (5,false)
])
theorem kid22_part385_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part385) = true := by rfl

def kid22_part386 : Audit := .cycle 0 17 true (0)
theorem kid22_part386_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part386) = true := by rfl

def kid22_part387 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 false (4),
.cycle 28 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 0 19 true (0),
.cycle 28 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 17 2 true (0),
.cycle 18 1 true (0),
.cycle 34 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (1),
.cycle 31 1 false (3),
.cycle 21 1 false (-1),
.cycle 18 1 true (0)
])
theorem kid22_part387_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part387) = true := by rfl

def kid22_part388 : Audit := .cycle 17 1 false (1)
theorem kid22_part388_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part388) = true := by rfl

def kid22_part389 : Audit := .cycle 0 16 true (0)
theorem kid22_part389_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part389) = true := by rfl

def kid22_part390 : Audit := .cycle 41 1 false (5)
theorem kid22_part390_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part390) = true := by rfl

def kid22_part391 : Audit := .cycle 10 8 true (0)
theorem kid22_part391_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part391) = true := by rfl

def kid22_part392 : Audit := .cycle 23 1 false (3)
theorem kid22_part392_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part392) = true := by rfl

def kid22_part393 : Audit := .split 17 (5,false) (byMove [
.cycle 28 1 false (4),
.cycle 21 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 2 false (3),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 2, 64],[2, 16, 64, 1, 16, 18, 64],64⟩,
.cycle 10 10 true (0),
.cycle 25 1 false (3),
.cycle 16 2 true (3),
.cycle 17 1 true (3),
.cycle 22 1 false (2),
.cycle 14 4 true (2),
.last 18 (2,true),
.cycle 29 1 false (5),
.cycle 20 2 false (4),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 22, 8, 64],[2, 16, 64, 1, 16, 18, 64],64⟩,
.cycle 31 1 false (5),
.cycle 17 1 true (3)
])
theorem kid22_part393_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part393) = true := by rfl

def kid22_part394 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 11 24 true (0),
.cycle 33 1 false (5),
.cycle 10 8 true (0),
.cycle 16 2 true (4),
.cycle 16 1 true (4),
.cycle 11 30 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 39 1 false (5),
.cycle 51 1 false (7),
.cycle 25 1 false (3),
.cycle 16 1 true (4)
])
theorem kid22_part394_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part394) = true := by rfl

def kid22_part395 : Audit := .cycle 20 1 false (2)
theorem kid22_part395_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part395) = true := by rfl

def kid22_part396 : Audit := .cycle 14 2 true (2)
theorem kid22_part396_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part396) = true := by rfl

def kid22_part397 : Audit := .split 16 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 9, 1, 8, 4, 8, 64],112⟩,
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.cycle 19 1 false (5),
.cycle 0 18 true (0),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 13 8 true (1),
.cycle 14 5 false (3),
.cycle 29 1 false (5),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 45 1 false (5),
.cycle 31 1 false (5),
.cycle 2 16 true (0),
.cycle 0 18 true (0),
.cycle 15 2 true (2),
.cycle 29 1 false (5)
])
theorem kid22_part397_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part397) = true := by rfl

def kid22_part398 : Audit := .cycle 27 1 false (5)
theorem kid22_part398_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part398) = true := by rfl

def kid22_part399 : Audit := .split 18 (5,false) (byMove [
.cycle 48 36 true (1),
.cycle 10 11 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 15 7 false (3),
.last 20 (2,true),
.cycle 31 1 false (5),
.cycle 19 1 false (1),
.cycle 17 2 true (0),
.cycle 21 1 false (1),
.last 26 (2,true),
.last 20 (2,true),
.cycle 15 9 false (3),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 15 8 false (3),
.last 20 (2,true),
.cycle 44 16 true (2),
.cycle 11 8 true (0),
.cycle 21 1 false (-1),
.cycle 5 16 true (0)
])
theorem kid22_part399_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part399) = true := by rfl

def kid22_part400 : Audit := .cycle 17 1 false (1)
theorem kid22_part400_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part400) = true := by rfl

def kid22_part401 : Audit := .cycle 0 16 true (0)
theorem kid22_part401_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part401) = true := by rfl

def kid22_part402 : Audit := .cycle 1 15 true (0)
theorem kid22_part402_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part402) = true := by rfl

def kid22_part403 : Audit := .cycle 2 14 true (0)
theorem kid22_part403_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part403) = true := by rfl

def kid22_part404 : Audit := .cycle 17 19 true (2)
theorem kid22_part404_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part404) = true := by rfl

def kid22_part405 : Audit := .cycle 29 1 false (5)
theorem kid22_part405_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part405) = true := by rfl

def kid22_part406 : Audit := .split 16 (5,false) (byMove [
.cycle 5 50 true (0),
.cycle 31 1 false (5),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 15 2 true (3),
.cycle 29 1 false (5),
.cycle 0 17 true (0),
.cycle 5 49 true (0),
.cycle 10 9 true (0),
.cycle 3 14 true (0),
.cycle 16 2 true (4),
.cycle 16 1 true (4),
.cycle 27 1 false (3),
.cycle 14 3 true (2),
.last 17 (2,true),
.cycle 5 32 true (0),
.cycle 5 34 true (0),
.cycle 23 1 false (3),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 5 33 true (0),
.cycle 5 34 true (0),
.cycle 16 1 true (4)
])
theorem kid22_part406_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part406) = true := by rfl

def kid22_part382 : Audit := .split 15 (4,true) (byMove [(kid22_part383),(kid22_part384),(kid22_part385),(kid22_part386),(kid22_part387),(kid22_part388),(kid22_part389),(kid22_part390),(kid22_part391),(kid22_part392),(kid22_part393),(kid22_part394),(kid22_part395),(kid22_part396),(kid22_part397),(kid22_part398),(kid22_part399),(kid22_part400),(kid22_part401),(kid22_part402),(kid22_part403),(kid22_part404),(kid22_part405),(kid22_part406)])

theorem kid22_part382_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part382) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) 15 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some mv)) (byMove [(kid22_part383),(kid22_part384),(kid22_part385),(kid22_part386),(kid22_part387),(kid22_part388),(kid22_part389),(kid22_part390),(kid22_part391),(kid22_part392),(kid22_part393),(kid22_part394),(kid22_part395),(kid22_part396),(kid22_part397),(kid22_part398),(kid22_part399),(kid22_part400),(kid22_part401),(kid22_part402),(kid22_part403),(kid22_part404),(kid22_part405),(kid22_part406)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part383_checked

  · exact kid22_part389_checked

  · exact kid22_part395_checked

  · exact kid22_part401_checked

  · exact kid22_part384_checked

  · exact kid22_part390_checked

  · exact kid22_part396_checked

  · exact kid22_part402_checked

  · exact kid22_part385_checked

  · exact kid22_part391_checked

  · exact kid22_part397_checked

  · exact kid22_part403_checked

  · exact kid22_part386_checked

  · exact kid22_part392_checked

  · exact kid22_part398_checked

  · exact kid22_part404_checked

  · exact kid22_part387_checked

  · exact kid22_part393_checked

  · exact kid22_part399_checked

  · exact kid22_part405_checked

  · exact kid22_part388_checked

  · exact kid22_part394_checked

  · exact kid22_part400_checked

  · exact kid22_part406_checked

def kid22_part408 : Audit := .cycle 0 16 true (0)
theorem kid22_part408_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part408) = true := by rfl

def kid22_part409 : Audit := .split 24 (4,true) (byMove [
.cycle 26 20 true (0),
.cycle 12 13 false (1),
.last 25 (2,true),
.cycle 51 1 false (-1),
.cycle 12 22 false (1),
.cycle 14 11 false (0),
.last 27 (2,true),
.last 61 (2,true),
.last 33 (2,true),
.cycle 42 17 true (0),
.cycle 10 15 false (2),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 1024, 32768, 524288, 1048576, 32768, 33554434, 8589934592, 8589934592, 524288, 1048576, 134217728, 1024, 1024, 8589934592, 137438953472, 274877906944, 8589934592, 33554432, 146028888064, 146028888064, 128, 256, 134217728, 432176789323776, 1024, 8589967360, 137438953472, 274877906944, 549755813888, 1024, 274877907968, 35184372088832, 137438953472, 274877906944, 35184372088832, 432314228277248, 467782068076544, 467782068076544, 137438953472, 274877906944, 549755813888, 432176789192704, 467782068077568, 35184372088832, 281474976710656],[2, 1024, 281474976710656, 1, 32, 131072, 8192, 4194304, 281474976710656, 4096, 131072, 131072, 33554432, 4194304, 281474976710656, 16777216, 536870912, 68719476736, 2147483648, 1099511627776, 281474976710656, 1073741824, 34359738368, 68719607808, 33554432, 1024, 281474976710656, 16777216, 536870912, 131072, 137438953472, 1099511627776, 281474976710656, 68719476736, 2199023255552, 1168231104512, 8796093022208, 1099511627776, 281474976710656, 4398046511104, 140737488355328, 432176789323776, 137438953472, 1099511627776, 281474976710656, 68719476736, 2199023255552, 432176789192704, 281474976710656],562940504461376⟩,
.cycle 12 14 true (-3),
.cycle 23 2 true (-1),
.last 25 (2,true),
.last 67 (2,true),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.last 27 (2,true),
.cycle 45 4 true (0),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 1024, 32768, 524288, 1048576, 32768, 33554434, 8589934592, 8589934592, 524288, 1048576, 134217728, 1024, 1024, 8589934592, 137438953472, 274877906944, 8589934592, 33554432, 281612415664128, 281612415664128, 128, 256, 134217728, 281474977759232, 1024, 8589967360, 137438953472, 274877906944, 549755813888, 1024, 281749854617600, 35184372088832, 137438953472, 274877906944, 35184372088832, 290683387641856, 317896299380736, 317896299380736, 137438953472, 274877906944, 549755813888, 282574488338432, 318171177287680, 35184372088832, 281474976710656],[2, 1024, 281474976710656, 1, 256, 1048576, 8192, 4194304, 281474976710656, 4096, 1048576, 281474976710656, 33554432, 4194304, 281474976710656, 16777216, 1048576, 68719476736, 2147483648, 1099511627776, 281474976710656, 1073741824, 274877906944, 281474976710656, 33554432, 1024, 281474976710656, 16777216, 256, 1048576, 137438953472, 1099511627776, 281474976710656, 68719476736, 274877906944, 282574488338432, 8796093022208, 1099511627776, 281474976710656, 4398046511104, 274877906944, 282918085722112, 137438953472, 1099511627776, 281474976710656, 68719476736, 274877906944, 282918085722112, 281474976710656],562940504461376⟩,
.last 29 (2,true),
.cycle 24 4 true (-1),
.cycle 28 2 true (-1)
])
theorem kid22_part409_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part409) = true := by rfl

def kid22_part410 : Audit := .split 12 (2,true) (byMove [
.last 21 (4,true),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 17 (4,true),
.last 16 (4,true),
.cycle 29 1 false (1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 19 (4,true),
.last 39 (4,true),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid22_part410_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part410) = true := by rfl

def kid22_part411 : Audit := .split 15 (2,true) (byMove [
.cycle 0 34 true (0),
.last 19 (4,true),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 0 33 true (0),
.last 23 (4,true),
.cycle 3 13 true (0),
.cycle 0 19 true (0),
.cycle 40 1 false (0),
.cycle 24 1 false (-2),
.last 17 (4,true),
.cycle 26 1 false (0),
.cycle 38 1 false (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.proven (BB6.Agent11Raw39B0RBPumps.M1905.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M1905.never m hm),
.last 18 (4,true),
.cycle 0 18 true (0)
])
theorem kid22_part411_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part411) = true := by rfl

def kid22_part412 : Audit := .split 12 (4,true) (byMove [
.cycle 38 2 false (-2),
.cycle 22 2 false (0),
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
.cycle 27 2 false (-3),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 2 18 true (0),
.last 17 (2,true),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part412_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part412) = true := by rfl

def kid22_part413 : Audit := .cycle 14 1 false (-2)
theorem kid22_part413_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part413) = true := by rfl

def kid22_part414 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (0),
.last 24 (2,true),
.last 21 (2,true),
.last 30 (2,true),
.cycle 11 6 true (1),
.cycle 1 17 true (1),
.cycle 7 10 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 0 20 true (0),
.cycle 9 8 true (1),
.cycle 24 16 false (2),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 40 1 false (4),
.cycle 25 7 false (0),
.cycle 6 12 true (1),
.cycle 1 17 true (1),
.cycle 13 4 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 15 2 true (2)
])
theorem kid22_part414_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part414) = true := by rfl

def kid22_part415 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 17 7 false (1),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 16 5 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 1 15 true (1),
.cycle 1 14 true (1),
.cycle 6 8 true (1),
.last 15 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 16 5 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 1 14 true (1)
])
theorem kid22_part415_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part415) = true := by rfl

def kid22_part416 : Audit := .cycle 0 14 true (0)
theorem kid22_part416_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part416) = true := by rfl

def kid22_part417 : Audit := .split 17 (4,true) (byMove [
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 43 1 false (3),
.cycle 12 8 true (0),
.cycle 27 1 false (3),
.cycle 29 1 false (3),
.cycle 12 8 true (0),
.cycle 24 1 false (2),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 17 4 true (2),
.cycle 3 16 true (0)
])
theorem kid22_part417_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part417) = true := by rfl

def kid22_part418 : Audit := .cycle 10 2 true (1)
theorem kid22_part418_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part418) = true := by rfl

def kid22_part419 : Audit := .cycle 9 4 true (1)
theorem kid22_part419_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part419) = true := by rfl

def kid22_part420 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 27, 2, 16, 64],[2, 16, 64, 1, 10, 17, 64],64⟩,
.cycle 24 1 false (-2),
.cycle 23 1 false (-3),
.cycle 16 7 false (0),
.cycle 17 6 false (0),
.last 25 (2,true),
.cycle 13 10 false (2),
.last 23 (2,true),
.cycle 0 36 true (-2),
.cycle 16 8 true (-2),
.cycle 15 8 false (1),
.cycle 14 16 false (2),
.last 24 (2,true),
.last 27 (2,true),
.cycle 23 1 false (-3),
.cycle 16 7 false (0),
.cycle 21 6 false (-1),
.last 25 (2,true),
.cycle 19 4 true (-2),
.last 23 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 27, 2, 16, 64],[2, 16, 64, 1, 8, 17, 64],64⟩,
.cycle 20 4 true (-2),
.cycle 21 2 true (-2)
])
theorem kid22_part420_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part420) = true := by rfl

def kid22_part421 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.last 20 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 32 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 30 (2,true),
.cycle 10 4 true (0),
.last 16 (2,true),
.last 21 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.last 17 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 32 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 13 4 true (0),
.cycle 16 2 true (2)
])
theorem kid22_part421_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part421) = true := by rfl

def kid22_part422 : Audit := .split 12 (2,true) (byMove [
.cycle 0 20 true (-1),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 20 (4,true),
.cycle 0 16 true (0),
.last 24 (4,true),
.cycle 0 16 true (0),
.last 18 (4,true),
.last 13 (4,true),
.last 22 (4,true),
.last 15 (4,true),
.last 16 (4,true),
.last 39 (4,true),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 28 (4,true),
.cycle 0 16 true (0),
.last 16 (4,true),
.cycle 0 16 true (0),
.last 18 (4,true),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid22_part422_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part422) = true := by rfl

def kid22_part423 : Audit := .split 15 (2,true) (byMove [
.cycle 28 1 false (2),
.cycle 21 1 false (-1),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 35 1 false (1),
.last 23 (4,true),
.cycle 25 1 false (1),
.cycle 31 1 false (3),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.last 17 (4,true),
.cycle 31 1 false (3),
.cycle 29 1 false (3),
.last 16 (4,true),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.last 35 (4,true),
.last 18 (4,true),
.last 35 (4,true)
])
theorem kid22_part423_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part423) = true := by rfl

def kid22_part424 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 16 2 false (0),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 14 2 false (2),
.cycle 14 2 false (0),
.cycle 22 2 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 12 4 true (0),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 12 4 true (0),
.cycle 12 2 true (0)
])
theorem kid22_part424_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part424) = true := by rfl

def kid22_part425 : Audit := .cycle 14 1 false (-2)
theorem kid22_part425_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part425) = true := by rfl

def kid22_part426 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 0 32 true (-1),
.last 17 (2,true),
.last 27 (2,true),
.cycle 51 22 false (1),
.cycle 19 8 false (2),
.cycle 1 17 true (1),
.cycle 24 12 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 0 20 true (0),
.cycle 21 10 false (2),
.cycle 6 14 true (1),
.cycle 16 2 true (1),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 16 8 false (2),
.cycle 31 8 false (-1),
.cycle 1 17 true (1),
.cycle 13 4 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 15 2 true (2)
])
theorem kid22_part426_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part426) = true := by rfl

def kid22_part427 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 17 (4,true),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 1 15 true (1),
.cycle 1 14 true (1),
.last 20 (4,true),
.last 15 (4,true),
.last 21 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 1 14 true (1)
])
theorem kid22_part427_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part427) = true := by rfl

def kid22_part428 : Audit := .cycle 0 14 true (0)
theorem kid22_part428_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part428) = true := by rfl

def kid22_part429 : Audit := .cycle 4 8 true (1)
theorem kid22_part429_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part429) = true := by rfl

def kid22_part430 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 26 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 15 4 false (0),
.last 17 (2,true),
.cycle 16 4 false (2),
.last 15 (2,true),
.cycle 0 22 true (0),
.cycle 16 4 false (2),
.cycle 15 4 false (1),
.cycle 22 4 false (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 17 4 false (-1),
.last 17 (2,true),
.cycle 12 4 true (0),
.last 15 (2,true),
.cycle 0 22 true (0),
.cycle 12 4 true (0),
.cycle 13 2 true (0)
])
theorem kid22_part430_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part430) = true := by rfl

def kid22_part431 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 30 true (-1),
.last 15 (2,true),
.last 25 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 0, 64],64⟩,
.cycle 17 6 false (1),
.cycle 1 15 true (1),
.cycle 22 10 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 17 1 true (3),
.cycle 19 8 false (1),
.cycle 6 12 true (1),
.cycle 14 2 true (1),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 15 6 false (1),
.cycle 15 3 false (1),
.cycle 1 15 true (1),
.cycle 13 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 4 true (2),
.cycle 13 2 true (2)
])
theorem kid22_part431_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part431) = true := by rfl

def kid22_part407 : Audit := .split 11 (5,false) (byMove [(kid22_part408),(kid22_part409),(kid22_part410),(kid22_part411),(kid22_part412),(kid22_part413),(kid22_part414),(kid22_part415),(kid22_part416),(kid22_part417),(kid22_part418),(kid22_part419),(kid22_part420),(kid22_part421),(kid22_part422),(kid22_part423),(kid22_part424),(kid22_part425),(kid22_part426),(kid22_part427),(kid22_part428),(kid22_part429),(kid22_part430),(kid22_part431)])

theorem kid22_part407_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part407) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some mv)) (byMove [(kid22_part408),(kid22_part409),(kid22_part410),(kid22_part411),(kid22_part412),(kid22_part413),(kid22_part414),(kid22_part415),(kid22_part416),(kid22_part417),(kid22_part418),(kid22_part419),(kid22_part420),(kid22_part421),(kid22_part422),(kid22_part423),(kid22_part424),(kid22_part425),(kid22_part426),(kid22_part427),(kid22_part428),(kid22_part429),(kid22_part430),(kid22_part431)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part408_checked

  · exact kid22_part414_checked

  · exact kid22_part420_checked

  · exact kid22_part426_checked

  · exact kid22_part409_checked

  · exact kid22_part415_checked

  · exact kid22_part421_checked

  · exact kid22_part427_checked

  · exact kid22_part410_checked

  · exact kid22_part416_checked

  · exact kid22_part422_checked

  · exact kid22_part428_checked

  · exact kid22_part411_checked

  · exact kid22_part417_checked

  · exact kid22_part423_checked

  · exact kid22_part429_checked

  · exact kid22_part412_checked

  · exact kid22_part418_checked

  · exact kid22_part424_checked

  · exact kid22_part430_checked

  · exact kid22_part413_checked

  · exact kid22_part419_checked

  · exact kid22_part425_checked

  · exact kid22_part431_checked

def kid22_part433 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 17 8 false (1),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 6 16 true (1),
.last 15 (4,true),
.last 21 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 23 (4,true),
.cycle 1 15 true (1)
])
theorem kid22_part433_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part433) = true := by rfl

def kid22_part434 : Audit := .cycle 0 14 true (0)
theorem kid22_part434_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part434) = true := by rfl

def kid22_part435 : Audit := .split 17 (4,true) (byMove [
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.last 40 (2,true),
.cycle 12 8 true (0),
.cycle 27 1 false (3),
.last 20 (2,true),
.cycle 29 1 false (3),
.cycle 24 1 false (2),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 31 1 false (5),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 23 1 false (1),
.last 19 (2,true)
])
theorem kid22_part435_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part435) = true := by rfl

def kid22_part436 : Audit := .split 15 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 34 1 false (2),
.last 23 (4,true),
.cycle 24 1 false (2),
.cycle 0 19 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (1),
.last 17 (4,true),
.cycle 30 1 false (4),
.cycle 28 1 false (4),
.last 16 (4,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.last 35 (4,true),
.cycle 20 1 false (0),
.cycle 0 18 true (0)
])
theorem kid22_part436_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part436) = true := by rfl

def kid22_part437 : Audit := .cycle 13 2 false (-1)
theorem kid22_part437_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part437) = true := by rfl

def kid22_part438 : Audit := .cycle 13 1 false (-1)
theorem kid22_part438_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part438) = true := by rfl

def kid22_part439 : Audit := .cycle 1 11 true (1)
theorem kid22_part439_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part439) = true := by rfl

def kid22_part440 : Audit := .cycle 7 4 true (2)
theorem kid22_part440_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part440) = true := by rfl

def kid22_part441 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 21 (4,true),
.last 21 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 23 (4,true),
.last 23 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.last 20 (4,true)
])
theorem kid22_part441_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part441) = true := by rfl

def kid22_part442 : Audit := .cycle 0 12 true (0)
theorem kid22_part442_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part442) = true := by rfl

def kid22_part443 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 12 2 true (1),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 12 2 true (3),
.cycle 12 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.cycle 12 2 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 12 2 true (4)
])
theorem kid22_part443_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part443) = true := by rfl

def kid22_part444 : Audit := .cycle 9 2 true (2)
theorem kid22_part444_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part444) = true := by rfl

def kid22_part445 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 17 8 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 13 false (2),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (2),
.cycle 3 11 true (1),
.cycle 6 20 true (1),
.cycle 35 21 true (1),
.cycle 6 16 true (1),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 13 false (2),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 12 9 true (2)
])
theorem kid22_part445_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part445) = true := by rfl

def kid22_part446 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 16 6 false (0),
.cycle 16 1 false (0),
.last 21 (4,true),
.last 13 (4,true),
.cycle 14 4 false (0),
.cycle 1 13 true (1),
.last 18 (4,true),
.last 22 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 14 4 false (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 6 false (2)
])
theorem kid22_part446_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part446) = true := by rfl

def kid22_part447 : Audit := .cycle 1 13 true (1)
theorem kid22_part447_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part447) = true := by rfl

def kid22_part448 : Audit := .split 15 (4,true) (byMove [
.cycle 27 1 false (3),
.cycle 20 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 42 1 false (4),
.cycle 11 8 true (0),
.cycle 24 1 false (2),
.cycle 30 1 false (4),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 28 1 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 17 19 true (2),
.cycle 20 1 false (0),
.cycle 40 1 false (2)
])
theorem kid22_part448_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part448) = true := by rfl

def kid22_part449 : Audit := .cycle 13 2 false (-1)
theorem kid22_part449_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part449) = true := by rfl

def kid22_part450 : Audit := .cycle 13 1 false (-1)
theorem kid22_part450_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part450) = true := by rfl

def kid22_part451 : Audit := .cycle 1 11 true (1)
theorem kid22_part451_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part451) = true := by rfl

def kid22_part452 : Audit := .split 17 (4,true) (byMove [
.cycle 1 18 true (1),
.cycle 21 7 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 1 22 false (4),
.cycle 19 5 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 16 8 true (2),
.cycle 3 15 true (1),
.cycle 1 19 true (1),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 2, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 1 19 true (1),
.last 24 (2,true),
.cycle 19 5 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 2, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 18 true (1)
])
theorem kid22_part452_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part452) = true := by rfl

def kid22_part453 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 5 false (0),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 2 12 true (1),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 17 (4,true),
.cycle 2 11 true (1)
])
theorem kid22_part453_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part453) = true := by rfl

def kid22_part454 : Audit := .cycle 0 12 true (0)
theorem kid22_part454_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part454) = true := by rfl

def kid22_part455 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 5 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 7 false (1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (2),
.cycle 3 9 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 8 5 true (2),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 13 7 false (1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 20 5 false (2)
])
theorem kid22_part455_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part455) = true := by rfl

def kid22_part456 : Audit := .cycle 15 3 false (1)
theorem kid22_part456_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part456) = true := by rfl

def kid22_part432 : Audit := .split 10 (5,false) (byMove [(kid22_part433),(kid22_part434),(kid22_part435),(kid22_part436),(kid22_part437),(kid22_part438),(kid22_part439),(kid22_part440),(kid22_part441),(kid22_part442),(kid22_part443),(kid22_part444),(kid22_part445),(kid22_part446),(kid22_part447),(kid22_part448),(kid22_part449),(kid22_part450),(kid22_part451),(kid22_part452),(kid22_part453),(kid22_part454),(kid22_part455),(kid22_part456)])

theorem kid22_part432_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part432) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part433),(kid22_part434),(kid22_part435),(kid22_part436),(kid22_part437),(kid22_part438),(kid22_part439),(kid22_part440),(kid22_part441),(kid22_part442),(kid22_part443),(kid22_part444),(kid22_part445),(kid22_part446),(kid22_part447),(kid22_part448),(kid22_part449),(kid22_part450),(kid22_part451),(kid22_part452),(kid22_part453),(kid22_part454),(kid22_part455),(kid22_part456)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part433_checked

  · exact kid22_part439_checked

  · exact kid22_part445_checked

  · exact kid22_part451_checked

  · exact kid22_part434_checked

  · exact kid22_part440_checked

  · exact kid22_part446_checked

  · exact kid22_part452_checked

  · exact kid22_part435_checked

  · exact kid22_part441_checked

  · exact kid22_part447_checked

  · exact kid22_part453_checked

  · exact kid22_part436_checked

  · exact kid22_part442_checked

  · exact kid22_part448_checked

  · exact kid22_part454_checked

  · exact kid22_part437_checked

  · exact kid22_part443_checked

  · exact kid22_part449_checked

  · exact kid22_part455_checked

  · exact kid22_part438_checked

  · exact kid22_part444_checked

  · exact kid22_part450_checked

  · exact kid22_part456_checked

def kid22_part457 : Audit := .cycle 0 10 true (0)
theorem kid22_part457_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part457) = true := by rfl

def kid22_part458 : Audit := .cycle 1 9 true (1)
theorem kid22_part458_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part458) = true := by rfl

def kid22_part459 : Audit := .cycle 2 8 true (1)
theorem kid22_part459_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part459) = true := by rfl

def kid22_part460 : Audit := .cycle 1 12 true (1)
theorem kid22_part460_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part460) = true := by rfl

def kid22_part461 : Audit := .cycle 8 2 true (3)
theorem kid22_part461_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part461) = true := by rfl

def kid22_part462 : Audit := .split 10 (5,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 18 1 false (-2),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 21 (4,true),
.last 21 (4,true),
.cycle 6 12 true (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 18 1 false (-2),
.last 19 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 17 2 false (1),
.cycle 19 2 false (1),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 36 1 false (2),
.cycle 9 10 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.cycle 10 10 true (3),
.cycle 9 20 true (3),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 1 24 true (1),
.cycle 9 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 10 9 true (3)
]),
.cycle 3 8 true (1),
.cycle 10 2 true (4),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 22 (2,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 10 4 true (3),
.last 15 (2,true),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 22 (2,true),
.cycle 9 5 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 22 (4,true),
.last 29 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 21 (4,true),
.cycle 5 9 true (1),
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
.cycle 0 15 true (0),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 23 2 false (3),
.cycle 9 3 true (3),
.cycle 6 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 9 3 true (3)
]),
.cycle 9 3 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.cycle 10 1 true (4)
])
theorem kid22_part462_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part462) = true := by rfl

def kid22_part222 : Audit := .split 9 (5,true) (byMove [(kid22_part223),(kid22_part224),(kid22_part225),(kid22_part250),(kid22_part251),(kid22_part276),(kid22_part277),(kid22_part278),(kid22_part279),(kid22_part304),(kid22_part329),(kid22_part354),(kid22_part355),(kid22_part356),(kid22_part381),(kid22_part382),(kid22_part407),(kid22_part432),(kid22_part457),(kid22_part458),(kid22_part459),(kid22_part460),(kid22_part461),(kid22_part462)])

theorem kid22_part222_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (kid22_part222) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) 9 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part223),(kid22_part224),(kid22_part225),(kid22_part250),(kid22_part251),(kid22_part276),(kid22_part277),(kid22_part278),(kid22_part279),(kid22_part304),(kid22_part329),(kid22_part354),(kid22_part355),(kid22_part356),(kid22_part381),(kid22_part382),(kid22_part407),(kid22_part432),(kid22_part457),(kid22_part458),(kid22_part459),(kid22_part460),(kid22_part461),(kid22_part462)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part223_checked

  · exact kid22_part277_checked

  · exact kid22_part355_checked

  · exact kid22_part457_checked

  · exact kid22_part224_checked

  · exact kid22_part278_checked

  · exact kid22_part356_checked

  · exact kid22_part458_checked

  · exact kid22_part225_checked

  · exact kid22_part279_checked

  · exact kid22_part381_checked

  · exact kid22_part459_checked

  · exact kid22_part250_checked

  · exact kid22_part304_checked

  · exact kid22_part382_checked

  · exact kid22_part460_checked

  · exact kid22_part251_checked

  · exact kid22_part329_checked

  · exact kid22_part407_checked

  · exact kid22_part461_checked

  · exact kid22_part276_checked

  · exact kid22_part354_checked

  · exact kid22_part432_checked

  · exact kid22_part462_checked

def kid22_part463 : Audit := .cycle 0 9 true (0)
theorem kid22_part463_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,0⟩)) (kid22_part463) = true := by rfl

def kid22_part464 : Audit := .cycle 1 8 true (1)
theorem kid22_part464_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,1⟩)) (kid22_part464) = true := by rfl

def kid22_part466 : Audit := .cycle 1 17 true (1)
theorem kid22_part466_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part466) = true := by rfl

def kid22_part467 : Audit := .cycle 7 10 true (3)
theorem kid22_part467_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part467) = true := by rfl

def kid22_part468 : Audit := .split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 33 1 false (3),
.split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 34 1 false (2),
.last 22 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 44 1 false (8),
.cycle 18 1 true (4),
.cycle 7 13 true (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 28 1 false (0),
.cycle 30 1 false (0),
.last 22 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 18 1 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 38 1 false (8),
.cycle 29 1 false (3),
.cycle 37 1 false (5),
.split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 44 1 false (8),
.last 24 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 35 (5,true),
.cycle 38 1 false (8),
.cycle 38 1 false (4),
.cycle 18 1 true (6),
.cycle 7 13 true (3),
.cycle 17 3 true (5),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 17 3 true (5),
.last 24 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 18 1 true (6)
]),
.cycle 7 12 true (3),
.cycle 37 5 false (1),
.cycle 0 20 true (0),
.cycle 27 1 false (1),
.cycle 17 2 true (4),
.split 18 (5,false) (byMove [
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 0 22 true (0),
.last 22 (5,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 17 2 true (4),
.cycle 0 20 true (0),
.cycle 34 1 false (2),
.last 19 (5,true),
.last 23 (5,true),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 28 1 false (0),
.cycle 30 1 false (0),
.last 22 (5,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 20 (5,true),
.cycle 0 20 true (0),
.last 30 (5,true),
.last 19 (5,true)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (3),
.split 18 (5,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 17 2 true (5),
.cycle 0 20 true (0),
.cycle 34 1 false (2),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 2 30 true (1),
.cycle 18 1 true (6),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 34 1 false (2),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 18 1 true (6)
])
])
theorem kid22_part468_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part468) = true := by rfl

def kid22_part469 : Audit := .cycle 0 18 true (0)
theorem kid22_part469_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part469) = true := by rfl

def kid22_part470 : Audit := .cycle 33 1 false (3)
theorem kid22_part470_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part470) = true := by rfl

def kid22_part472 : Audit := .cycle 0 18 true (0)
theorem kid22_part472_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part472) = true := by rfl

def kid22_part473 : Audit := .cycle 1 17 true (1)
theorem kid22_part473_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part473) = true := by rfl

def kid22_part474 : Audit := .cycle 30 1 false (2)
theorem kid22_part474_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part474) = true := by rfl

def kid22_part475 : Audit := .cycle 27 1 false (1)
theorem kid22_part475_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part475) = true := by rfl

def kid22_part476 : Audit := .cycle 33 1 false (3)
theorem kid22_part476_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part476) = true := by rfl

def kid22_part477 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 34 1 false (2),
.cycle 23 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 44 1 false (8),
.cycle 18 1 true (4),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 28 1 false (0),
.last 20 (2,true),
.cycle 23 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 18 1 true (4)
])
theorem kid22_part477_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part477) = true := by rfl

def kid22_part478 : Audit := .cycle 0 18 true (0)
theorem kid22_part478_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part478) = true := by rfl

def kid22_part479 : Audit := .cycle 1 17 true (1)
theorem kid22_part479_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part479) = true := by rfl

def kid22_part480 : Audit := .cycle 38 1 false (8)
theorem kid22_part480_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part480) = true := by rfl

def kid22_part481 : Audit := .cycle 29 1 false (3)
theorem kid22_part481_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part481) = true := by rfl

def kid22_part482 : Audit := .split 34 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1284, 4, 4096, 128, 256, 8, 2, 4, 4096, 4096],[2, 1024, 256, 1, 4096, 16, 2, 1024, 256, 1, 4, 16, 4096],6176⟩,
.cycle 51 89 true (3),
.cycle 36 1 false (4),
.cycle 35 1 false (3),
.cycle 44 1 false (10),
.last 35 (5,false),
.cycle 0 41 true (0),
.cycle 53 1 false (13),
.cycle 40 1 false (10),
.cycle 42 1 false (10),
.last 36 (5,false),
.last 37 (5,false),
.cycle 36 33 true (4),
.cycle 70 1 false (10),
.cycle 0 45 true (0),
.cycle 35 1 false (3),
.cycle 33 2 true (3),
.last 35 (5,false),
.cycle 0 41 true (0),
.cycle 1 81 true (0),
.cycle 2 37 true (0),
.cycle 0 101 true (0),
.cycle 55 1 false (13),
.last 37 (5,false)
])
theorem kid22_part482_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part482) = true := by rfl

def kid22_part483 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 44 1 false (8),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 34 (2,true),
.cycle 38 1 false (8),
.last 39 (2,true),
.cycle 18 1 true (6),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.last 20 (2,true),
.cycle 31 1 false (7),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 18 1 true (6)
])
theorem kid22_part483_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part483) = true := by rfl

def kid22_part484 : Audit := .cycle 7 12 true (3)
theorem kid22_part484_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part484) = true := by rfl

def kid22_part485 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 35 1 false (1),
.cycle 0 21 true (0),
.last 21 (5,false),
.cycle 32 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.last 53 (5,false),
.last 20 (5,false),
.cycle 6 14 true (2),
.cycle 38 5 false (1),
.cycle 1 23 true (1),
.cycle 1 21 true (1),
.last 21 (5,false),
.cycle 32 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.last 20 (5,false)
])
theorem kid22_part485_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part485) = true := by rfl

def kid22_part486 : Audit := .cycle 0 20 true (0)
theorem kid22_part486_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part486) = true := by rfl

def kid22_part487 : Audit := .cycle 27 1 false (1)
theorem kid22_part487_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part487) = true := by rfl

def kid22_part488 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 34 1 false (2),
.cycle 31 1 false (1),
.cycle 37 1 false (3),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 44 1 false (8),
.cycle 33 1 false (3),
.last 40 (5,false),
.last 20 (5,false),
.cycle 7 14 true (3),
.last 47 (5,false),
.cycle 0 22 true (0),
.cycle 31 1 false (1),
.cycle 18 2 true (4),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.last 20 (5,false)
])
theorem kid22_part488_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part488) = true := by rfl

def kid22_part489 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 0 22 true (0),
.cycle 23 1 false (-1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 50 1 false (8),
.cycle 17 2 true (4),
.cycle 29 6 false (1),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 28 1 false (0),
.last 20 (2,true),
.cycle 23 1 false (-1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 30 3 false (0),
.cycle 29 3 false (1)
])
theorem kid22_part489_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part489) = true := by rfl

def kid22_part490 : Audit := .cycle 0 18 true (0)
theorem kid22_part490_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part490) = true := by rfl

def kid22_part491 : Audit := .cycle 1 17 true (1)
theorem kid22_part491_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part491) = true := by rfl

def kid22_part492 : Audit := .cycle 2 16 true (1)
theorem kid22_part492_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part492) = true := by rfl

def kid22_part493 : Audit := .cycle 1 20 true (1)
theorem kid22_part493_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part493) = true := by rfl

def kid22_part494 : Audit := .cycle 8 10 true (3)
theorem kid22_part494_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part494) = true := by rfl

def kid22_part495 : Audit := .split 18 (5,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 38 1 false (2),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 18 14 true (5),
.cycle 18 1 true (6),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.last 22 (2,true),
.cycle 17 3 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 18 1 true (6)
])
theorem kid22_part495_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part495) = true := by rfl

def kid22_part471 : Audit := .split 17 (5,true) (byMove [(kid22_part472),(kid22_part473),(kid22_part474),(kid22_part475),(kid22_part476),(kid22_part477),(kid22_part478),(kid22_part479),(kid22_part480),(kid22_part481),(kid22_part482),(kid22_part483),(kid22_part484),(kid22_part485),(kid22_part486),(kid22_part487),(kid22_part488),(kid22_part489),(kid22_part490),(kid22_part491),(kid22_part492),(kid22_part493),(kid22_part494),(kid22_part495)])

theorem kid22_part471_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part471) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part472),(kid22_part473),(kid22_part474),(kid22_part475),(kid22_part476),(kid22_part477),(kid22_part478),(kid22_part479),(kid22_part480),(kid22_part481),(kid22_part482),(kid22_part483),(kid22_part484),(kid22_part485),(kid22_part486),(kid22_part487),(kid22_part488),(kid22_part489),(kid22_part490),(kid22_part491),(kid22_part492),(kid22_part493),(kid22_part494),(kid22_part495)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part472_checked

  · exact kid22_part478_checked

  · exact kid22_part484_checked

  · exact kid22_part490_checked

  · exact kid22_part473_checked

  · exact kid22_part479_checked

  · exact kid22_part485_checked

  · exact kid22_part491_checked

  · exact kid22_part474_checked

  · exact kid22_part480_checked

  · exact kid22_part486_checked

  · exact kid22_part492_checked

  · exact kid22_part475_checked

  · exact kid22_part481_checked

  · exact kid22_part487_checked

  · exact kid22_part493_checked

  · exact kid22_part476_checked

  · exact kid22_part482_checked

  · exact kid22_part488_checked

  · exact kid22_part494_checked

  · exact kid22_part477_checked

  · exact kid22_part483_checked

  · exact kid22_part489_checked

  · exact kid22_part495_checked

def kid22_part496 : Audit := .cycle 0 17 true (0)
theorem kid22_part496_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part496) = true := by rfl

def kid22_part497 : Audit := .cycle 1 16 true (1)
theorem kid22_part497_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part497) = true := by rfl

def kid22_part498 : Audit := .cycle 9 8 true (3)
theorem kid22_part498_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part498) = true := by rfl

def kid22_part499 : Audit := .cycle 3 14 true (1)
theorem kid22_part499_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part499) = true := by rfl

def kid22_part500 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 64, 64],[2, 16, 64, 1, 16, 64, 64],96⟩
theorem kid22_part500_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part500) = true := by rfl

def kid22_part501 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (3),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 42 1 false (4),
.cycle 51 1 false (7),
.cycle 0 83 true (0),
.cycle 25 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 33 (2,true),
.cycle 0 73 true (0),
.cycle 71 1 false (7),
.cycle 27 1 false (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 37 1 false (3),
.last 21 (2,true),
.cycle 25 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 18 2 true (5)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 27 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 8 20 true (3),
.cycle 9 20 true (3),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 18 10 true (5),
.cycle 10 18 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
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
.cycle 8 20 true (3),
.cycle 9 20 true (3)
]),
.cycle 10 8 true (3),
.split 29 (5,true) (byMove [
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 11 20 true (3),
.last 34 (2,true),
.cycle 0 33 true (0),
.last 32 (2,true),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 15 16 true (5),
.last 31 (2,true),
.cycle 1 32 true (1),
.cycle 12 18 true (3),
.last 31 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 16 14 true (5),
.cycle 30 12 true (10)
]),
.cycle 17 1 true (7),
.cycle 7 12 true (3),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 32 (5,true),
.cycle 0 21 true (0),
.cycle 16 4 true (6),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.last 30 (5,true),
.cycle 17 3 true (6),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 15 6 true (5)
]),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.last 22 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (5,true),
.cycle 10 10 true (3),
.last 31 (5,true),
.cycle 17 3 true (6),
.cycle 7 14 true (3),
.cycle 15 7 true (5),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (6),
.last 22 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.last 22 (5,true)
]),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 50 1 false (6),
.last 71 (2,true),
.cycle 1 23 true (1),
.cycle 25 1 false (-1),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 93 1 false (17),
.cycle 39 1 false (9),
.cycle 7 18 true (3),
.last 21 (2,true),
.cycle 5 16 true (1),
.cycle 43 1 false (5),
.last 21 (2,true),
.cycle 25 1 false (-1),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 8 14 true (3),
.cycle 20 3 true (6)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (3),
.cycle 17 1 true (7)
])
theorem kid22_part501_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part501) = true := by rfl

def kid22_part502 : Audit := .cycle 6 11 true (2)
theorem kid22_part502_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part502) = true := by rfl

def kid22_part503 : Audit := .cycle 15 2 true (5)
theorem kid22_part503_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part503) = true := by rfl

def kid22_part504 : Audit := .split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 0 21 true (0),
.split 18 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 11 10 true (3),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 34 1 false (2),
.last 22 (5,true),
.cycle 7 13 true (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 58 1 false (10),
.last 20 (5,true),
.cycle 6 18 true (2),
.last 21 (5,true),
.cycle 7 15 true (3),
.cycle 28 1 false (0),
.cycle 62 3 false (10),
.last 22 (5,true),
.cycle 7 13 true (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 8 14 true (3),
.last 20 (5,true)
]),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 40 1 false (10),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 44 1 false (8),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 39 (5,false),
.cycle 38 1 false (8),
.cycle 68 1 false (18),
.last 19 (5,false),
.cycle 7 13 true (3),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.last 21 (5,false),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.last 19 (5,false)
]),
.cycle 14 8 true (4),
.cycle 37 5 false (1),
.cycle 1 20 true (1),
.cycle 27 1 false (1),
.cycle 17 2 true (4),
.split 18 (5,false) (byMove [
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 1 22 true (1),
.last 22 (5,true),
.cycle 6 13 true (2),
.cycle 15 4 true (4),
.cycle 17 2 true (4),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.last 19 (5,true),
.last 23 (5,true),
.last 21 (5,true),
.cycle 5 15 true (1),
.cycle 28 1 false (0),
.cycle 34 3 false (2),
.last 22 (5,true),
.cycle 6 13 true (2),
.last 22 (5,true),
.last 20 (5,true),
.cycle 1 20 true (1),
.last 30 (5,true),
.last 19 (5,true)
]),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.cycle 16 2 true (5),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.last 20 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 0 34 true (0),
.last 19 (5,false),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.cycle 17 2 true (5),
.cycle 1 20 true (1),
.cycle 1 22 true (1),
.last 20 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.last 19 (5,false)
])
])
theorem kid22_part504_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part504) = true := by rfl

def kid22_part505 : Audit := .cycle 1 18 true (1)
theorem kid22_part505_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part505) = true := by rfl

def kid22_part506 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 31 1 false (1),
.cycle 0 23 true (0),
.split 20 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 11 12 true (3),
.cycle 35 1 false (1),
.cycle 32 1 false (0),
.cycle 38 1 false (2),
.last 24 (5,true),
.cycle 7 15 true (3),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 62 1 false (10),
.last 22 (5,true),
.cycle 6 20 true (2),
.last 23 (5,true),
.cycle 7 17 true (3),
.cycle 32 1 false (0),
.cycle 31 3 false (0),
.last 24 (5,true),
.cycle 7 15 true (3),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.cycle 8 16 true (3),
.last 22 (5,true)
]),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 44 1 false (10),
.cycle 0 21 true (0),
.cycle 64 1 false (12),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 50 1 false (8),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 43 (5,false),
.cycle 44 1 false (8),
.cycle 54 1 false (12),
.last 21 (5,false),
.cycle 7 15 true (3),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 8 13 true (3),
.last 21 (5,false)
]),
.cycle 44 7 false (2),
.cycle 45 7 false (1),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.cycle 18 2 true (4),
.split 20 (5,false) (byMove [
.last 24 (5,true),
.cycle 1 24 true (1),
.cycle 35 1 false (1),
.cycle 32 1 false (0),
.cycle 1 24 true (1),
.last 24 (5,true),
.cycle 6 15 true (2),
.cycle 15 6 true (4),
.cycle 19 2 true (4),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.last 21 (5,true),
.cycle 32 8 false (2),
.last 23 (5,true),
.cycle 5 17 true (1),
.cycle 32 1 false (0),
.cycle 31 3 false (0),
.last 24 (5,true),
.cycle 6 15 true (2),
.cycle 44 7 false (2),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 37 5 false (1),
.last 21 (5,true)
]),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 16 4 true (4),
.split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 22 (5,false),
.cycle 0 22 true (0),
.last 24 (5,false),
.last 22 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (3),
.cycle 3 18 true (1),
.last 38 (5,false),
.last 21 (5,false),
.cycle 6 15 true (2),
.cycle 15 6 true (4),
.cycle 19 2 true (5),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.last 22 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 8 13 true (3),
.last 21 (5,false)
])
])
theorem kid22_part506_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part506) = true := by rfl

def kid22_part508 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 39 1 false (1),
.cycle 0 22 true (0),
.last 42 (5,false),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (3),
.cycle 3 18 true (1),
.last 36 (5,false),
.last 21 (5,false),
.cycle 6 15 true (2),
.cycle 15 12 true (4),
.cycle 5 19 true (1),
.cycle 1 22 true (1),
.last 42 (5,false),
.cycle 17 8 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 8 13 true (3),
.last 21 (5,false)
])
theorem kid22_part508_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part508) = true := by rfl

def kid22_part509 : Audit := .cycle 0 21 true (0)
theorem kid22_part509_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part509) = true := by rfl

def kid22_part510 : Audit := .cycle 30 1 false (2)
theorem kid22_part510_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part510) = true := by rfl

def kid22_part511 : Audit := .cycle 27 1 false (1)
theorem kid22_part511_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part511) = true := by rfl

def kid22_part512 : Audit := .cycle 0 21 true (0)
theorem kid22_part512_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part512) = true := by rfl

def kid22_part513 : Audit := .split 18 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 11 10 true (3),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 34 1 false (2),
.cycle 23 1 false (-1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.last 20 (2,true),
.cycle 21 1 true (5),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (3),
.cycle 28 1 false (0),
.last 20 (2,true),
.cycle 23 1 false (-1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (2,true),
.cycle 23 1 true (3)
])
theorem kid22_part513_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part513) = true := by rfl

def kid22_part514 : Audit := .cycle 1 18 true (1)
theorem kid22_part514_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part514) = true := by rfl

def kid22_part515 : Audit := .cycle 7 11 true (3)
theorem kid22_part515_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part515) = true := by rfl

def kid22_part516 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 44 1 false (8),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 40 1 false (10),
.cycle 38 1 false (8),
.last 37 (5,false),
.last 19 (5,false),
.cycle 7 13 true (3),
.cycle 15 6 true (5),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 18 2 true (5),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.last 19 (5,false)
])
theorem kid22_part516_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part516) = true := by rfl

def kid22_part517 : Audit := .cycle 0 19 true (0)
theorem kid22_part517_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part517) = true := by rfl

def kid22_part518 : Audit := .split 19 (5,false) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 31 1 false (1),
.cycle 0 23 true (0),
.cycle 27 1 false (3),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (5),
.cycle 60 1 false (12),
.cycle 14 12 true (4),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.last 21 (2,true),
.cycle 26 1 false (0),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 16 4 true (5),
.cycle 17 17 true (5)
])
theorem kid22_part518_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part518) = true := by rfl

def kid22_part519 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 40 1 false (8),
.cycle 36 1 false (6),
.cycle 44 1 false (10),
.cycle 27 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 44 1 false (12),
.cycle 40 1 false (10),
.cycle 48 1 false (14),
.cycle 19 1 true (7),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 37 1 false (7),
.last 21 (2,true),
.cycle 34 1 false (8),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 19 1 true (7)
])
theorem kid22_part519_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part519) = true := by rfl

def kid22_part520 : Audit := .cycle 14 8 true (4)
theorem kid22_part520_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part520) = true := by rfl

def kid22_part521 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.cycle 35 1 false (1),
.cycle 7 15 true (3),
.last 21 (5,false),
.cycle 32 3 false (0),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 8, 64, 64],[0, 2, 8, 0, 32, 2, 64],96⟩,
.cycle 0 21 true (0),
.last 21 (5,false),
.last 23 (5,false),
.cycle 14 6 true (4),
.cycle 38 5 false (1),
.cycle 5 17 true (1),
.cycle 5 15 true (1),
.last 21 (5,false),
.cycle 32 3 false (0),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 44 7 false (2),
.cycle 50 9 false (2)
])
theorem kid22_part521_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part521) = true := by rfl

def kid22_part522 : Audit := .cycle 1 20 true (1)
theorem kid22_part522_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part522) = true := by rfl

def kid22_part523 : Audit := .cycle 27 1 false (1)
theorem kid22_part523_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part523) = true := by rfl

def kid22_part524 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 31 1 false (1),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 44 1 false (10),
.cycle 0 21 true (0),
.last 21 (5,false),
.last 23 (5,false),
.last 25 (5,false),
.last 47 (5,false),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.cycle 18 2 true (4),
.last 20 (5,false),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 16 4 true (4),
.last 22 (5,false)
])
theorem kid22_part524_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part524) = true := by rfl

def kid22_part525 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.cycle 28 1 false (0),
.cycle 1 22 true (1),
.cycle 23 1 false (-1),
.cycle 6 13 true (2),
.cycle 15 4 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 18 2 true (4),
.cycle 17 2 true (4),
.cycle 29 6 false (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 28 1 false (0),
.last 20 (2,true),
.cycle 23 1 false (-1),
.cycle 6 13 true (2),
.cycle 37 5 false (1),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 30 3 false (0),
.cycle 29 3 false (1)
])
theorem kid22_part525_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part525) = true := by rfl

def kid22_part526 : Audit := .cycle 1 18 true (1)
theorem kid22_part526_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part526) = true := by rfl

def kid22_part527 : Audit := .cycle 7 11 true (3)
theorem kid22_part527_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part527) = true := by rfl

def kid22_part528 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 34 1 false (2),
.cycle 0 20 true (0),
.last 20 (5,false),
.cycle 2 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.last 32 (5,false),
.last 19 (5,false),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 20 (5,false),
.cycle 17 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.last 19 (5,false)
])
theorem kid22_part528_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part528) = true := by rfl

def kid22_part529 : Audit := .cycle 0 19 true (0)
theorem kid22_part529_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part529) = true := by rfl

def kid22_part530 : Audit := .cycle 16 2 true (5)
theorem kid22_part530_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part530) = true := by rfl

def kid22_part531 : Audit := .split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 16 4 true (5),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 17 14 true (5),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 17 5 true (5),
.cycle 17 3 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 19 1 true (7)
])
theorem kid22_part531_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part531) = true := by rfl

def kid22_part507 : Audit := .split 17 (5,true) (byMove [(kid22_part508),(kid22_part509),(kid22_part510),(kid22_part511),(kid22_part512),(kid22_part513),(kid22_part514),(kid22_part515),(kid22_part516),(kid22_part517),(kid22_part518),(kid22_part519),(kid22_part520),(kid22_part521),(kid22_part522),(kid22_part523),(kid22_part524),(kid22_part525),(kid22_part526),(kid22_part527),(kid22_part528),(kid22_part529),(kid22_part530),(kid22_part531)])

theorem kid22_part507_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part507) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part508),(kid22_part509),(kid22_part510),(kid22_part511),(kid22_part512),(kid22_part513),(kid22_part514),(kid22_part515),(kid22_part516),(kid22_part517),(kid22_part518),(kid22_part519),(kid22_part520),(kid22_part521),(kid22_part522),(kid22_part523),(kid22_part524),(kid22_part525),(kid22_part526),(kid22_part527),(kid22_part528),(kid22_part529),(kid22_part530),(kid22_part531)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part508_checked

  · exact kid22_part514_checked

  · exact kid22_part520_checked

  · exact kid22_part526_checked

  · exact kid22_part509_checked

  · exact kid22_part515_checked

  · exact kid22_part521_checked

  · exact kid22_part527_checked

  · exact kid22_part510_checked

  · exact kid22_part516_checked

  · exact kid22_part522_checked

  · exact kid22_part528_checked

  · exact kid22_part511_checked

  · exact kid22_part517_checked

  · exact kid22_part523_checked

  · exact kid22_part529_checked

  · exact kid22_part512_checked

  · exact kid22_part518_checked

  · exact kid22_part524_checked

  · exact kid22_part530_checked

  · exact kid22_part513_checked

  · exact kid22_part519_checked

  · exact kid22_part525_checked

  · exact kid22_part531_checked

def kid22_part532 : Audit := .cycle 0 17 true (0)
theorem kid22_part532_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part532) = true := by rfl

def kid22_part533 : Audit := .cycle 1 16 true (1)
theorem kid22_part533_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part533) = true := by rfl

def kid22_part534 : Audit := .cycle 2 15 true (1)
theorem kid22_part534_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part534) = true := by rfl

def kid22_part535 : Audit := .cycle 1 19 true (1)
theorem kid22_part535_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part535) = true := by rfl

def kid22_part536 : Audit := .cycle 8 9 true (3)
theorem kid22_part536_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part536) = true := by rfl

def kid22_part537 : Audit := .split 17 (5,false) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 30 (5,true),
.cycle 0 20 true (0),
.last 34 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.last 29 (5,true),
.cycle 2 18 true (1),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 17 2 true (6)
]),
.cycle 0 19 true (0),
.cycle 16 2 true (6),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 43 1 false (3),
.cycle 25 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 10 true (3),
.cycle 3 16 true (1),
.cycle 18 11 true (5),
.cycle 29 1 false (1),
.cycle 6 13 true (2),
.cycle 15 4 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 18 2 true (5),
.cycle 25 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 17 2 true (6)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 9 true (3),
.cycle 3 15 true (1),
.split 28 (5,true) (byMove [
.cycle 1 29 true (1),
.cycle 7 22 true (3),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 16 13 true (6),
.cycle 68 1 false (4),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 9 20 true (3),
.cycle 3 26 true (1),
.cycle 18 11 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 6 23 true (2),
.cycle 15 14 true (5),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 27 2 true (9),
.cycle 29 4 true (7),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 8 21 true (3),
.cycle 17 12 true (6)
]),
.cycle 17 1 true (7),
.cycle 6 12 true (2),
.cycle 15 3 true (5),
.split 18 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 1 21 true (1),
.last 30 (5,true),
.cycle 7 14 true (3),
.cycle 1 25 true (1),
.last 19 (5,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 29 (5,true),
.cycle 0 20 true (0),
.cycle 16 3 true (6),
.last 19 (5,true),
.cycle 14 5 true (4),
.last 21 (5,true),
.cycle 5 16 true (1),
.cycle 5 14 true (1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.cycle 16 3 true (6),
.last 19 (5,true)
]),
.cycle 1 19 true (1),
.split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 16 4 true (6),
.last 24 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.cycle 18 11 true (6),
.last 22 (2,true),
.cycle 6 14 true (2),
.cycle 15 5 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 18 2 true (6),
.last 24 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 17 3 true (6)
]),
.split 18 (5,true) (byMove [
.last 21 (2,true),
.last 21 (2,true),
.last 19 (2,true),
.cycle 7 14 true (3),
.cycle 1 25 true (1),
.cycle 25 1 false (-1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 16 3 true (6),
.cycle 46 1 false (10),
.cycle 14 5 true (4),
.cycle 15 7 true (5),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 18 2 true (5),
.cycle 25 1 false (-1),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 16 3 true (6),
.cycle 17 3 true (6)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (3),
.cycle 17 1 true (7)
])
theorem kid22_part537_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part537) = true := by rfl

def kid22_part465 : Audit := .split 16 (4,true) (byMove [(kid22_part466),(kid22_part467),(kid22_part468),(kid22_part469),(kid22_part470),(kid22_part471),(kid22_part496),(kid22_part497),(kid22_part498),(kid22_part499),(kid22_part500),(kid22_part501),(kid22_part502),(kid22_part503),(kid22_part504),(kid22_part505),(kid22_part506),(kid22_part507),(kid22_part532),(kid22_part533),(kid22_part534),(kid22_part535),(kid22_part536),(kid22_part537)])

theorem kid22_part465_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (kid22_part465) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) 16 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid22_part466),(kid22_part467),(kid22_part468),(kid22_part469),(kid22_part470),(kid22_part471),(kid22_part496),(kid22_part497),(kid22_part498),(kid22_part499),(kid22_part500),(kid22_part501),(kid22_part502),(kid22_part503),(kid22_part504),(kid22_part505),(kid22_part506),(kid22_part507),(kid22_part532),(kid22_part533),(kid22_part534),(kid22_part535),(kid22_part536),(kid22_part537)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part466_checked

  · exact kid22_part496_checked

  · exact kid22_part502_checked

  · exact kid22_part532_checked

  · exact kid22_part467_checked

  · exact kid22_part497_checked

  · exact kid22_part503_checked

  · exact kid22_part533_checked

  · exact kid22_part468_checked

  · exact kid22_part498_checked

  · exact kid22_part504_checked

  · exact kid22_part534_checked

  · exact kid22_part469_checked

  · exact kid22_part499_checked

  · exact kid22_part505_checked

  · exact kid22_part535_checked

  · exact kid22_part470_checked

  · exact kid22_part500_checked

  · exact kid22_part506_checked

  · exact kid22_part536_checked

  · exact kid22_part471_checked

  · exact kid22_part501_checked

  · exact kid22_part507_checked

  · exact kid22_part537_checked

def kid22_part538 : Audit := .cycle 3 6 true (1)
theorem kid22_part538_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (kid22_part538) = true := by rfl

def kid22_part539 : Audit := .cycle 8 1 true (4)
theorem kid22_part539_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,4⟩)) (kid22_part539) = true := by rfl

def kid22_part541 : Audit := .cycle 0 10 true (0)
theorem kid22_part541_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part541) = true := by rfl

def kid22_part542 : Audit := .cycle 1 9 true (1)
theorem kid22_part542_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part542) = true := by rfl

def kid22_part543 : Audit := .cycle 2 8 true (1)
theorem kid22_part543_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part543) = true := by rfl

def kid22_part544 : Audit := .cycle 1 12 true (1)
theorem kid22_part544_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part544) = true := by rfl

def kid22_part545 : Audit := .cycle 8 2 true (4)
theorem kid22_part545_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part545) = true := by rfl

def kid22_part546 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 56 1 false (6),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.last 24 (2,true),
.last 22 (2,true)
]),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 21 (4,true) (byMove [
.last 24 (2,true),
.last 25 (2,true),
.last 22 (2,true),
.cycle 0 27 true (0),
.cycle 24 1 false (2),
.cycle 38 1 false (10),
.cycle 6 16 true (0),
.cycle 46 14 true (8),
.last 22 (2,true),
.cycle 0 53 true (0),
.cycle 32 1 false (4),
.last 23 (2,true),
.cycle 35 1 false (7),
.cycle 20 2 true (2),
.last 22 (2,true),
.cycle 40 1 false (10),
.last 25 (2,true),
.last 23 (2,true),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 22 (2,true),
.cycle 22 30 true (3),
.cycle 23 12 true (4),
.last 23 (2,true)
]),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 35 1 false (5),
.last 20 (2,true),
.cycle 36 1 false (6),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 27 1 false (3),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 27 1 false (5),
.cycle 36 1 false (8),
.cycle 34 1 false (8),
.cycle 0 54 true (0),
.cycle 3 22 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 3 22 true (0),
.cycle 3 18 true (0)
]),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.cycle 6 12 true (2),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 27 (4,true),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.last 27 (4,true),
.last 23 (4,true),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 19 (4,true),
.last 17 (4,true)
]),
.cycle 0 14 true (0),
.split 17 (4,true) (byMove [
.cycle 30 1 false (4),
.cycle 23 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 49 1 false (5),
.cycle 12 8 true (0),
.cycle 27 1 false (3),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 35 1 false (5),
.cycle 33 1 false (5)
]),
.cycle 11 2 true (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
])
theorem kid22_part546_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part546) = true := by rfl

def kid22_part547 : Audit := .cycle 0 10 true (0)
theorem kid22_part547_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part547) = true := by rfl

def kid22_part548 : Audit := .cycle 1 9 true (1)
theorem kid22_part548_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part548) = true := by rfl

def kid22_part550 : Audit := .split 21 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (3),
.cycle 39 1 false (3),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 1 30 true (1),
.cycle 3 19 true (1),
.cycle 0 38 true (0),
.cycle 9 13 true (3),
.cycle 6 16 true (2),
.cycle 1 24 true (1),
.cycle 1 25 true (1),
.cycle 1 23 true (1),
.cycle 18 8 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 8 14 true (3),
.cycle 1 31 true (1)
])
theorem kid22_part550_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part550) = true := by rfl

def kid22_part551 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 8 14 true (3),
.cycle 7 24 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 10 12 true (3),
.cycle 7 22 true (3),
.cycle 0 42 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 32, 4, 64],[2, 16, 64, 1, 40, 32, 64],64⟩,
.cycle 7 16 true (3),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.cycle 20 2 true (6),
.last 23 (2,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 8 14 true (3),
.cycle 7 24 true (3)
])
theorem kid22_part551_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part551) = true := by rfl

def kid22_part552 : Audit := .split 19 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 28 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 0 24 true (0),
.cycle 35 1 false (3),
.cycle 7 14 true (3),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 31 1 false (3),
.last 21 (5,true),
.last 41 (5,true),
.last 23 (5,true),
.cycle 39 5 false (1),
.cycle 7 16 true (3),
.cycle 29 1 false (1),
.last 21 (5,true),
.cycle 19 2 true (4),
.cycle 7 14 true (3),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 21 10 true (7)
])
theorem kid22_part552_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part552) = true := by rfl

def kid22_part553 : Audit := .cycle 7 14 true (3)
theorem kid22_part553_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part553) = true := by rfl

def kid22_part554 : Audit := .cycle 0 24 true (0)
theorem kid22_part554_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part554) = true := by rfl

def kid22_part555 : Audit := .split 19 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 28 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 0 24 true (0),
.cycle 35 1 false (3),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 31 1 false (3),
.cycle 56 1 false (12),
.last 21 (2,true),
.cycle 7 18 true (3),
.last 21 (2,true),
.cycle 7 16 true (3),
.cycle 29 1 false (1),
.cycle 19 2 true (4),
.last 21 (2,true),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 8 14 true (3),
.last 21 (2,true)
])
theorem kid22_part555_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part555) = true := by rfl

def kid22_part556 : Audit := .cycle 1 19 true (1)
theorem kid22_part556_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part556) = true := by rfl

def kid22_part557 : Audit := .cycle 7 12 true (3)
theorem kid22_part557_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part557) = true := by rfl

def kid22_part558 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 21 8 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (3),
.cycle 20 8 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.last 32 (5,true),
.cycle 7 14 true (3),
.cycle 22 8 true (6),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 19 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 21 8 true (7)
])
theorem kid22_part558_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part558) = true := by rfl

def kid22_part559 : Audit := .cycle 0 20 true (0)
theorem kid22_part559_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part559) = true := by rfl

def kid22_part560 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 4, 64],[2, 16, 64, 1, 16, 64, 64],64⟩
theorem kid22_part560_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part560) = true := by rfl

def kid22_part561 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 9 20 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (3),
.cycle 9 18 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 19 2 true (6),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 9 20 true (3)
])
theorem kid22_part561_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part561) = true := by rfl

def kid22_part562 : Audit := .cycle 6 16 true (2)
theorem kid22_part562_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part562) = true := by rfl

def kid22_part563 : Audit := .cycle 17 2 true (5)
theorem kid22_part563_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part563) = true := by rfl

def kid22_part564 : Audit := .split 19 (2,true) (byMove [
.cycle 1 26 true (1),
.cycle 1 23 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 67 1 false (11),
.cycle 1 23 true (1),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.cycle 45 1 false (11),
.cycle 1 21 true (1),
.cycle 1 23 true (1),
.last 20 (5,true),
.cycle 16 8 true (4),
.cycle 39 5 false (1),
.cycle 5 16 true (1),
.cycle 29 1 false (1),
.last 21 (5,true),
.cycle 19 2 true (4),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.cycle 18 2 true (5),
.last 20 (5,true)
])
theorem kid22_part564_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part564) = true := by rfl

def kid22_part565 : Audit := .cycle 5 14 true (1)
theorem kid22_part565_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part565) = true := by rfl

def kid22_part566 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 36 1 false (2),
.cycle 33 1 false (1),
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 6 16 true (2),
.cycle 7 20 true (3),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 79 1 false (15),
.cycle 53 1 false (13),
.cycle 46 7 false (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 33 1 false (1),
.cycle 20 2 true (4),
.last 23 (2,true),
.cycle 6 16 true (2),
.cycle 18 6 true (4),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 18 4 true (4),
.cycle 22 13 true (6)
])
theorem kid22_part566_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part566) = true := by rfl

def kid22_part567 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 22 (2,true),
.cycle 49 1 false (13),
.cycle 16 8 true (4),
.last 21 (2,true),
.cycle 5 16 true (1),
.cycle 29 1 false (1),
.cycle 19 2 true (4),
.last 21 (2,true),
.cycle 6 14 true (2),
.cycle 7 16 true (3),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 18 2 true (5),
.cycle 20 11 true (6)
])
theorem kid22_part567_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part567) = true := by rfl

def kid22_part568 : Audit := .cycle 1 19 true (1)
theorem kid22_part568_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part568) = true := by rfl

def kid22_part569 : Audit := .cycle 7 12 true (3)
theorem kid22_part569_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part569) = true := by rfl

def kid22_part570 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 36 1 false (2),
.cycle 0 21 true (0),
.cycle 2 19 true (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 26 true (1),
.cycle 3 17 true (1),
.cycle 2 32 true (1),
.cycle 9 11 true (3),
.cycle 6 14 true (2),
.cycle 2 20 true (1),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.cycle 18 2 true (6),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 2 27 true (1)
])
theorem kid22_part570_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part570) = true := by rfl

def kid22_part571 : Audit := .cycle 0 20 true (0)
theorem kid22_part571_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part571) = true := by rfl

def kid22_part572 : Audit := .cycle 8 12 true (3)
theorem kid22_part572_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part572) = true := by rfl

def kid22_part573 : Audit := .split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 20 9 true (6),
.cycle 39 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 20 9 true (6),
.cycle 3 17 true (1),
.cycle 33 9 true (11),
.cycle 9 11 true (3),
.cycle 6 14 true (2),
.cycle 20 9 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 18 2 true (6),
.last 23 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 20 9 true (7)
])
theorem kid22_part573_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part573) = true := by rfl

def kid22_part549 : Audit := .split 18 (4,true) (byMove [(kid22_part550),(kid22_part551),(kid22_part552),(kid22_part553),(kid22_part554),(kid22_part555),(kid22_part556),(kid22_part557),(kid22_part558),(kid22_part559),(kid22_part560),(kid22_part561),(kid22_part562),(kid22_part563),(kid22_part564),(kid22_part565),(kid22_part566),(kid22_part567),(kid22_part568),(kid22_part569),(kid22_part570),(kid22_part571),(kid22_part572),(kid22_part573)])

theorem kid22_part549_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part549) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid22_part550),(kid22_part551),(kid22_part552),(kid22_part553),(kid22_part554),(kid22_part555),(kid22_part556),(kid22_part557),(kid22_part558),(kid22_part559),(kid22_part560),(kid22_part561),(kid22_part562),(kid22_part563),(kid22_part564),(kid22_part565),(kid22_part566),(kid22_part567),(kid22_part568),(kid22_part569),(kid22_part570),(kid22_part571),(kid22_part572),(kid22_part573)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part550_checked

  · exact kid22_part556_checked

  · exact kid22_part562_checked

  · exact kid22_part568_checked

  · exact kid22_part551_checked

  · exact kid22_part557_checked

  · exact kid22_part563_checked

  · exact kid22_part569_checked

  · exact kid22_part552_checked

  · exact kid22_part558_checked

  · exact kid22_part564_checked

  · exact kid22_part570_checked

  · exact kid22_part553_checked

  · exact kid22_part559_checked

  · exact kid22_part565_checked

  · exact kid22_part571_checked

  · exact kid22_part554_checked

  · exact kid22_part560_checked

  · exact kid22_part566_checked

  · exact kid22_part572_checked

  · exact kid22_part555_checked

  · exact kid22_part561_checked

  · exact kid22_part567_checked

  · exact kid22_part573_checked

def kid22_part574 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (1),
.cycle 7 10 true (3),
.split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 38 1 false (8),
.cycle 29 1 false (3),
.last 34 (5,true),
.cycle 38 1 false (8),
.cycle 7 12 true (3),
.cycle 37 5 false (1),
.cycle 0 20 true (0),
.cycle 27 1 false (1),
.last 19 (5,true),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (3),
.cycle 3 16 true (1)
]),
.cycle 0 18 true (0),
.cycle 33 1 false (3),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 38 1 false (8),
.cycle 29 1 false (3),
.cycle 37 1 false (5),
.cycle 38 1 false (8),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 27 1 false (1),
.cycle 17 2 true (4),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (3),
.cycle 3 16 true (1)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 10 8 true (3),
.cycle 3 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 8, 64],[2, 16, 64, 1, 16, 64, 64],64⟩,
.cycle 9 8 true (3),
.cycle 6 11 true (2),
.cycle 15 2 true (5),
.split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 40 1 false (10),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.last 18 (5,true),
.cycle 14 8 true (4),
.cycle 37 5 false (1),
.cycle 1 20 true (1),
.cycle 27 1 false (1),
.last 19 (5,true),
.cycle 1 20 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.cycle 16 2 true (5),
.last 18 (5,true)
]),
.cycle 1 18 true (1),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 31 1 false (1),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 64 1 false (12),
.cycle 44 1 false (10),
.cycle 44 7 false (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 31 1 false (1),
.cycle 18 2 true (4),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 16 4 true (4),
.cycle 3 19 true (1)
]),
.split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 0 21 true (0),
.cycle 30 1 false (2),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.cycle 40 1 false (10),
.cycle 14 8 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 27 1 false (1),
.cycle 17 2 true (4),
.cycle 1 20 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (5),
.cycle 3 17 true (1)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 8 9 true (3),
.cycle 3 15 true (1)
])
theorem kid22_part574_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part574) = true := by rfl

def kid22_part575 : Audit := .cycle 8 2 true (4)
theorem kid22_part575_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part575) = true := by rfl

def kid22_part576 : Audit := .cycle 9 1 true (5)
theorem kid22_part576_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part576) = true := by rfl

def kid22_part577 : Audit := .cycle 7 4 true (3)
theorem kid22_part577_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part577) = true := by rfl

def kid22_part579 : Audit := .cycle 1 12 true (1)
theorem kid22_part579_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part579) = true := by rfl

def kid22_part580 : Audit := .cycle 7 5 true (3)
theorem kid22_part580_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part580) = true := by rfl

def kid22_part581 : Audit := .split 21 (4,true) (byMove [
.cycle 37 1 false (5),
.cycle 30 1 false (2),
.cycle 24 1 false (2),
.cycle 0 23 true (0),
.cycle 29 1 false (1),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 64 1 false (6),
.cycle 14 8 true (0),
.cycle 34 1 false (4),
.cycle 40 1 false (4),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.cycle 20 2 true (2),
.cycle 24 1 false (2),
.cycle 38 1 false (6),
.last 24 (5,true),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (2),
.cycle 30 1 false (2),
.cycle 20 3 true (2)
])
theorem kid22_part581_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part581) = true := by rfl

def kid22_part582 : Audit := .cycle 0 13 true (0)
theorem kid22_part582_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part582) = true := by rfl

def kid22_part583 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 37 1 false (1),
.cycle 0 14 true (0),
.cycle 24 5 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 8 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 17 11 true (1),
.cycle 1 14 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (4),
.cycle 12 3 true (4)
])
theorem kid22_part583_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part583) = true := by rfl

def kid22_part584 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 24 1 false (-2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 15 11 false (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 18 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (4),
.last 15 (4,true)
])
theorem kid22_part584_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part584) = true := by rfl

def kid22_part585 : Audit := .cycle 0 12 true (0)
theorem kid22_part585_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part585) = true := by rfl

def kid22_part586 : Audit := .cycle 1 11 true (1)
theorem kid22_part586_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part586) = true := by rfl

def kid22_part587 : Audit := .split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 1 34 true (1),
.cycle 0 21 true (0),
.cycle 8 13 true (4),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (4),
.cycle 3 17 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4),
.cycle 6 14 true (2),
.cycle 18 2 true (6),
.cycle 65 1 false (13),
.cycle 1 21 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 18 3 true (6)
])
theorem kid22_part587_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part587) = true := by rfl

def kid22_part588 : Audit := .cycle 3 9 true (1)
theorem kid22_part588_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part588) = true := by rfl

def kid22_part589 : Audit := .cycle 8 4 true (4)
theorem kid22_part589_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part589) = true := by rfl

def kid22_part590 : Audit := .cycle 9 3 true (4)
theorem kid22_part590_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part590) = true := by rfl

def kid22_part591 : Audit := .cycle 6 6 true (2)
theorem kid22_part591_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part591) = true := by rfl

def kid22_part592 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 27 5 false (1),
.cycle 0 15 true (0),
.cycle 29 7 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 27 5 false (1),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid22_part592_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part592) = true := by rfl

def kid22_part593 : Audit := .cycle 5 10 true (1)
theorem kid22_part593_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part593) = true := by rfl

def kid22_part594 : Audit := .cycle 1 13 true (1)
theorem kid22_part594_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part594) = true := by rfl

def kid22_part595 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (3),
.last 15 (5,true),
.last 15 (5,true),
.cycle 7 8 true (3),
.cycle 24 5 false (0),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 8 6 true (4),
.last 13 (5,true),
.cycle 6 10 true (2),
.cycle 12 2 true (3),
.last 15 (5,true),
.cycle 5 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.cycle 8 6 true (4),
.last 13 (5,true)
])
theorem kid22_part595_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part595) = true := by rfl

def kid22_part596 : Audit := .split 12 (5,true) (byMove [
.cycle 10 8 true (3),
.cycle 1 15 true (1),
.cycle 24 1 false (-2),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 18 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 16 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 5 true (4),
.last 15 (4,true),
.last 14 (4,true),
.last 27 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 18 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid22_part596_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part596) = true := by rfl

def kid22_part597 : Audit := .cycle 0 12 true (0)
theorem kid22_part597_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part597) = true := by rfl

def kid22_part598 : Audit := .cycle 1 11 true (1)
theorem kid22_part598_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part598) = true := by rfl

def kid22_part599 : Audit := .cycle 2 10 true (1)
theorem kid22_part599_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part599) = true := by rfl

def kid22_part600 : Audit := .cycle 1 14 true (1)
theorem kid22_part600_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part600) = true := by rfl

def kid22_part601 : Audit := .cycle 8 4 true (4)
theorem kid22_part601_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part601) = true := by rfl

def kid22_part602 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 11 4 true (5),
.cycle 0 16 true (0),
.cycle 34 9 false (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (5),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 6 9 true (2),
.cycle 13 2 true (5),
.last 16 (5,true),
.cycle 1 16 true (1),
.last 19 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid22_part602_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part602) = true := by rfl

def kid22_part578 : Audit := .split 11 (2,true) (byMove [(kid22_part579),(kid22_part580),(kid22_part581),(kid22_part582),(kid22_part583),(kid22_part584),(kid22_part585),(kid22_part586),(kid22_part587),(kid22_part588),(kid22_part589),(kid22_part590),(kid22_part591),(kid22_part592),(kid22_part593),(kid22_part594),(kid22_part595),(kid22_part596),(kid22_part597),(kid22_part598),(kid22_part599),(kid22_part600),(kid22_part601),(kid22_part602)])

theorem kid22_part578_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part578) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid22_part579),(kid22_part580),(kid22_part581),(kid22_part582),(kid22_part583),(kid22_part584),(kid22_part585),(kid22_part586),(kid22_part587),(kid22_part588),(kid22_part589),(kid22_part590),(kid22_part591),(kid22_part592),(kid22_part593),(kid22_part594),(kid22_part595),(kid22_part596),(kid22_part597),(kid22_part598),(kid22_part599),(kid22_part600),(kid22_part601),(kid22_part602)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part579_checked

  · exact kid22_part585_checked

  · exact kid22_part591_checked

  · exact kid22_part597_checked

  · exact kid22_part580_checked

  · exact kid22_part586_checked

  · exact kid22_part592_checked

  · exact kid22_part598_checked

  · exact kid22_part581_checked

  · exact kid22_part587_checked

  · exact kid22_part593_checked

  · exact kid22_part599_checked

  · exact kid22_part582_checked

  · exact kid22_part588_checked

  · exact kid22_part594_checked

  · exact kid22_part600_checked

  · exact kid22_part583_checked

  · exact kid22_part589_checked

  · exact kid22_part595_checked

  · exact kid22_part601_checked

  · exact kid22_part584_checked

  · exact kid22_part590_checked

  · exact kid22_part596_checked

  · exact kid22_part602_checked

def kid22_part603 : Audit := .cycle 0 12 true (0)
theorem kid22_part603_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part603) = true := by rfl

def kid22_part604 : Audit := .cycle 4 6 true (1)
theorem kid22_part604_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part604) = true := by rfl

def kid22_part605 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.last 22 (2,true),
.cycle 23 1 false (1),
.cycle 24 3 false (0),
.cycle 19 3 false (-1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 35 3 false (3),
.cycle 23 3 false (1),
.cycle 6 11 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 29 1 false (3),
.cycle 21 3 false (0),
.cycle 19 3 false (-1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 22 3 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 10 12 true (3),
.last 21 (2,true),
.cycle 7 16 true (3),
.cycle 0 28 true (0),
.cycle 0 24 true (0),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 20, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.cycle 11 10 true (3),
.cycle 6 18 true (2),
.cycle 19 2 true (5),
.last 21 (2,true),
.cycle 5 16 true (1),
.last 24 (2,true),
.last 22 (2,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 8 14 true (3),
.cycle 20 11 true (6)
]),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 39 1 false (3),
.cycle 31 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 12 8 true (3),
.cycle 3 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 24, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 9 10 true (3),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 3 19 true (1)
]),
.cycle 8 4 true (4),
.cycle 9 3 true (4),
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 5 12 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (4),
.last 15 (4,true)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 10 2 true (4),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (1),
.last 22 (2,true),
.cycle 23 1 false (1),
.cycle 24 3 false (0),
.cycle 19 3 false (-1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 45 3 false (9),
.cycle 23 3 false (1),
.cycle 6 14 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 39 1 false (7),
.cycle 21 3 false (0),
.cycle 19 3 false (-1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 22 3 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.last 21 (2,true),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 11 3 true (5),
.cycle 6 11 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 20 5 true (4),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 11 3 true (5)
])
])
theorem kid22_part605_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part605) = true := by rfl

def kid22_part607 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 33 1 false (1),
.cycle 13 10 true (3),
.last 15 (4,true),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 24 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 16 true (0),
.last 17 (4,true),
.last 16 (4,true),
.last 21 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.cycle 11 8 true (2),
.cycle 1 15 true (1),
.cycle 13 8 true (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (1)
])
theorem kid22_part607_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part607) = true := by rfl

def kid22_part608 : Audit := .cycle 1 15 true (1)
theorem kid22_part608_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part608) = true := by rfl

def kid22_part609 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 36 1 false (4),
.last 20 (2,true),
.cycle 0 25 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.last 20 (2,true),
.cycle 0 49 true (0),
.cycle 30 1 false (2),
.cycle 32 1 false (4),
.cycle 33 1 false (5),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 38 1 false (8),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 20 28 true (3),
.last 26 (2,true),
.last 21 (2,true)
])
theorem kid22_part609_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part609) = true := by rfl

def kid22_part610 : Audit := .split 23 (2,true) (byMove [
.cycle 36 1 false (6),
.cycle 29 1 false (3),
.cycle 26 1 false (4),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 25 1 false (3),
.cycle 0 24 true (0),
.last 41 (4,true),
.last 31 (4,true),
.cycle 33 1 false (5),
.cycle 29 1 false (3),
.cycle 27 1 false (3),
.cycle 30 1 false (4),
.last 25 (4,true),
.cycle 39 1 false (7),
.cycle 37 1 false (7),
.last 24 (4,true),
.cycle 25 1 false (3),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.last 45 (4,true),
.last 31 (4,true),
.last 36 (4,true)
])
theorem kid22_part610_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part610) = true := by rfl

def kid22_part611 : Audit := .cycle 18 1 false (0)
theorem kid22_part611_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part611) = true := by rfl

def kid22_part612 : Audit := .cycle 15 1 false (-1)
theorem kid22_part612_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part612) = true := by rfl

def kid22_part613 : Audit := .cycle 6 6 true (2)
theorem kid22_part613_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part613) = true := by rfl

def kid22_part614 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 9 5 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 7 10 true (3),
.cycle 7 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 7 9 true (3)
])
theorem kid22_part614_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part614) = true := by rfl

def kid22_part615 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 21 (4,true),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 25 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 25 (4,true),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.last 19 (4,true),
.last 29 (4,true),
.cycle 18 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true)
])
theorem kid22_part615_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part615) = true := by rfl

def kid22_part616 : Audit := .cycle 1 13 true (1)
theorem kid22_part616_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part616) = true := by rfl

def kid22_part617 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 22 (2,true),
.last 23 (2,true),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 31 1 false (9),
.cycle 30 1 false (8),
.cycle 6 10 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 38 1 false (8),
.cycle 49 1 false (9),
.cycle 18 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 20 3 true (6)
])
theorem kid22_part617_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part617) = true := by rfl

def kid22_part618 : Audit := .cycle 27 1 false (7)
theorem kid22_part618_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part618) = true := by rfl

def kid22_part619 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 13 12 true (3),
.last 15 (2,true),
.cycle 13 10 true (3),
.cycle 27 1 false (-1),
.cycle 17 14 true (3),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 13 10 true (3),
.cycle 6 12 true (2),
.cycle 13 2 true (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 22 7 false (2),
.cycle 11 8 true (2),
.cycle 1 15 true (1),
.cycle 13 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 8 true (3),
.cycle 6 10 true (2)
])
theorem kid22_part619_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part619) = true := by rfl

def kid22_part620 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (1),
.last 30 (4,true),
.cycle 28 1 false (2),
.last 17 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 25 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 24 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 16 (4,true)
])
theorem kid22_part620_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part620) = true := by rfl

def kid22_part621 : Audit := .cycle 5 8 true (1)
theorem kid22_part621_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part621) = true := by rfl

def kid22_part622 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 31 1 false (3),
.last 18 (2,true),
.cycle 0 23 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 6 12 true (0),
.cycle 38 10 true (8),
.last 18 (2,true),
.cycle 0 45 true (0),
.cycle 27 1 false (1),
.cycle 27 1 false (3),
.cycle 30 1 false (4),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 35 1 false (7),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.last 18 (2,true),
.cycle 18 26 true (3),
.cycle 19 8 true (4),
.cycle 5 14 true (0)
])
theorem kid22_part622_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part622) = true := by rfl

def kid22_part623 : Audit := .cycle 11 2 true (2)
theorem kid22_part623_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part623) = true := by rfl

def kid22_part624 : Audit := .cycle 15 1 false (-1)
theorem kid22_part624_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part624) = true := by rfl

def kid22_part625 : Audit := .cycle 6 6 true (2)
theorem kid22_part625_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part625) = true := by rfl

def kid22_part626 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (0),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 9 5 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 6 true (2),
.cycle 7 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 7 9 true (3)
])
theorem kid22_part626_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part626) = true := by rfl

def kid22_part627 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 2 14 true (1),
.last 21 (4,true),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 12 true (1)
])
theorem kid22_part627_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part627) = true := by rfl

def kid22_part628 : Audit := .cycle 1 13 true (1)
theorem kid22_part628_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part628) = true := by rfl

def kid22_part629 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 8 8 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 22 1 false (0),
.cycle 8 8 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 8 6 true (3),
.cycle 6 10 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 11 4 true (2),
.cycle 11 2 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 8 6 true (3)
])
theorem kid22_part629_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part629) = true := by rfl

def kid22_part630 : Audit := .cycle 12 3 true (4)
theorem kid22_part630_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part630) = true := by rfl

def kid22_part606 : Audit := .split 11 (5,true) (byMove [(kid22_part607),(kid22_part608),(kid22_part609),(kid22_part610),(kid22_part611),(kid22_part612),(kid22_part613),(kid22_part614),(kid22_part615),(kid22_part616),(kid22_part617),(kid22_part618),(kid22_part619),(kid22_part620),(kid22_part621),(kid22_part622),(kid22_part623),(kid22_part624),(kid22_part625),(kid22_part626),(kid22_part627),(kid22_part628),(kid22_part629),(kid22_part630)])

theorem kid22_part606_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part606) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part607),(kid22_part608),(kid22_part609),(kid22_part610),(kid22_part611),(kid22_part612),(kid22_part613),(kid22_part614),(kid22_part615),(kid22_part616),(kid22_part617),(kid22_part618),(kid22_part619),(kid22_part620),(kid22_part621),(kid22_part622),(kid22_part623),(kid22_part624),(kid22_part625),(kid22_part626),(kid22_part627),(kid22_part628),(kid22_part629),(kid22_part630)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part607_checked

  · exact kid22_part613_checked

  · exact kid22_part619_checked

  · exact kid22_part625_checked

  · exact kid22_part608_checked

  · exact kid22_part614_checked

  · exact kid22_part620_checked

  · exact kid22_part626_checked

  · exact kid22_part609_checked

  · exact kid22_part615_checked

  · exact kid22_part621_checked

  · exact kid22_part627_checked

  · exact kid22_part610_checked

  · exact kid22_part616_checked

  · exact kid22_part622_checked

  · exact kid22_part628_checked

  · exact kid22_part611_checked

  · exact kid22_part617_checked

  · exact kid22_part623_checked

  · exact kid22_part629_checked

  · exact kid22_part612_checked

  · exact kid22_part618_checked

  · exact kid22_part624_checked

  · exact kid22_part630_checked

def kid22_part631 : Audit := .cycle 0 10 true (0)
theorem kid22_part631_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part631) = true := by rfl

def kid22_part632 : Audit := .cycle 1 9 true (1)
theorem kid22_part632_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part632) = true := by rfl

def kid22_part633 : Audit := .cycle 2 8 true (1)
theorem kid22_part633_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part633) = true := by rfl

def kid22_part634 : Audit := .cycle 1 12 true (1)
theorem kid22_part634_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part634) = true := by rfl

def kid22_part635 : Audit := .cycle 8 2 true (4)
theorem kid22_part635_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part635) = true := by rfl

def kid22_part636 : Audit := .cycle 9 1 true (5)
theorem kid22_part636_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part636) = true := by rfl

def kid22_part540 : Audit := .split 9 (5,false) (byMove [(kid22_part541),(kid22_part542),(kid22_part543),(kid22_part544),(kid22_part545),(kid22_part546),(kid22_part547),(kid22_part548),(kid22_part549),(kid22_part574),(kid22_part575),(kid22_part576),(kid22_part577),(kid22_part578),(kid22_part603),(kid22_part604),(kid22_part605),(kid22_part606),(kid22_part631),(kid22_part632),(kid22_part633),(kid22_part634),(kid22_part635),(kid22_part636)])

theorem kid22_part540_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (kid22_part540) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part541),(kid22_part542),(kid22_part543),(kid22_part544),(kid22_part545),(kid22_part546),(kid22_part547),(kid22_part548),(kid22_part549),(kid22_part574),(kid22_part575),(kid22_part576),(kid22_part577),(kid22_part578),(kid22_part603),(kid22_part604),(kid22_part605),(kid22_part606),(kid22_part631),(kid22_part632),(kid22_part633),(kid22_part634),(kid22_part635),(kid22_part636)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part541_checked

  · exact kid22_part547_checked

  · exact kid22_part577_checked

  · exact kid22_part631_checked

  · exact kid22_part542_checked

  · exact kid22_part548_checked

  · exact kid22_part578_checked

  · exact kid22_part632_checked

  · exact kid22_part543_checked

  · exact kid22_part549_checked

  · exact kid22_part603_checked

  · exact kid22_part633_checked

  · exact kid22_part544_checked

  · exact kid22_part574_checked

  · exact kid22_part604_checked

  · exact kid22_part634_checked

  · exact kid22_part545_checked

  · exact kid22_part575_checked

  · exact kid22_part605_checked

  · exact kid22_part635_checked

  · exact kid22_part546_checked

  · exact kid22_part576_checked

  · exact kid22_part606_checked

  · exact kid22_part636_checked

def kid22_part637 : Audit := .cycle 6 3 true (2)
theorem kid22_part637_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (kid22_part637) = true := by rfl

def kid22_part639 : Audit := .cycle 1 11 true (1)
theorem kid22_part639_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part639) = true := by rfl

def kid22_part640 : Audit := .cycle 7 4 true (3)
theorem kid22_part640_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part640) = true := by rfl

def kid22_part641 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (-2),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 21 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 16 (5,true),
.cycle 12 1 true (2),
.last 19 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 21 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 22 (5,true),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 38 1 false (10),
.cycle 21 1 false (3),
.cycle 11 3 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 29 9 false (2),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (5,true),
.cycle 38 1 false (10),
.cycle 11 4 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (3),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 16 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4)
]),
.cycle 6 12 true (2),
.cycle 21 5 false (1),
.cycle 0 14 true (0),
.cycle 19 1 false (1),
.cycle 22 1 false (-2),
.split 12 (5,false) (byMove [
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.last 18 (5,true),
.last 21 (5,true),
.last 14 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.last 13 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.last 21 (5,true),
.last 14 (5,true),
.cycle 1 13 true (1),
.last 18 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 18 (5,true),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 11 4 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 26 1 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4)
])
])
theorem kid22_part641_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part641) = true := by rfl

def kid22_part642 : Audit := .cycle 0 12 true (0)
theorem kid22_part642_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part642) = true := by rfl

def kid22_part643 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 19 8 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 16 4 false (0),
.split 15 (5,true) (byMove [
.cycle 0 32 true (0),
.cycle 16 15 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 30 1 false (2),
.cycle 29 1 false (1),
.cycle 12 4 true (1),
.last 16 (5,false),
.cycle 20 11 false (2),
.cycle 20 3 false (-1),
.last 17 (5,false),
.cycle 33 1 false (1),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 19 8 false (1),
.last 16 (5,false)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (1),
.cycle 3 12 true (1),
.cycle 12 3 true (1),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 19 8 false (1),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 32 true (0),
.cycle 9 12 true (1),
.cycle 12 4 true (1),
.cycle 15 1 true (3),
.cycle 21 12 false (3),
.cycle 13 3 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 19 8 false (1),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 23 12 false (1),
.cycle 15 1 true (3)
]),
.cycle 21 9 false (1),
.cycle 17 6 false (1),
.cycle 18 18 true (-1),
.cycle 1 16 true (1),
.cycle 16 4 false (0),
.split 15 (5,true) (byMove [
.cycle 13 8 true (0),
.cycle 7 25 false (4),
.last 17 (5,false),
.cycle 28 1 false (-2),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 1 16 true (1),
.cycle 21 9 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 20 5 false (0),
.last 17 (5,false),
.cycle 18 9 false (2),
.cycle 20 3 false (-1),
.last 17 (5,false),
.cycle 27 1 false (-1),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 1 16 true (1),
.cycle 20 10 false (2),
.cycle 14 2 true (1),
.cycle 0 17 true (0),
.cycle 17 6 false (1),
.last 17 (5,false)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 18 8 false (2),
.split 15 (5,false) (byMove [
.cycle 1 16 true (1),
.cycle 20 10 false (2),
.cycle 14 2 true (2),
.cycle 0 17 true (0),
.cycle 17 6 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 9 13 true (1),
.cycle 3 13 true (1),
.cycle 12 4 true (1),
.cycle 15 1 true (3),
.cycle 25 14 false (1),
.cycle 18 8 false (2),
.last 17 (5,true),
.cycle 1 17 true (1),
.cycle 17 6 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 19 10 false (3),
.cycle 15 1 true (3)
])
])
theorem kid22_part643_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part643) = true := by rfl

def kid22_part645 : Audit := .cycle 0 12 true (0)
theorem kid22_part645_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part645) = true := by rfl

def kid22_part646 : Audit := .cycle 1 11 true (1)
theorem kid22_part646_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part646) = true := by rfl

def kid22_part647 : Audit := .cycle 22 1 false (2)
theorem kid22_part647_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part647) = true := by rfl

def kid22_part648 : Audit := .cycle 21 1 false (1)
theorem kid22_part648_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part648) = true := by rfl

def kid22_part649 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.last 21 (5,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 21 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (1),
.cycle 3 12 true (1),
.cycle 12 3 true (1),
.last 15 (5,false),
.cycle 21 9 false (1),
.last 19 (5,false),
.cycle 18 18 true (-1),
.cycle 1 16 true (1),
.last 21 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 29 (5,false),
.last 15 (5,false)
])
theorem kid22_part649_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part649) = true := by rfl

def kid22_part650 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 15 (2,true),
.cycle 12 1 true (2),
.cycle 19 8 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 22 5 false (0),
.cycle 12 1 true (2)
])
theorem kid22_part650_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part650) = true := by rfl

def kid22_part651 : Audit := .cycle 0 12 true (0)
theorem kid22_part651_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part651) = true := by rfl

def kid22_part652 : Audit := .cycle 1 11 true (1)
theorem kid22_part652_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part652) = true := by rfl

def kid22_part653 : Audit := .cycle 38 1 false (10)
theorem kid22_part653_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part653) = true := by rfl

def kid22_part654 : Audit := .cycle 21 1 false (3)
theorem kid22_part654_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part654) = true := by rfl

def kid22_part655 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 30 1 false (2),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 16 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.last 15 (5,false)
])
theorem kid22_part655_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part655) = true := by rfl

def kid22_part656 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 15 (2,true),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (2,true),
.cycle 38 1 false (10),
.last 15 (2,true),
.cycle 12 1 true (4),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 15 (2,true),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4)
])
theorem kid22_part656_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part656) = true := by rfl

def kid22_part657 : Audit := .cycle 6 12 true (2)
theorem kid22_part657_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part657) = true := by rfl

def kid22_part658 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 26 7 false (1),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 20 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (2),
.cycle 3 11 true (1),
.cycle 12 3 true (2),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 22 5 false (1),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 15 (5,false),
.cycle 20 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 27 9 false (2),
.last 14 (5,false)
])
theorem kid22_part658_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part658) = true := by rfl

def kid22_part659 : Audit := .cycle 0 14 true (0)
theorem kid22_part659_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part659) = true := by rfl

def kid22_part660 : Audit := .cycle 19 1 false (1)
theorem kid22_part660_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part660) = true := by rfl

def kid22_part661 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.last 21 (5,false),
.cycle 18 1 false (0),
.last 23 (5,false),
.last 21 (5,false),
.last 17 (5,false),
.cycle 1 15 true (1),
.last 25 (5,false),
.cycle 0 32 true (0),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 21 (5,false),
.cycle 20 7 false (1),
.last 19 (5,false),
.cycle 20 12 true (-1),
.cycle 5 10 true (1),
.last 21 (5,false),
.last 17 (5,false),
.cycle 1 15 true (1),
.last 23 (5,false),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 25 (5,false),
.last 19 (5,false)
])
theorem kid22_part661_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part661) = true := by rfl

def kid22_part662 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.last 17 (2,true),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 17 (2,true),
.cycle 11 2 true (2),
.cycle 17 6 false (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.cycle 23 5 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 17 3 false (1)
])
theorem kid22_part662_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part662) = true := by rfl

def kid22_part663 : Audit := .cycle 0 12 true (0)
theorem kid22_part663_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part663) = true := by rfl

def kid22_part664 : Audit := .cycle 1 11 true (1)
theorem kid22_part664_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part664) = true := by rfl

def kid22_part665 : Audit := .cycle 2 10 true (1)
theorem kid22_part665_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part665) = true := by rfl

def kid22_part666 : Audit := .cycle 1 14 true (1)
theorem kid22_part666_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part666) = true := by rfl

def kid22_part667 : Audit := .cycle 8 4 true (3)
theorem kid22_part667_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part667) = true := by rfl

def kid22_part668 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 24 (2,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.last 15 (2,true),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4)
])
theorem kid22_part668_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part668) = true := by rfl

def kid22_part644 : Audit := .split 11 (5,true) (byMove [(kid22_part645),(kid22_part646),(kid22_part647),(kid22_part648),(kid22_part649),(kid22_part650),(kid22_part651),(kid22_part652),(kid22_part653),(kid22_part654),(kid22_part655),(kid22_part656),(kid22_part657),(kid22_part658),(kid22_part659),(kid22_part660),(kid22_part661),(kid22_part662),(kid22_part663),(kid22_part664),(kid22_part665),(kid22_part666),(kid22_part667),(kid22_part668)])

theorem kid22_part644_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part644) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part645),(kid22_part646),(kid22_part647),(kid22_part648),(kid22_part649),(kid22_part650),(kid22_part651),(kid22_part652),(kid22_part653),(kid22_part654),(kid22_part655),(kid22_part656),(kid22_part657),(kid22_part658),(kid22_part659),(kid22_part660),(kid22_part661),(kid22_part662),(kid22_part663),(kid22_part664),(kid22_part665),(kid22_part666),(kid22_part667),(kid22_part668)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part645_checked

  · exact kid22_part651_checked

  · exact kid22_part657_checked

  · exact kid22_part663_checked

  · exact kid22_part646_checked

  · exact kid22_part652_checked

  · exact kid22_part658_checked

  · exact kid22_part664_checked

  · exact kid22_part647_checked

  · exact kid22_part653_checked

  · exact kid22_part659_checked

  · exact kid22_part665_checked

  · exact kid22_part648_checked

  · exact kid22_part654_checked

  · exact kid22_part660_checked

  · exact kid22_part666_checked

  · exact kid22_part649_checked

  · exact kid22_part655_checked

  · exact kid22_part661_checked

  · exact kid22_part667_checked

  · exact kid22_part650_checked

  · exact kid22_part656_checked

  · exact kid22_part662_checked

  · exact kid22_part668_checked

def kid22_part669 : Audit := .cycle 0 11 true (0)
theorem kid22_part669_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part669) = true := by rfl

def kid22_part670 : Audit := .cycle 1 10 true (1)
theorem kid22_part670_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part670) = true := by rfl

def kid22_part671 : Audit := .cycle 9 8 true (3)
theorem kid22_part671_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part671) = true := by rfl

def kid22_part672 : Audit := .cycle 3 8 true (1)
theorem kid22_part672_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part672) = true := by rfl

def kid22_part673 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 30 1 false (2),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 25 4 false (1),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 11 4 true (4),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.last 16 (5,false),
.cycle 1 16 true (1),
.cycle 21 8 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.last 15 (5,false)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.cycle 11 3 true (4),
.split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 14 true (4),
.cycle 9 11 true (3),
.cycle 11 4 true (4),
.cycle 14 1 true (6),
.cycle 7 9 true (3),
.cycle 12 3 true (4),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 10 8 true (4),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 14 1 true (6)
]),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.cycle 5 12 true (1),
.cycle 1 15 true (1),
.cycle 10 5 true (4),
.split 14 (5,true) (byMove [
.cycle 12 8 true (3),
.cycle 0 27 true (0),
.last 16 (5,false),
.cycle 7 10 true (3),
.cycle 25 4 false (1),
.last 16 (5,false),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 10 5 true (4),
.last 16 (5,false),
.cycle 9 7 true (3),
.far true 1 ⟨0,[0, 0],[0, 2, 10, 8, 2, 64, 64],[2, 0, 32, 2, 2, 2, 64],96⟩,
.last 16 (5,false),
.cycle 5 10 true (1),
.cycle 37 4 false (7),
.last 16 (5,false),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 13 2 true (4),
.cycle 0 16 true (0),
.cycle 10 5 true (4),
.last 16 (5,false)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 13 2 true (5),
.cycle 0 16 true (0),
.cycle 10 5 true (4),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 11 4 true (4),
.cycle 14 1 true (6),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 10 6 true (4),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 14 1 true (6)
])
])
theorem kid22_part673_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part673) = true := by rfl

def kid22_part674 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.last 16 (2,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (2,true),
.cycle 33 1 false (5),
.last 16 (2,true),
.cycle 19 1 false (1),
.cycle 6 16 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.last 16 (2,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 12 2 true (3)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 8 14 true (3),
.cycle 9 20 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (3),
.cycle 9 18 true (3),
.last 24 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1056, 4096, 4, 128, 256, 8, 2, 32, 4, 4096],[2, 1024, 4096, 1, 32, 32, 2, 1024, 4096, 1, 32, 32, 4096],4112⟩,
.cycle 7 16 true (3),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.cycle 19 4 true (5),
.last 23 (2,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 8 14 true (3),
.cycle 9 20 true (3)
]),
.cycle 9 8 true (3),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 10 5 true (4),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 12 3 true (5),
.cycle 11 4 true (5),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5)
]),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 30 1 false (2),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.cycle 12 3 true (4),
.cycle 11 3 true (4),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.cycle 5 12 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 6 true (3)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 8 8 true (3),
.last 22 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 10 true (3),
.cycle 9 12 true (3),
.last 18 (2,true),
.last 19 (2,true),
.cycle 7 10 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 12 4 true (3),
.last 22 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 8 8 true (3),
.cycle 14 3 true (4)
]),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 34 1 false (4),
.last 27 (2,true),
.last 16 (2,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 18 (2,true),
.cycle 29 1 false (7),
.cycle 15 12 true (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 29 1 false (3),
.last 16 (2,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 14 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part674_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part674) = true := by rfl

def kid22_part675 : Audit := .cycle 6 5 true (2)
theorem kid22_part675_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part675) = true := by rfl

def kid22_part676 : Audit := .cycle 9 2 true (3)
theorem kid22_part676_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part676) = true := by rfl

def kid22_part677 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 13 11 false (2),
.split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 21 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 16 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 21 (5,true),
.cycle 22 1 false (0),
.last 21 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 22 (5,true),
.last 14 (5,true)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 30 1 false (8),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (5,false),
.cycle 38 1 false (10),
.last 16 (5,false),
.last 13 (5,false),
.cycle 7 7 true (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 29 9 false (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
]),
.cycle 9 8 true (2),
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.cycle 19 1 false (1),
.cycle 15 10 true (-3),
.split 12 (5,false) (byMove [
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.last 18 (5,true),
.last 21 (5,true),
.last 14 (5,true),
.cycle 6 7 true (2),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.last 13 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.last 21 (5,true),
.last 14 (5,true),
.cycle 6 7 true (2),
.last 16 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.last 13 (5,true)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
])
theorem kid22_part677_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part677) = true := by rfl

def kid22_part678 : Audit := .cycle 1 12 true (1)
theorem kid22_part678_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part678) = true := by rfl

def kid22_part679 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 19 8 false (1),
.cycle 18 1 false (0),
.cycle 23 9 false (1),
.cycle 16 4 false (0),
.split 15 (5,true) (byMove [
.cycle 17 20 true (1),
.cycle 18 13 false (1),
.last 17 (5,false),
.cycle 0 27 true (0),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 23 9 false (1),
.cycle 1 21 true (1),
.cycle 1 18 true (1),
.cycle 27 1 false (1),
.cycle 12 4 true (1),
.last 16 (5,false),
.cycle 20 11 false (2),
.cycle 20 3 false (-1),
.last 17 (5,false),
.cycle 21 1 false (1),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 19 10 false (3),
.cycle 1 21 true (1),
.cycle 1 18 true (1),
.cycle 9 10 true (1),
.cycle 19 8 false (1),
.last 16 (5,false)
]),
.cycle 6 9 true (1),
.cycle 21 10 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 1 16 true (1),
.cycle 19 8 false (1),
.split 15 (5,true) (byMove [
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 9 12 true (1),
.last 21 (5,false),
.cycle 19 8 false (1),
.last 16 (5,false),
.cycle 1 16 true (1),
.cycle 7 9 true (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.last 24 (5,false),
.last 17 (5,false),
.cycle 19 10 false (3),
.last 21 (5,false),
.cycle 1 18 true (1),
.cycle 9 10 true (1),
.cycle 19 8 false (1),
.last 16 (5,false),
.cycle 1 16 true (1),
.cycle 25 12 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 21 10 false (1),
.last 17 (5,false)
]),
.cycle 20 7 false (1),
.cycle 17 6 false (1),
.cycle 15 10 true (-1),
.cycle 9 8 true (1),
.cycle 16 4 false (0),
.split 15 (5,true) (byMove [
.cycle 13 8 true (0),
.cycle 51 13 true (0),
.last 17 (5,false),
.cycle 26 1 false (-2),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 9 8 true (1),
.cycle 20 7 false (1),
.last 17 (5,false),
.cycle 5 11 true (1),
.cycle 20 5 false (0),
.last 19 (5,false),
.cycle 18 9 false (2),
.cycle 20 3 false (-1),
.last 17 (5,false),
.cycle 25 1 false (-1),
.cycle 17 4 false (-1),
.last 17 (5,false),
.cycle 23 12 false (1),
.cycle 18 8 false (2),
.cycle 14 2 true (1),
.cycle 5 11 true (1),
.cycle 17 6 false (1),
.last 19 (5,false)
]),
.cycle 24 12 false (2),
.cycle 17 8 false (3),
.cycle 2 15 true (1),
.cycle 1 16 true (1),
.cycle 16 6 false (2),
.split 15 (5,true) (byMove [
.last 19 (5,false),
.cycle 20 10 false (2),
.last 17 (5,false),
.cycle 27 14 false (2),
.cycle 17 6 false (1),
.last 19 (5,false),
.cycle 1 16 true (1),
.cycle 24 12 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 20 10 false (2),
.last 17 (5,false),
.cycle 23 12 false (1),
.cycle 18 8 false (2),
.cycle 14 2 true (2),
.cycle 5 11 true (1),
.cycle 17 6 false (1),
.last 19 (5,false),
.cycle 1 16 true (1),
.cycle 20 10 false (4),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 17 8 false (3),
.last 17 (5,false)
])
])
theorem kid22_part679_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part679) = true := by rfl

def kid22_part681 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 16 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 26 (5,false),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (2),
.cycle 3 12 true (1),
.cycle 13 3 true (3),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 9 12 true (2),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 26 (5,false),
.cycle 11 8 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 7 true (3),
.last 15 (5,false)
])
theorem kid22_part681_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part681) = true := by rfl

def kid22_part682 : Audit := .cycle 0 15 true (0)
theorem kid22_part682_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part682) = true := by rfl

def kid22_part683 : Audit := .cycle 22 1 false (2)
theorem kid22_part683_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part683) = true := by rfl

def kid22_part684 : Audit := .cycle 21 1 false (1)
theorem kid22_part684_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part684) = true := by rfl

def kid22_part685 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.last 21 (5,false),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.last 21 (5,false),
.last 17 (5,false),
.last 22 (5,false),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.last 19 (5,false),
.last 15 (5,false),
.cycle 21 9 false (1),
.last 19 (5,false),
.cycle 36 24 true (1),
.cycle 1 20 true (1),
.last 21 (5,false),
.last 17 (5,false),
.last 37 (5,false),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 29 (5,false),
.last 15 (5,false)
])
theorem kid22_part685_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part685) = true := by rfl

def kid22_part686 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 20 (2,true),
.cycle 15 1 false (-1),
.last 23 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 15 (2,true),
.cycle 15 1 true (3),
.cycle 19 8 false (1),
.last 14 (2,true),
.last 27 (2,true),
.cycle 22 1 false (0),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 0 26 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 22 5 false (0),
.cycle 17 1 true (1)
])
theorem kid22_part686_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part686) = true := by rfl

def kid22_part687 : Audit := .cycle 1 12 true (1)
theorem kid22_part687_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part687) = true := by rfl

def kid22_part688 : Audit := .cycle 7 5 true (3)
theorem kid22_part688_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part688) = true := by rfl

def kid22_part689 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (8),
.cycle 38 1 false (10),
.cycle 12 3 true (4),
.last 13 (5,false),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
theorem kid22_part689_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part689) = true := by rfl

def kid22_part690 : Audit := .cycle 0 13 true (0)
theorem kid22_part690_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part690) = true := by rfl

def kid22_part691 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.last 17 (2,true),
.cycle 9 12 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.last 16 (2,true),
.cycle 18 1 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (3),
.last 17 (2,true)
])
theorem kid22_part691_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part691) = true := by rfl

def kid22_part692 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 30 1 false (6),
.cycle 26 1 false (4),
.last 16 (2,true),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 34 1 false (10),
.cycle 30 1 false (8),
.last 16 (2,true),
.cycle 13 1 true (5),
.cycle 7 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 27 1 false (5),
.last 16 (2,true),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part692_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part692) = true := by rfl

def kid22_part693 : Audit := .cycle 9 8 true (2)
theorem kid22_part693_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part693) = true := by rfl

def kid22_part694 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 26 7 false (1),
.cycle 29 1 false (1),
.cycle 18 10 true (2),
.last 15 (5,false),
.cycle 20 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 2, 64, 64],[0, 2, 8, 0, 32, 2, 64],96⟩,
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false),
.cycle 9 6 true (2),
.cycle 22 5 false (1),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.last 15 (5,false),
.cycle 20 3 false (0),
.cycle 1 14 true (1),
.cycle 30 11 false (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 24 7 false (2),
.cycle 26 9 false (2)
])
theorem kid22_part694_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part694) = true := by rfl

def kid22_part695 : Audit := .cycle 1 14 true (1)
theorem kid22_part695_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part695) = true := by rfl

def kid22_part696 : Audit := .cycle 19 1 false (1)
theorem kid22_part696_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part696) = true := by rfl

def kid22_part697 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (1),
.last 21 (5,false),
.cycle 18 1 false (0),
.last 21 (5,false),
.last 21 (5,false),
.last 17 (5,false),
.cycle 6 9 true (1),
.last 23 (5,false),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 3, 2, 3],[128, 256, 8, 4, 16384, 16777216, 524288, 1048576, 32768, 2, 4, 16777216, 524288, 1048576, 8, 1024, 16384, 16777216, 524288, 1048576, 32768, 2, 16777220, 16777216, 16777216],[2, 1024, 4, 1, 16777216, 4, 8192, 4194304, 16384, 4096, 4, 16777216, 2, 4194304, 4, 1, 16777216, 16777220, 8192, 4194304, 16384, 4096, 16777220, 16777220, 16777216],29493280⟩,
.cycle 1 16 true (1),
.last 16 (5,false),
.last 21 (5,false),
.cycle 20 7 false (1),
.last 19 (5,false),
.cycle 15 10 true (-1),
.cycle 9 8 true (1),
.last 21 (5,false),
.last 17 (5,false),
.last 39 (5,false),
.last 21 (5,false),
.cycle 2 15 true (1),
.cycle 1 16 true (1),
.last 25 (5,false),
.last 19 (5,false)
])
theorem kid22_part697_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part697) = true := by rfl

def kid22_part698 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.last 17 (2,true),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 12 2 true (2),
.cycle 11 2 true (2),
.cycle 17 6 false (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.last 20 (2,true),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 21 5 false (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 3 false (0),
.cycle 17 3 false (1)
])
theorem kid22_part698_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part698) = true := by rfl

def kid22_part699 : Audit := .cycle 1 12 true (1)
theorem kid22_part699_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part699) = true := by rfl

def kid22_part700 : Audit := .cycle 7 5 true (3)
theorem kid22_part700_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part700) = true := by rfl

def kid22_part701 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 26 1 false (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 12 3 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
theorem kid22_part701_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part701) = true := by rfl

def kid22_part702 : Audit := .cycle 0 13 true (0)
theorem kid22_part702_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part702) = true := by rfl

def kid22_part703 : Audit := .cycle 10 2 true (3)
theorem kid22_part703_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part703) = true := by rfl

def kid22_part704 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (3),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.last 16 (2,true),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 11 5 true (3),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part704_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part704) = true := by rfl

def kid22_part680 : Audit := .split 11 (5,true) (byMove [(kid22_part681),(kid22_part682),(kid22_part683),(kid22_part684),(kid22_part685),(kid22_part686),(kid22_part687),(kid22_part688),(kid22_part689),(kid22_part690),(kid22_part691),(kid22_part692),(kid22_part693),(kid22_part694),(kid22_part695),(kid22_part696),(kid22_part697),(kid22_part698),(kid22_part699),(kid22_part700),(kid22_part701),(kid22_part702),(kid22_part703),(kid22_part704)])

theorem kid22_part680_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part680) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part681),(kid22_part682),(kid22_part683),(kid22_part684),(kid22_part685),(kid22_part686),(kid22_part687),(kid22_part688),(kid22_part689),(kid22_part690),(kid22_part691),(kid22_part692),(kid22_part693),(kid22_part694),(kid22_part695),(kid22_part696),(kid22_part697),(kid22_part698),(kid22_part699),(kid22_part700),(kid22_part701),(kid22_part702),(kid22_part703),(kid22_part704)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part681_checked

  · exact kid22_part687_checked

  · exact kid22_part693_checked

  · exact kid22_part699_checked

  · exact kid22_part682_checked

  · exact kid22_part688_checked

  · exact kid22_part694_checked

  · exact kid22_part700_checked

  · exact kid22_part683_checked

  · exact kid22_part689_checked

  · exact kid22_part695_checked

  · exact kid22_part701_checked

  · exact kid22_part684_checked

  · exact kid22_part690_checked

  · exact kid22_part696_checked

  · exact kid22_part702_checked

  · exact kid22_part685_checked

  · exact kid22_part691_checked

  · exact kid22_part697_checked

  · exact kid22_part703_checked

  · exact kid22_part686_checked

  · exact kid22_part692_checked

  · exact kid22_part698_checked

  · exact kid22_part704_checked

def kid22_part705 : Audit := .cycle 0 11 true (0)
theorem kid22_part705_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part705) = true := by rfl

def kid22_part706 : Audit := .cycle 1 10 true (1)
theorem kid22_part706_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part706) = true := by rfl

def kid22_part707 : Audit := .cycle 2 9 true (1)
theorem kid22_part707_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part707) = true := by rfl

def kid22_part708 : Audit := .cycle 1 13 true (1)
theorem kid22_part708_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part708) = true := by rfl

def kid22_part709 : Audit := .cycle 8 3 true (3)
theorem kid22_part709_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part709) = true := by rfl

def kid22_part710 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 26 1 false (2),
.cycle 0 14 true (0),
.cycle 21 6 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.cycle 12 3 true (4),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 11 2 true (4)
]),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 18 (2,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 10 true (3),
.cycle 3 10 true (1),
.last 15 (2,true),
.cycle 21 1 false (1),
.cycle 6 7 true (2),
.cycle 9 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 12 2 true (3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 11 2 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 9 true (3),
.cycle 3 9 true (1),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 34 1 false (2),
.cycle 0 16 true (0),
.cycle 10 5 true (4),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 12 true (3),
.cycle 3 12 true (1),
.cycle 12 3 true (5),
.cycle 11 4 true (5),
.cycle 6 9 true (2),
.cycle 9 6 true (3),
.cycle 9 12 true (2),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5)
]),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 9 3 true (3),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 17 (5,true),
.cycle 26 1 false (2),
.cycle 7 8 true (3),
.cycle 21 6 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.last 13 (5,true),
.cycle 9 5 true (3),
.last 15 (5,true),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.last 13 (5,true)
]),
.cycle 1 13 true (1),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.last 26 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 9 11 true (3),
.cycle 3 11 true (1),
.last 16 (2,true),
.cycle 12 5 true (4),
.cycle 6 8 true (2),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.last 26 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (4)
]),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 7 11 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.last 18 (2,true),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 36 1 false (8),
.cycle 9 5 true (3),
.cycle 9 7 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 12 2 true (3),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part710_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part710) = true := by rfl

def kid22_part638 : Audit := .split 10 (4,true) (byMove [(kid22_part639),(kid22_part640),(kid22_part641),(kid22_part642),(kid22_part643),(kid22_part644),(kid22_part669),(kid22_part670),(kid22_part671),(kid22_part672),(kid22_part673),(kid22_part674),(kid22_part675),(kid22_part676),(kid22_part677),(kid22_part678),(kid22_part679),(kid22_part680),(kid22_part705),(kid22_part706),(kid22_part707),(kid22_part708),(kid22_part709),(kid22_part710)])

theorem kid22_part638_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (kid22_part638) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some mv)) (byMove [(kid22_part639),(kid22_part640),(kid22_part641),(kid22_part642),(kid22_part643),(kid22_part644),(kid22_part669),(kid22_part670),(kid22_part671),(kid22_part672),(kid22_part673),(kid22_part674),(kid22_part675),(kid22_part676),(kid22_part677),(kid22_part678),(kid22_part679),(kid22_part680),(kid22_part705),(kid22_part706),(kid22_part707),(kid22_part708),(kid22_part709),(kid22_part710)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part639_checked

  · exact kid22_part669_checked

  · exact kid22_part675_checked

  · exact kid22_part705_checked

  · exact kid22_part640_checked

  · exact kid22_part670_checked

  · exact kid22_part676_checked

  · exact kid22_part706_checked

  · exact kid22_part641_checked

  · exact kid22_part671_checked

  · exact kid22_part677_checked

  · exact kid22_part707_checked

  · exact kid22_part642_checked

  · exact kid22_part672_checked

  · exact kid22_part678_checked

  · exact kid22_part708_checked

  · exact kid22_part643_checked

  · exact kid22_part673_checked

  · exact kid22_part679_checked

  · exact kid22_part709_checked

  · exact kid22_part644_checked

  · exact kid22_part674_checked

  · exact kid22_part680_checked

  · exact kid22_part710_checked

def kid22_part712 : Audit := .cycle 1 13 true (1)
theorem kid22_part712_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part712) = true := by rfl

def kid22_part713 : Audit := .cycle 0 13 true (0)
theorem kid22_part713_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part713) = true := by rfl

def kid22_part714 : Audit := .split 17 (4,true) (byMove [
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 25 1 false (3),
.cycle 28 1 false (2),
.split 18 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 28 1 false (2),
.last 19 (5,false),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 33 1 false (7),
.last 19 (5,false),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 27 1 false (3),
.cycle 19 1 false (1),
.cycle 27 1 false (3),
.last 19 (5,false),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 19 (5,false)
]),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.cycle 28 1 false (4),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.last 19 (5,false),
.cycle 0 19 true (0),
.last 41 (5,false),
.cycle 11 10 true (0),
.last 26 (5,false),
.cycle 0 22 true (0),
.last 19 (5,false),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 48 1 false (6),
.cycle 5 38 true (0),
.last 28 (5,false),
.last 19 (5,false)
]),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 34 1 false (4),
.split 18 (5,true) (byMove [
.cycle 25 1 false (1),
.cycle 14 32 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 27 (5,false),
.last 19 (5,false),
.cycle 24 1 false (4),
.cycle 26 1 false (4),
.cycle 21 1 false (3),
.cycle 31 1 false (7),
.last 20 (5,false),
.last 21 (5,false),
.cycle 15 8 true (1),
.cycle 23 1 false (1),
.cycle 26 1 false (4),
.cycle 19 1 false (1),
.cycle 34 1 false (4),
.last 19 (5,false),
.cycle 27 24 true (3),
.cycle 28 1 false (2),
.cycle 22 1 false (2),
.cycle 0 47 true (0),
.cycle 17 2 true (2),
.last 21 (5,false)
]),
.cycle 0 48 true (0),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 24 1 false (2),
.split 18 (5,true) (byMove [
.cycle 52 1 false (6),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.last 20 (5,false),
.last 21 (5,false),
.cycle 0 19 true (0),
.last 48 (5,false),
.last 27 (5,false),
.cycle 3 16 true (0),
.cycle 0 22 true (0),
.last 19 (5,false),
.last 30 (5,false),
.last 21 (5,false),
.cycle 22 1 false (2),
.last 45 (5,false),
.cycle 17 2 true (3),
.last 21 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 24 1 false (2),
.last 19 (5,false)
])
])
theorem kid22_part714_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part714) = true := by rfl

def kid22_part715 : Audit := .cycle 17 1 false (1)
theorem kid22_part715_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part715) = true := by rfl

def kid22_part716 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 7 19 true (1),
.cycle 0 34 true (0),
.cycle 33 1 false (1),
.cycle 0 29 true (0),
.split 18 (5,false) (byMove [
.last 28 (5,true),
.last 34 (5,true),
.cycle 37 1 false (1),
.last 30 (5,true),
.last 41 (5,true),
.last 20 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.last 28 (5,true),
.last 26 (5,true),
.cycle 10 9 true (1),
.last 21 (5,true),
.last 24 (5,true),
.last 22 (5,true),
.last 25 (5,true),
.cycle 34 1 false (0),
.last 27 (5,true),
.last 20 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.last 26 (5,true),
.cycle 1 28 true (1),
.cycle 21 11 false (2),
.last 21 (5,true)
]),
.cycle 13 5 true (3),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 0 61 true (0),
.cycle 1 21 true (1),
.split 18 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 22 true (0),
.last 28 (5,true),
.cycle 34 1 false (4),
.cycle 10 9 true (1),
.last 22 (5,true),
.cycle 1 19 true (1),
.cycle 7 12 true (1),
.cycle 0 23 true (0),
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 19 (5,true),
.cycle 13 10 true (3),
.cycle 16 4 true (3),
.cycle 1 21 true (1),
.last 26 (5,true),
.cycle 5 16 true (1),
.last 22 (5,true),
.cycle 1 19 true (1),
.cycle 14 5 true (3),
.cycle 2 20 true (1),
.cycle 0 20 true (0),
.last 35 (5,true),
.last 19 (5,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 31, 64, 64],[2, 16, 31, 1, 16, 64, 64],96⟩,
.cycle 23 2 true (0),
.cycle 11 7 true (1),
.cycle 29 1 false (3),
.cycle 1 28 true (1),
.split 18 (5,false) (byMove [
.last 23 (5,true),
.cycle 11 9 true (1),
.last 26 (5,true),
.cycle 26 1 false (0),
.cycle 21 9 false (2),
.last 20 (5,true),
.cycle 1 24 true (1),
.last 28 (5,true),
.last 27 (5,true),
.cycle 12 7 true (2),
.cycle 17 2 true (2),
.last 19 (5,true),
.last 22 (5,true),
.last 22 (5,true),
.cycle 1 28 true (1),
.last 24 (5,true),
.last 27 (5,true),
.last 20 (5,true),
.cycle 1 24 true (1),
.last 28 (5,true),
.last 24 (5,true),
.cycle 12 7 true (2),
.last 20 (5,true),
.last 19 (5,true)
]),
.cycle 13 5 true (3),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 31, 64, 64],[2, 16, 31, 1, 16, 64, 64],96⟩,
.split 18 (5,false) (byMove [
.cycle 1 24 true (1),
.last 48 (5,true),
.cycle 0 35 true (0),
.cycle 12 7 true (2),
.cycle 17 2 true (3),
.last 19 (5,true),
.cycle 1 19 true (1),
.cycle 1 35 true (1),
.cycle 8 12 true (1),
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 19 (5,true),
.last 41 (5,true),
.last 21 (5,true),
.last 40 (5,true),
.cycle 5 14 true (1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 1 19 true (1),
.cycle 14 5 true (3),
.cycle 2 20 true (1),
.cycle 0 20 true (0),
.cycle 15 6 true (3),
.last 19 (5,true)
])
])
theorem kid22_part716_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part716) = true := by rfl

def kid22_part718 : Audit := .cycle 0 15 true (0)
theorem kid22_part718_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part718) = true := by rfl

def kid22_part719 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (1),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 0 23 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 13 8 true (1),
.cycle 3 16 true (1),
.cycle 0 22 true (0),
.cycle 1 19 true (1),
.cycle 6 13 true (1),
.cycle 17 2 true (3),
.cycle 9 10 true (1),
.cycle 1 20 true (1),
.cycle 5 17 true (1),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 21 (5,true),
.last 23 (5,true)
])
theorem kid22_part719_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part719) = true := by rfl

def kid22_part720 : Audit := .cycle 21 1 false (1)
theorem kid22_part720_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part720) = true := by rfl

def kid22_part721 : Audit := .cycle 0 17 true (0)
theorem kid22_part721_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part721) = true := by rfl

def kid22_part722 : Audit := .split 20 (5,true) (byMove [
.cycle 87 18 true (5),
.cycle 11 11 false (1),
.cycle 0 26 false (4),
.last 30 (4,true),
.last 21 (4,true),
.cycle 0 26 false (4),
.last 54 (4,true),
.last 28 (4,true),
.last 28 (4,true),
.last 56 (4,true),
.far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 3, 3],[128, 256, 8, 16777216, 1, 128, 128, 256, 32768, 2, 3, 16777216, 524288, 1048576, 8, 1024, 1, 384, 524288, 1048576, 2097152, 21496834, 24937859, 24937859, 16777216],[2, 1024, 33024, 1, 16777216, 16, 8192, 1024, 1, 4096, 16777216, 65536, 2, 4194304, 16777216, 1, 16777216, 16, 524288, 4194304, 24937859, 262144, 16777216, 4194304, 16777216],33323020⟩,
.cycle 10 11 false (2),
.cycle 11 12 true (-3),
.last 22 (4,true),
.cycle 12 9 false (1),
.last 30 (4,true),
.last 21 (4,true),
.last 28 (4,true),
.last 54 (4,true),
.last 28 (4,true),
.cycle 2 19 false (4),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 1, 128, 524288, 1048576, 32768, 33554434, 50331648, 281474976710656, 524288, 1048576, 134217728, 1024, 16777216, 384, 137438953472, 274877906944, 8589934592, 33554432, 281474976711680, 281474976710656, 128, 256, 134217728, 281474976710656, 16777216, 128, 137438953472, 274877906944, 549755813888, 1024, 68719476736, 281475027042304, 137438953472, 274877906944, 35184372088832, 290408508686336, 331442681841026, 281612415664128, 137438953472, 274877906944, 549755813888, 282574488338432, 68719476736, 331442681841026, 281474976710656],[2, 1024, 1048576, 1, 281474976710656, 512, 8192, 4194304, 33554434, 4096, 281474976710656, 2097152, 33554432, 4194304, 281474976710656, 16777216, 281474976710656, 2097152, 2147483648, 1099511627776, 33554432, 1073741824, 281474976710656, 549755813888, 33554432, 1024, 1081344, 16777216, 281474976710656, 512, 137438953472, 1099511627776, 281474976710656, 68719476736, 281474976710656, 549755813888, 8796093022208, 1099511627776, 331442681841026, 4398046511104, 281474976710656, 549755813888, 137438953472, 1099511627776, 281749854617600, 68719476736, 281474976710656, 549755813888, 281474976710656],562940504463424⟩,
.cycle 11 13 false (1),
.last 22 (4,true)
])
theorem kid22_part722_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part722) = true := by rfl

def kid22_part723 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 24 (4,true),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.last 20 (4,true),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 23 true (0),
.cycle 13 1 false (1),
.cycle 12 5 false (1),
.cycle 12 3 false (0),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.last 24 (4,true),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.last 20 (4,true),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part723_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part723) = true := by rfl

def kid22_part724 : Audit := .split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.last 23 (4,true),
.last 23 (4,true),
.cycle 29 1 false (1),
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 11 5 true (3),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.last 23 (4,true),
.cycle 1 19 true (1),
.cycle 1 17 true (1),
.last 33 (4,true),
.last 23 (4,true),
.cycle 11 7 true (2),
.last 21 (4,true),
.cycle 1 26 true (1),
.cycle 1 22 true (1),
.cycle 11 5 true (3),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 21 (4,true),
.cycle 1 17 true (1)
])
theorem kid22_part724_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part724) = true := by rfl

def kid22_part725 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 0 17 true (0),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 0 17 true (0),
.cycle 1 14 true (1),
.cycle 30 5 false (2),
.last 21 (4,true),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 1 17 true (1),
.cycle 7 8 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.cycle 1 14 true (1)
])
theorem kid22_part725_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part725) = true := by rfl

def kid22_part726 : Audit := .cycle 0 13 true (0)
theorem kid22_part726_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part726) = true := by rfl

def kid22_part727 : Audit := .split 17 (4,true) (byMove [
.last 21 (5,true),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.last 23 (5,true),
.last 25 (5,true),
.last 18 (5,true),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.cycle 28 1 false (4),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.last 18 (5,true),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 34 1 false (4),
.last 18 (5,true),
.cycle 0 48 true (0),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.last 21 (5,true),
.last 18 (5,true)
])
theorem kid22_part727_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part727) = true := by rfl

def kid22_part728 : Audit := .cycle 1 14 true (1)
theorem kid22_part728_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part728) = true := by rfl

def kid22_part729 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 0 16 true (0),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 0 16 true (0),
.cycle 13 1 true (5),
.last 37 (4,true),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 1 16 true (1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 13 1 true (5)
])
theorem kid22_part729_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part729) = true := by rfl

def kid22_part730 : Audit := .split 15 (5,true) (byMove [
.cycle 17 20 true (1),
.last 32 (4,true),
.cycle 24 1 false (-2),
.cycle 0 27 true (0),
.last 16 (4,true),
.cycle 16 6 false (0),
.last 18 (4,true),
.cycle 1 21 true (1),
.cycle 1 18 true (1),
.last 21 (4,true),
.cycle 5 13 true (1),
.last 19 (4,true),
.cycle 21 5 false (1),
.last 17 (4,true),
.last 27 (4,true),
.cycle 21 1 false (1),
.last 16 (4,true),
.last 20 (4,true),
.last 18 (4,true),
.cycle 1 21 true (1),
.cycle 1 18 true (1),
.last 20 (4,true),
.cycle 16 8 false (2),
.last 19 (4,true)
])
theorem kid22_part730_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part730) = true := by rfl

def kid22_part731 : Audit := .split 13 (5,true) (byMove [
.last 22 (4,true),
.cycle 14 13 false (1),
.cycle 20 1 false (-2),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 14 4 false (0),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 1 25 true (1),
.cycle 10 4 true (1),
.cycle 20 5 false (0),
.last 15 (4,true),
.cycle 11 11 false (2),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 14 4 false (0),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.last 20 (4,true),
.cycle 1 22 true (1),
.cycle 15 6 false (1),
.last 16 (4,true)
])
theorem kid22_part731_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part731) = true := by rfl

def kid22_part732 : Audit := .split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.last 25 (4,true),
.last 25 (4,true),
.cycle 33 1 false (1),
.last 25 (4,true),
.cycle 0 29 true (0),
.cycle 13 5 true (3),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.last 25 (4,true),
.cycle 1 21 true (1),
.cycle 1 21 true (1),
.last 37 (4,true),
.last 25 (4,true),
.cycle 11 7 true (1),
.last 23 (4,true),
.cycle 1 28 true (1),
.cycle 1 28 true (1),
.cycle 13 5 true (3),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 25 (4,true),
.last 25 (4,true)
])
theorem kid22_part732_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part732) = true := by rfl

def kid22_part733 : Audit := .cycle 18 1 false (0)
theorem kid22_part733_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part733) = true := by rfl

def kid22_part734 : Audit := .split 20 (5,true) (byMove [
.cycle 15 38 true (-3),
.last 28 (4,true),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 28 (4,true),
.last 111 (4,true),
.last 28 (4,true),
.cycle 55 17 true (5),
.cycle 0 30 true (-3),
.cycle 21 1 false (1),
.cycle 0 31 true (-3),
.cycle 40 22 true (1),
.cycle 19 5 false (1),
.cycle 18 3 false (1),
.last 32 (4,true),
.cycle 21 1 false (-1),
.cycle 71 21 true (5),
.cycle 11 16 true (-3),
.last 28 (4,true),
.cycle 1 56 true (-3),
.last 61 (4,true),
.cycle 35 20 true (1),
.cycle 11 10 true (-3),
.last 22 (4,true)
])
theorem kid22_part734_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part734) = true := by rfl

def kid22_part735 : Audit := .split 12 (5,true) (byMove [
.cycle 0 30 true (-1),
.last 39 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 14 (4,true),
.cycle 14 1 false (0),
.cycle 18 1 false (4),
.last 13 (4,true),
.cycle 15 1 false (3),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 21 5 true (2),
.last 14 (4,true),
.cycle 0 24 true (0),
.last 40 (4,true),
.last 13 (4,true),
.cycle 17 3 true (3)
])
theorem kid22_part735_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part735) = true := by rfl

def kid22_part736 : Audit := .split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.last 36 (4,true),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.last 16 (4,true),
.cycle 0 22 true (0),
.cycle 11 5 true (3),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.last 21 (4,true),
.cycle 1 19 true (1),
.cycle 1 17 true (1),
.last 23 (4,true),
.last 17 (4,true),
.last 36 (4,true),
.last 27 (4,true),
.last 16 (4,true),
.last 25 (4,true),
.cycle 11 5 true (3),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 24 (4,true),
.cycle 1 17 true (1)
])
theorem kid22_part736_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part736) = true := by rfl

def kid22_part737 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.last 32 (4,true),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 1 14 true (1),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 19 7 true (-1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 17 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 24 9 false (2),
.cycle 1 14 true (1)
])
theorem kid22_part737_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part737) = true := by rfl

def kid22_part738 : Audit := .cycle 0 13 true (0)
theorem kid22_part738_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part738) = true := by rfl

def kid22_part739 : Audit := .cycle 4 7 true (1)
theorem kid22_part739_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part739) = true := by rfl

def kid22_part740 : Audit := .split 16 (5,true) (byMove [
.last 41 (4,true),
.last 24 (4,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 24 (4,true),
.cycle 17 3 false (0),
.last 19 (4,true),
.cycle 33 3 false (7),
.cycle 21 3 false (5),
.cycle 17 1 false (1),
.last 22 (4,true),
.last 18 (4,true),
.cycle 14 5 false (2),
.cycle 15 3 false (1),
.last 21 (4,true),
.cycle 17 1 false (-1),
.cycle 49 3 false (7),
.last 18 (4,true),
.last 19 (4,true),
.cycle 1 25 true (0),
.last 37 (4,true),
.last 21 (4,true),
.cycle 17 3 false (1),
.last 18 (4,true)
])
theorem kid22_part740_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part740) = true := by rfl

def kid22_part741 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.last 24 (4,true),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 13 7 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 24 (4,true),
.cycle 13 1 true (5)
])
theorem kid22_part741_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part741) = true := by rfl

def kid22_part717 : Audit := .split 10 (5,false) (byMove [(kid22_part718),(kid22_part719),(kid22_part720),(kid22_part721),(kid22_part722),(kid22_part723),(kid22_part724),(kid22_part725),(kid22_part726),(kid22_part727),(kid22_part728),(kid22_part729),(kid22_part730),(kid22_part731),(kid22_part732),(kid22_part733),(kid22_part734),(kid22_part735),(kid22_part736),(kid22_part737),(kid22_part738),(kid22_part739),(kid22_part740),(kid22_part741)])

theorem kid22_part717_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part717) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part718),(kid22_part719),(kid22_part720),(kid22_part721),(kid22_part722),(kid22_part723),(kid22_part724),(kid22_part725),(kid22_part726),(kid22_part727),(kid22_part728),(kid22_part729),(kid22_part730),(kid22_part731),(kid22_part732),(kid22_part733),(kid22_part734),(kid22_part735),(kid22_part736),(kid22_part737),(kid22_part738),(kid22_part739),(kid22_part740),(kid22_part741)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part718_checked

  · exact kid22_part724_checked

  · exact kid22_part730_checked

  · exact kid22_part736_checked

  · exact kid22_part719_checked

  · exact kid22_part725_checked

  · exact kid22_part731_checked

  · exact kid22_part737_checked

  · exact kid22_part720_checked

  · exact kid22_part726_checked

  · exact kid22_part732_checked

  · exact kid22_part738_checked

  · exact kid22_part721_checked

  · exact kid22_part727_checked

  · exact kid22_part733_checked

  · exact kid22_part739_checked

  · exact kid22_part722_checked

  · exact kid22_part728_checked

  · exact kid22_part734_checked

  · exact kid22_part740_checked

  · exact kid22_part723_checked

  · exact kid22_part729_checked

  · exact kid22_part735_checked

  · exact kid22_part741_checked

def kid22_part742 : Audit := .cycle 1 10 true (1)
theorem kid22_part742_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part742) = true := by rfl

def kid22_part743 : Audit := .cycle 7 3 true (3)
theorem kid22_part743_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part743) = true := by rfl

def kid22_part744 : Audit := .split 21 (4,true) (byMove [
.cycle 73 1 false (17),
.cycle 30 1 false (8),
.cycle 31 1 false (9),
.cycle 24 15 true (4),
.cycle 0 77 true (0),
.split 22 (5,true) (byMove [
.cycle 0 53 true (0),
.cycle 61 1 false (9),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 0 77 true (0),
.last 23 (5,false),
.cycle 24 15 true (4),
.cycle 73 1 false (17),
.cycle 31 1 false (9),
.cycle 23 1 false (3),
.cycle 0 33 true (0),
.last 23 (5,false),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 4, 64, 64],[8, 9, 8, 8, 32, 1, 64],96⟩,
.cycle 0 58 true (0),
.cycle 0 33 true (0),
.cycle 23 1 false (1),
.cycle 89 1 false (17),
.last 23 (5,false),
.cycle 24 15 true (4),
.cycle 1 61 true (0),
.cycle 49 34 true (4),
.cycle 37 1 false (9),
.cycle 30 1 false (8),
.last 23 (5,false)
]),
.cycle 0 25 true (0),
.cycle 36 26 true (6),
.cycle 9 14 true (0),
.cycle 44 30 true (4),
.cycle 0 28 true (0),
.split 22 (5,true) (byMove [
.cycle 0 37 true (0),
.cycle 1 58 true (0),
.cycle 41 1 false (9),
.cycle 53 1 false (13),
.cycle 40 1 false (12),
.last 23 (5,false),
.last 44 (5,false),
.last 25 (5,false),
.cycle 9 14 true (0),
.cycle 0 57 true (0),
.cycle 0 28 true (0),
.last 25 (5,false),
.cycle 24 15 true (4),
.last 61 (5,false),
.last 48 (5,false),
.cycle 37 1 false (9),
.cycle 30 1 false (8),
.last 23 (5,false),
.last 66 (5,false),
.last 25 (5,false),
.last 80 (5,false),
.last 53 (5,false),
.last 40 (5,false),
.last 25 (5,false)
]),
.cycle 37 1 false (9),
.cycle 20 2 true (2),
.cycle 28 1 false (8),
.cycle 33 1 false (9),
.cycle 53 1 false (9),
.split 22 (5,true) (byMove [
.cycle 9 18 true (0),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 31 (5,false),
.last 23 (5,false),
.cycle 33 1 false (9),
.cycle 37 1 false (9),
.cycle 28 1 false (8),
.cycle 0 29 true (0),
.last 24 (5,false),
.last 27 (5,false),
.cycle 19 8 true (1),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 4, 64, 64],[8, 10, 8, 8, 32, 2, 64],96⟩,
.cycle 37 1 false (9),
.cycle 23 1 false (1),
.cycle 53 1 false (9),
.last 23 (5,false),
.cycle 39 32 true (5),
.cycle 26 17 true (4),
.cycle 9 16 true (0),
.cycle 0 29 true (0),
.cycle 21 2 true (2),
.last 27 (5,false)
]),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.cycle 2 53 true (0),
.cycle 5 17 true (0),
.cycle 23 13 true (5),
.split 22 (5,true) (byMove [
.last 88 (5,false),
.cycle 9 18 true (0),
.cycle 0 63 true (0),
.last 27 (5,false),
.last 24 (5,false),
.last 25 (5,false),
.cycle 6 17 true (0),
.last 25 (5,false),
.last 55 (5,false),
.cycle 3 52 true (0),
.cycle 0 28 true (0),
.last 25 (5,false),
.last 46 (5,false),
.last 31 (5,false),
.cycle 9 16 true (0),
.last 27 (5,false),
.cycle 21 2 true (3),
.last 25 (5,false),
.last 66 (5,false),
.last 25 (5,false),
.cycle 2 33 true (0),
.last 53 (5,false),
.cycle 23 13 true (5),
.last 25 (5,false)
])
])
theorem kid22_part744_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part744) = true := by rfl

def kid22_part745 : Audit := .cycle 0 11 true (0)
theorem kid22_part745_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part745) = true := by rfl

def kid22_part746 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 0 19 true (0),
.cycle 0 14 true (0),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,true),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 0 15 true (0),
.cycle 11 1 true (3),
.cycle 6 12 true (2),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 18 (5,true),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 28 true (0),
.cycle 0 49 true (0),
.cycle 0 14 true (0),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 0 15 true (0),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (5,true),
.last 22 (5,true),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 20 (5,true),
.cycle 1 15 true (1),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
]),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 24 1 false (4),
.cycle 1 14 true (1),
.split 11 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.last 20 (5,true),
.cycle 21 1 false (1),
.cycle 25 11 false (2),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true),
.last 15 (5,true),
.last 18 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 5 9 true (1),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
])
theorem kid22_part746_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part746) = true := by rfl

def kid22_part748 : Audit := .cycle 0 11 true (0)
theorem kid22_part748_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part748) = true := by rfl

def kid22_part749 : Audit := .cycle 1 10 true (1)
theorem kid22_part749_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part749) = true := by rfl

def kid22_part750 : Audit := .split 19 (4,true) (byMove [
.last 23 (5,false),
.cycle 25 1 false (3),
.last 21 (5,false),
.cycle 36 1 false (6),
.last 27 (5,false),
.cycle 22 1 false (2),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 0 24 true (0),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.cycle 23 1 false (3),
.cycle 27 1 false (5),
.cycle 37 1 false (5),
.cycle 22 1 false (2),
.cycle 0 54 true (0),
.cycle 2 22 true (0),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 2 22 true (0),
.last 22 (5,false)
])
theorem kid22_part750_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part750) = true := by rfl

def kid22_part751 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 11 8 true (0),
.cycle 26 1 false (4),
.cycle 0 21 true (0),
.last 18 (5,false),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 30 1 false (6),
.cycle 27 1 false (3),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 34 1 false (6),
.last 18 (5,false)
])
theorem kid22_part751_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part751) = true := by rfl

def kid22_part752 : Audit := .cycle 0 14 true (0)
theorem kid22_part752_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part752) = true := by rfl

def kid22_part753 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 0 15 true (0),
.cycle 11 1 true (3),
.cycle 6 12 true (2),
.cycle 11 3 true (2),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 1 15 true (1),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (3)
])
theorem kid22_part753_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part753) = true := by rfl

def kid22_part754 : Audit := .cycle 0 11 true (0)
theorem kid22_part754_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part754) = true := by rfl

def kid22_part755 : Audit := .cycle 1 10 true (1)
theorem kid22_part755_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part755) = true := by rfl

def kid22_part756 : Audit := .split 21 (4,true) (byMove [
.last 27 (5,false),
.last 29 (5,false),
.last 23 (5,false),
.cycle 24 15 true (4),
.last 31 (5,false),
.cycle 31 1 false (9),
.cycle 0 25 true (0),
.cycle 36 26 true (6),
.last 25 (5,false),
.cycle 44 30 true (4),
.cycle 0 28 true (0),
.cycle 9 14 true (0),
.cycle 37 1 false (9),
.cycle 20 2 true (2),
.last 27 (5,false),
.cycle 33 1 false (9),
.cycle 53 1 false (9),
.cycle 28 1 false (8),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 25 (5,false),
.cycle 5 17 true (0),
.cycle 23 13 true (5),
.last 37 (5,false)
])
theorem kid22_part756_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part756) = true := by rfl

def kid22_part757 : Audit := .split 19 (4,true) (byMove [
.cycle 42 1 false (10),
.cycle 36 1 false (10),
.last 21 (5,false),
.cycle 0 25 true (0),
.cycle 0 39 true (0),
.cycle 21 1 false (3),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.last 31 (5,false),
.cycle 0 49 true (0),
.cycle 0 25 true (0),
.cycle 0 22 true (0),
.cycle 31 1 false (7),
.cycle 18 2 true (2),
.cycle 34 1 false (10),
.cycle 36 1 false (10),
.cycle 43 1 false (7),
.cycle 27 1 false (7),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.cycle 2 27 true (0),
.cycle 20 28 true (3),
.cycle 21 10 true (4),
.cycle 0 22 true (0)
])
theorem kid22_part757_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part757) = true := by rfl

def kid22_part758 : Audit := .cycle 0 14 true (0)
theorem kid22_part758_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part758) = true := by rfl

def kid22_part759 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.cycle 11 3 true (4),
.cycle 0 14 true (0),
.last 19 (4,true),
.cycle 1 15 true (1),
.cycle 22 1 false (6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part759_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part759) = true := by rfl

def kid22_part760 : Audit := .cycle 7 5 true (3)
theorem kid22_part760_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part760) = true := by rfl

def kid22_part761 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.last 27 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 22 (4,true),
.last 20 (4,true),
.cycle 0 17 true (0),
.cycle 13 1 true (5),
.cycle 7 8 true (3),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 9 9 true (3),
.last 28 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part761_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part761) = true := by rfl

def kid22_part762 : Audit := .cycle 0 13 true (0)
theorem kid22_part762_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part762) = true := by rfl

def kid22_part763 : Audit := .split 17 (4,true) (byMove [
.last 21 (5,false),
.cycle 22 1 false (2),
.last 19 (5,false),
.cycle 31 1 false (5),
.last 25 (5,false),
.cycle 19 1 false (1),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.cycle 26 1 false (4),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 34 1 false (4),
.cycle 19 1 false (1),
.cycle 0 48 true (0),
.cycle 4 18 true (0),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 4 18 true (0),
.last 45 (5,false)
])
theorem kid22_part763_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part763) = true := by rfl

def kid22_part764 : Audit := .cycle 1 14 true (1)
theorem kid22_part764_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part764) = true := by rfl

def kid22_part765 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 21 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 25 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (3),
.last 14 (4,true),
.last 17 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.cycle 5 9 true (1),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 19 3 false (1)
])
theorem kid22_part765_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part765) = true := by rfl

def kid22_part766 : Audit := .cycle 0 11 true (0)
theorem kid22_part766_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part766) = true := by rfl

def kid22_part767 : Audit := .cycle 1 10 true (1)
theorem kid22_part767_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part767) = true := by rfl

def kid22_part768 : Audit := .cycle 2 9 true (1)
theorem kid22_part768_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part768) = true := by rfl

def kid22_part769 : Audit := .cycle 1 13 true (1)
theorem kid22_part769_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part769) = true := by rfl

def kid22_part770 : Audit := .cycle 8 3 true (3)
theorem kid22_part770_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part770) = true := by rfl

def kid22_part771 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 3 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part771_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part771) = true := by rfl

def kid22_part747 : Audit := .split 10 (5,true) (byMove [(kid22_part748),(kid22_part749),(kid22_part750),(kid22_part751),(kid22_part752),(kid22_part753),(kid22_part754),(kid22_part755),(kid22_part756),(kid22_part757),(kid22_part758),(kid22_part759),(kid22_part760),(kid22_part761),(kid22_part762),(kid22_part763),(kid22_part764),(kid22_part765),(kid22_part766),(kid22_part767),(kid22_part768),(kid22_part769),(kid22_part770),(kid22_part771)])

theorem kid22_part747_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part747) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid22_part748),(kid22_part749),(kid22_part750),(kid22_part751),(kid22_part752),(kid22_part753),(kid22_part754),(kid22_part755),(kid22_part756),(kid22_part757),(kid22_part758),(kid22_part759),(kid22_part760),(kid22_part761),(kid22_part762),(kid22_part763),(kid22_part764),(kid22_part765),(kid22_part766),(kid22_part767),(kid22_part768),(kid22_part769),(kid22_part770),(kid22_part771)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part748_checked

  · exact kid22_part754_checked

  · exact kid22_part760_checked

  · exact kid22_part766_checked

  · exact kid22_part749_checked

  · exact kid22_part755_checked

  · exact kid22_part761_checked

  · exact kid22_part767_checked

  · exact kid22_part750_checked

  · exact kid22_part756_checked

  · exact kid22_part762_checked

  · exact kid22_part768_checked

  · exact kid22_part751_checked

  · exact kid22_part757_checked

  · exact kid22_part763_checked

  · exact kid22_part769_checked

  · exact kid22_part752_checked

  · exact kid22_part758_checked

  · exact kid22_part764_checked

  · exact kid22_part770_checked

  · exact kid22_part753_checked

  · exact kid22_part759_checked

  · exact kid22_part765_checked

  · exact kid22_part771_checked

def kid22_part772 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 12 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 0 25 false (4),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 34 7 false (3),
.cycle 45 1 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 55 1 false (9),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 27 13 false (2),
.cycle 0 26 true (0),
.cycle 1 15 true (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 11 8 true (3),
.cycle 0 17 true (0),
.cycle 13 1 true (5),
.cycle 11 8 true (3),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 19 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5)
]),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 9 8 true (2),
.cycle 1 14 true (1),
.cycle 41 19 true (0),
.split 13 (5,true) (byMove [
.cycle 6 11 true (2),
.cycle 0 70 true (0),
.cycle 32 1 false (2),
.cycle 31 1 false (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 11 9 true (3),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 10 8 true (2),
.cycle 14 6 true (1),
.cycle 41 5 false (8),
.cycle 5 9 true (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 5 true (3),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.cycle 11 5 true (3),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 6 true (3),
.cycle 13 1 true (5)
])
])
theorem kid22_part772_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part772) = true := by rfl

def kid22_part773 : Audit := .split 13 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 23 7 false (1),
.cycle 19 5 false (1),
.cycle 11 7 true (2),
.cycle 0 35 false (4),
.split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 23 true (1),
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.last 32 (5,false),
.last 15 (5,false),
.cycle 11 7 true (2),
.cycle 1 19 true (1),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.cycle 1 18 true (1),
.last 15 (5,false),
.cycle 27 7 false (1),
.cycle 20 5 false (1),
.cycle 11 9 true (1),
.cycle 26 1 false (0),
.cycle 99 27 true (5),
.last 15 (5,false),
.cycle 11 7 true (2),
.cycle 1 19 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 23 7 false (1),
.last 15 (5,false)
]),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 17 8 true (3),
.cycle 0 15 true (0),
.cycle 0 18 true (0),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 23 7 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 10 true (2),
.last 22 (5,false),
.cycle 0 18 true (0),
.last 15 (5,false),
.cycle 11 7 true (2),
.last 19 (5,false),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 23 7 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (2),
.last 15 (5,false)
]),
.cycle 6 11 true (2),
.cycle 12 2 true (2),
.cycle 19 5 false (1),
.cycle 5 9 true (1),
.cycle 40 19 true (0),
.split 14 (5,true) (byMove [
.cycle 10 12 true (1),
.cycle 1 18 true (1),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 30 (5,false),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 7 11 true (2),
.cycle 9 6 true (2),
.cycle 1 16 true (1),
.last 16 (5,false),
.last 17 (5,false),
.cycle 12 8 true (1),
.cycle 20 5 false (1),
.cycle 5 11 true (1),
.cycle 21 1 false (1),
.cycle 40 19 true (0),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 11 9 true (2),
.cycle 11 4 true (2),
.cycle 1 16 true (1),
.cycle 13 2 true (2),
.last 17 (5,false)
]),
.cycle 1 14 true (1),
.cycle 11 5 true (2),
.cycle 2 15 true (1),
.cycle 0 15 true (0),
.cycle 11 5 true (2),
.split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 11 6 true (2),
.last 18 (5,false),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (5,false),
.cycle 3 12 true (1),
.cycle 0 18 true (0),
.last 15 (5,false),
.cycle 6 9 true (2),
.last 17 (5,false),
.cycle 11 4 true (2),
.cycle 1 16 true (1),
.cycle 13 2 true (3),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 5 true (2),
.last 15 (5,false)
])
])
theorem kid22_part773_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part773) = true := by rfl

def kid22_part774 : Audit := .cycle 1 12 true (1)
theorem kid22_part774_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part774) = true := by rfl

def kid22_part775 : Audit := .split 15 (4,true) (byMove [
.cycle 30 1 false (6),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 26 1 false (4),
.cycle 0 57 true (0),
.split 16 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 0 57 true (0),
.last 17 (5,false),
.cycle 26 1 false (4),
.cycle 30 1 false (6),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.cycle 30 1 false (6),
.last 17 (5,false),
.cycle 35 1 false (3),
.cycle 34 1 false (6),
.cycle 28 1 false (4),
.cycle 17 1 false (1),
.cycle 34 1 false (6),
.last 17 (5,false),
.cycle 5 16 true (0),
.cycle 1 45 true (0),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 19 1 false (1),
.last 17 (5,false)
]),
.cycle 0 37 true (0),
.cycle 22 18 true (4),
.cycle 23 1 false (3),
.cycle 0 17 true (0),
.cycle 0 20 true (0),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.last 37 (5,false),
.cycle 10 10 true (0),
.last 24 (5,false),
.cycle 0 20 true (0),
.last 17 (5,false),
.cycle 5 16 true (0),
.last 45 (5,false),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 60 (5,false),
.cycle 5 34 true (0),
.last 24 (5,false),
.last 17 (5,false)
]),
.cycle 23 1 false (3),
.cycle 14 2 true (2),
.cycle 17 1 false (1),
.cycle 21 1 false (3),
.cycle 31 1 false (3),
.split 16 (5,true) (byMove [
.cycle 5 15 true (0),
.cycle 12 30 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 25 (5,false),
.last 17 (5,false),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.cycle 18 1 false (2),
.cycle 28 1 false (6),
.last 18 (5,false),
.last 19 (5,false),
.cycle 13 8 true (1),
.cycle 31 1 false (3),
.cycle 23 1 false (3),
.cycle 17 1 false (1),
.cycle 31 1 false (3),
.last 17 (5,false),
.cycle 23 22 true (3),
.cycle 5 18 true (0),
.cycle 23 1 false (3),
.cycle 0 43 true (0),
.cycle 15 2 true (2),
.last 19 (5,false)
]),
.cycle 0 42 true (0),
.cycle 5 14 true (0),
.cycle 2 39 true (0),
.cycle 0 17 true (0),
.cycle 5 14 true (0),
.split 16 (5,true) (byMove [
.last 66 (5,false),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 0 18 true (0),
.last 18 (5,false),
.last 19 (5,false),
.cycle 0 17 true (0),
.last 42 (5,false),
.last 25 (5,false),
.cycle 3 14 true (0),
.cycle 0 20 true (0),
.last 17 (5,false),
.last 26 (5,false),
.last 19 (5,false),
.cycle 23 1 false (3),
.last 41 (5,false),
.cycle 15 2 true (3),
.last 19 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 18 20 true (3),
.cycle 5 14 true (0),
.last 17 (5,false)
])
])
theorem kid22_part775_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part775) = true := by rfl

def kid22_part776 : Audit := .cycle 5 7 true (1)
theorem kid22_part776_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part776) = true := by rfl

def kid22_part778 : Audit := .split 14 (5,true) (byMove [
.cycle 11 8 true (1),
.last 24 (4,true),
.cycle 18 1 false (0),
.last 18 (4,true),
.last 15 (4,true),
.cycle 0 18 false (4),
.cycle 6 9 true (1),
.last 16 (4,true),
.cycle 9 12 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 0 18 true (0),
.last 17 (4,true),
.last 16 (4,true),
.last 21 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.cycle 15 6 false (1),
.cycle 12 9 true (2),
.last 16 (4,true),
.cycle 13 2 true (2),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 1 18 true (1)
])
theorem kid22_part778_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part778) = true := by rfl

def kid22_part779 : Audit := .cycle 1 14 true (1)
theorem kid22_part779_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part779) = true := by rfl

def kid22_part780 : Audit := .split 17 (4,true) (byMove [
.last 21 (5,true),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.last 23 (5,true),
.last 25 (5,true),
.last 18 (5,true),
.cycle 0 41 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.last 18 (5,true),
.cycle 27 1 false (3),
.cycle 16 2 true (2),
.cycle 21 1 false (1),
.cycle 25 1 false (3),
.cycle 35 1 false (3),
.last 18 (5,true),
.last 43 (5,true),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.last 21 (5,true),
.last 18 (5,true)
])
theorem kid22_part780_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part780) = true := by rfl

def kid22_part781 : Audit := .split 16 (5,true) (byMove [
.cycle 13 8 true (1),
.last 38 (4,true),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 22 (4,true),
.cycle 18 1 false (0),
.cycle 22 1 false (2),
.last 18 (4,true),
.cycle 19 1 false (1),
.cycle 29 1 false (5),
.last 17 (4,true),
.cycle 20 1 false (4),
.last 19 (4,true),
.cycle 14 3 false (3),
.cycle 24 1 false (2),
.cycle 17 1 false (1),
.last 22 (4,true),
.cycle 18 1 false (0),
.last 25 (4,true),
.last 18 (4,true),
.cycle 15 2 true (2),
.last 35 (4,true),
.last 17 (4,true),
.cycle 0 21 true (0)
])
theorem kid22_part781_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part781) = true := by rfl

def kid22_part782 : Audit := .split 19 (4,true) (byMove [
.cycle 24 17 true (4),
.last 23 (5,true),
.last 21 (5,true),
.last 24 (5,true),
.last 41 (5,true),
.last 20 (5,true),
.cycle 17 21 true (-1),
.last 22 (5,true),
.cycle 37 8 true (7),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 1, 128, 524288, 1048576, 32768, 33554434, 8606711808, 50365440, 524288, 1048576, 134217728, 1024, 16777216, 1152, 137438953472, 274877906944, 8589934592, 33554432, 281475027076096, 50365440, 128, 256, 134217728, 50365440, 16777216, 128, 137438953472, 274877906944, 549755813888, 1024, 68719476736, 281483583423872, 137438953472, 274877906944, 35184372088832, 44117937651712, 331030359737344, 45286185534464, 137438953472, 274877906944, 549755813888, 1168247882752, 68719476736, 331442676598144, 281474976710656],[2, 1024, 4194304, 1, 8, 281474976710656, 8192, 4194304, 281474976710656, 4096, 32768, 281474976710656, 33554432, 4194304, 50365440, 16777216, 134217728, 281474976710656, 2147483648, 1099511627776, 281474976710656, 1073741824, 8589934592, 281474976710656, 33554432, 1024, 4227072, 16777216, 134217728, 281474976710656, 137438953472, 1099511627776, 50365440, 68719476736, 549755813888, 281474976710656, 8796093022208, 1099511627776, 326761166439424, 4398046511104, 35184372088832, 281474976710656, 137438953472, 1099511627776, 45148746580992, 68719476736, 549755813888, 281474976710656, 281474976710656],562940294729792⟩,
.last 53 (5,true),
.last 23 (5,true),
.last 30 (5,true),
.cycle 18 2 true (0),
.last 21 (5,true),
.last 24 (5,true),
.cycle 57 23 true (0),
.last 20 (5,true),
.last 36 (5,true),
.last 22 (5,true),
.last 50 (5,true),
.cycle 23 19 true (3),
.last 22 (5,true),
.cycle 19 2 true (1)
])
theorem kid22_part782_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part782) = true := by rfl

def kid22_part783 : Audit := .split 12 (5,true) (byMove [
.last 21 (4,true),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 36 (4,true),
.cycle 13 1 false (-1),
.cycle 6 11 true (0),
.cycle 41 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 18 (4,true),
.cycle 13 1 false (1),
.last 20 (4,true),
.cycle 12 3 false (0),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 49 1 false (3),
.cycle 13 1 false (-1),
.last 25 (4,true),
.last 52 (4,true),
.last 19 (4,true),
.last 45 (4,true),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part783_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part783) = true := by rfl

def kid22_part784 : Audit := .cycle 6 5 true (2)
theorem kid22_part784_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part784) = true := by rfl

def kid22_part785 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 7 8 true (2),
.cycle 0 14 true (0),
.cycle 0 17 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.cycle 5 11 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 1 13 true (1)
])
theorem kid22_part785_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part785) = true := by rfl

def kid22_part786 : Audit := .cycle 9 2 true (2)
theorem kid22_part786_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part786) = true := by rfl

def kid22_part787 : Audit := .cycle 1 12 true (1)
theorem kid22_part787_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part787) = true := by rfl

def kid22_part788 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 19 (5,true),
.cycle 1 16 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 9 20 true (0),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.last 12 (5,true),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 5 9 true (1),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.last 15 (5,true),
.last 12 (5,true)
])
theorem kid22_part788_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part788) = true := by rfl

def kid22_part789 : Audit := .split 11 (5,true) (byMove [
.cycle 11 8 true (2),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 25 (4,true),
.cycle 15 1 true (3),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 25 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (5),
.last 14 (4,true),
.last 19 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.cycle 5 9 true (1),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.last 17 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (5)
])
theorem kid22_part789_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part789) = true := by rfl

def kid22_part790 : Audit := .split 13 (4,true) (byMove [
.last 17 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 0 33 true (-2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 16 8 true (2),
.cycle 0 15 true (0),
.cycle 0 18 true (0),
.last 14 (5,true),
.cycle 6 11 true (1),
.cycle 12 2 true (2),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 22 27 true (-1),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.last 17 (5,true),
.last 14 (5,true)
])
theorem kid22_part790_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part790) = true := by rfl

def kid22_part791 : Audit := .split 13 (5,true) (byMove [
.cycle 11 8 true (0),
.last 26 (4,true),
.cycle 20 1 false (-2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 14 4 false (0),
.last 16 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 15 5 true (3),
.last 16 (4,true),
.last 15 (4,true),
.last 23 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 14 4 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 12 2 true (1),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 19 (4,true)
])
theorem kid22_part791_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part791) = true := by rfl

def kid22_part792 : Audit := .cycle 5 7 true (1)
theorem kid22_part792_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part792) = true := by rfl

def kid22_part793 : Audit := .split 15 (4,true) (byMove [
.last 19 (5,true),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 21 (5,true),
.last 23 (5,true),
.last 16 (5,true),
.cycle 0 37 true (0),
.cycle 22 18 true (4),
.cycle 24 1 false (2),
.cycle 0 17 true (0),
.cycle 0 20 true (0),
.last 16 (5,true),
.cycle 24 1 false (2),
.cycle 14 2 true (2),
.cycle 18 1 false (0),
.cycle 22 1 false (2),
.cycle 32 1 false (2),
.last 16 (5,true),
.cycle 0 42 true (0),
.last 19 (5,true),
.last 17 (5,true),
.cycle 0 17 true (0),
.last 19 (5,true),
.last 16 (5,true)
])
theorem kid22_part793_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part793) = true := by rfl

def kid22_part794 : Audit := .split 19 (4,true) (byMove [
.last 23 (5,true),
.cycle 11 10 true (-3),
.cycle 11 16 true (-3),
.last 29 (5,true),
.last 27 (5,true),
.last 20 (5,true),
.cycle 17 21 true (-1),
.cycle 19 7 true (1),
.cycle 49 8 true (1),
.cycle 20 14 true (1),
.cycle 0 26 true (-3),
.last 20 (5,true),
.cycle 26 11 true (1),
.cycle 18 2 true (0),
.cycle 12 8 true (-3),
.cycle 24 18 true (1),
.cycle 35 15 true (0),
.last 20 (5,true),
.last 36 (5,true),
.last 25 (5,true),
.last 21 (5,true),
.last 28 (5,true),
.last 25 (5,true),
.last 20 (5,true)
])
theorem kid22_part794_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part794) = true := by rfl

def kid22_part795 : Audit := .split 12 (5,true) (byMove [
.cycle 12 8 true (-1),
.last 18 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 14 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 17 1 false (5),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 17 (4,true),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 12 2 true (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 15 3 true (3)
])
theorem kid22_part795_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part795) = true := by rfl

def kid22_part796 : Audit := .cycle 6 5 true (2)
theorem kid22_part796_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part796) = true := by rfl

def kid22_part797 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 0 25 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 41 19 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 1 13 true (1)
])
theorem kid22_part797_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part797) = true := by rfl

def kid22_part798 : Audit := .split 12 (5,true) (byMove [
.cycle 11 8 true (1),
.cycle 1 16 true (1),
.last 19 (4,true),
.cycle 19 1 false (1),
.last 23 (4,true),
.cycle 1 16 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 2 14 true (1),
.last 15 (4,true),
.last 17 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.last 23 (4,true),
.cycle 16 3 false (0),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 2 14 true (1)
])
theorem kid22_part798_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part798) = true := by rfl

def kid22_part799 : Audit := .cycle 1 12 true (1)
theorem kid22_part799_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part799) = true := by rfl

def kid22_part800 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,true),
.last 20 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.last 24 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 14 8 true (3),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.last 12 (5,true),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 16 (5,true),
.cycle 5 7 true (1),
.cycle 37 17 true (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.last 15 (5,true),
.last 12 (5,true)
])
theorem kid22_part800_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part800) = true := by rfl

def kid22_part801 : Audit := .split 11 (5,true) (byMove [
.cycle 11 8 true (2),
.last 26 (4,true),
.cycle 18 1 false (0),
.last 30 (4,true),
.last 12 (4,true),
.cycle 21 1 true (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 22 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (5),
.last 14 (4,true),
.last 13 (4,true),
.last 21 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 15 3 false (1),
.cycle 1 12 true (1),
.last 17 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (5)
])
theorem kid22_part801_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part801) = true := by rfl

def kid22_part777 : Audit := .split 10 (5,false) (byMove [(kid22_part778),(kid22_part779),(kid22_part780),(kid22_part781),(kid22_part782),(kid22_part783),(kid22_part784),(kid22_part785),(kid22_part786),(kid22_part787),(kid22_part788),(kid22_part789),(kid22_part790),(kid22_part791),(kid22_part792),(kid22_part793),(kid22_part794),(kid22_part795),(kid22_part796),(kid22_part797),(kid22_part798),(kid22_part799),(kid22_part800),(kid22_part801)])

theorem kid22_part777_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part777) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part778),(kid22_part779),(kid22_part780),(kid22_part781),(kid22_part782),(kid22_part783),(kid22_part784),(kid22_part785),(kid22_part786),(kid22_part787),(kid22_part788),(kid22_part789),(kid22_part790),(kid22_part791),(kid22_part792),(kid22_part793),(kid22_part794),(kid22_part795),(kid22_part796),(kid22_part797),(kid22_part798),(kid22_part799),(kid22_part800),(kid22_part801)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part778_checked

  · exact kid22_part784_checked

  · exact kid22_part790_checked

  · exact kid22_part796_checked

  · exact kid22_part779_checked

  · exact kid22_part785_checked

  · exact kid22_part791_checked

  · exact kid22_part797_checked

  · exact kid22_part780_checked

  · exact kid22_part786_checked

  · exact kid22_part792_checked

  · exact kid22_part798_checked

  · exact kid22_part781_checked

  · exact kid22_part787_checked

  · exact kid22_part793_checked

  · exact kid22_part799_checked

  · exact kid22_part782_checked

  · exact kid22_part788_checked

  · exact kid22_part794_checked

  · exact kid22_part800_checked

  · exact kid22_part783_checked

  · exact kid22_part789_checked

  · exact kid22_part795_checked

  · exact kid22_part801_checked

def kid22_part802 : Audit := .cycle 1 10 true (1)
theorem kid22_part802_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part802) = true := by rfl

def kid22_part803 : Audit := .cycle 7 3 true (3)
theorem kid22_part803_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part803) = true := by rfl

def kid22_part804 : Audit := .cycle 2 9 true (1)
theorem kid22_part804_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part804) = true := by rfl

def kid22_part805 : Audit := .cycle 0 11 true (0)
theorem kid22_part805_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part805) = true := by rfl

def kid22_part806 : Audit := .split 10 (4,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.cycle 8 4 true (3),
.cycle 0 12 true (0),
.cycle 0 15 true (0),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 38 1 false (10),
.cycle 21 1 false (3),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 6 12 true (2),
.cycle 28 9 false (2),
.cycle 0 14 true (0),
.cycle 19 1 false (1),
.cycle 1 15 true (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 12 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 10 8 true (3),
.cycle 3 8 true (1),
.cycle 0 14 true (0),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 10 8 true (3),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
]),
.cycle 6 5 true (2),
.cycle 10 2 true (3),
.cycle 9 2 true (3),
.cycle 1 12 true (1),
.cycle 5 9 true (1),
.split 11 (5,true) (byMove [
.cycle 13 7 true (3),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (3),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 10 8 true (2),
.cycle 24 7 false (2),
.cycle 1 14 true (1),
.cycle 19 1 false (1),
.cycle 5 9 true (1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (3),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (3),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
])
theorem kid22_part806_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part806) = true := by rfl

def kid22_part808 : Audit := .cycle 1 11 true (1)
theorem kid22_part808_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part808) = true := by rfl

def kid22_part809 : Audit := .cycle 7 4 true (3)
theorem kid22_part809_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part809) = true := by rfl

def kid22_part810 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 9 4 true (3),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 21 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4)
])
theorem kid22_part810_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part810) = true := by rfl

def kid22_part811 : Audit := .cycle 0 12 true (0)
theorem kid22_part811_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part811) = true := by rfl

def kid22_part812 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,false),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 35 (5,false),
.cycle 0 21 true (0),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 6 12 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.cycle 1 15 true (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 12 (5,false)
])
theorem kid22_part812_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part812) = true := by rfl

def kid22_part813 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 0 21 false (4),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 0 16 true (0),
.cycle 12 1 true (2),
.cycle 18 8 false (2),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 59 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 21 5 false (1),
.cycle 12 1 true (2)
])
theorem kid22_part813_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part813) = true := by rfl

def kid22_part814 : Audit := .cycle 0 11 true (0)
theorem kid22_part814_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part814) = true := by rfl

def kid22_part815 : Audit := .cycle 1 10 true (1)
theorem kid22_part815_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part815) = true := by rfl

def kid22_part816 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 0 23 true (0),
.cycle 40 1 false (8),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.cycle 0 22 true (0),
.last 19 (5,false),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.cycle 9 10 true (3),
.cycle 1 20 true (1),
.cycle 5 17 true (1),
.last 21 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.last 19 (5,false)
])
theorem kid22_part816_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part816) = true := by rfl

def kid22_part817 : Audit := .cycle 3 8 true (1)
theorem kid22_part817_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part817) = true := by rfl

def kid22_part818 : Audit := .cycle 0 14 true (0)
theorem kid22_part818_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part818) = true := by rfl

def kid22_part819 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 19 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 1 20 true (1),
.cycle 29 1 false (7),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part819_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part819) = true := by rfl

def kid22_part820 : Audit := .cycle 6 5 true (2)
theorem kid22_part820_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part820) = true := by rfl

def kid22_part821 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 0 17 true (0),
.last 16 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 9 4 true (3),
.cycle 1 14 true (1),
.cycle 5 11 true (1),
.cycle 28 9 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
theorem kid22_part821_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part821) = true := by rfl

def kid22_part822 : Audit := .cycle 9 2 true (3)
theorem kid22_part822_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part822) = true := by rfl

def kid22_part823 : Audit := .cycle 1 12 true (1)
theorem kid22_part823_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part823) = true := by rfl

def kid22_part824 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,false),
.cycle 0 15 true (0),
.last 21 (5,false),
.cycle 21 1 false (1),
.last 28 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 6 9 true (2),
.cycle 15 2 true (2),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 5 9 true (1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 10 2 true (3)
])
theorem kid22_part824_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part824) = true := by rfl

def kid22_part825 : Audit := .split 12 (5,false) (byMove [
.cycle 17 8 false (3),
.cycle 1 16 true (1),
.last 19 (4,true),
.cycle 22 1 false (0),
.last 23 (4,true),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 9 4 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 11 2 true (2),
.last 15 (4,true),
.cycle 16 6 false (2),
.cycle 5 9 true (1),
.last 17 (4,true),
.last 23 (4,true),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 20 5 false (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 3 false (1)
])
theorem kid22_part825_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part825) = true := by rfl

def kid22_part826 : Audit := .cycle 0 11 true (0)
theorem kid22_part826_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part826) = true := by rfl

def kid22_part827 : Audit := .cycle 1 10 true (1)
theorem kid22_part827_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part827) = true := by rfl

def kid22_part828 : Audit := .cycle 2 9 true (1)
theorem kid22_part828_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part828) = true := by rfl

def kid22_part829 : Audit := .cycle 1 13 true (1)
theorem kid22_part829_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part829) = true := by rfl

def kid22_part830 : Audit := .cycle 8 3 true (3)
theorem kid22_part830_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part830) = true := by rfl

def kid22_part831 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 11 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 9 3 true (3),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 3 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part831_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part831) = true := by rfl

def kid22_part807 : Audit := .split 10 (5,true) (byMove [(kid22_part808),(kid22_part809),(kid22_part810),(kid22_part811),(kid22_part812),(kid22_part813),(kid22_part814),(kid22_part815),(kid22_part816),(kid22_part817),(kid22_part818),(kid22_part819),(kid22_part820),(kid22_part821),(kid22_part822),(kid22_part823),(kid22_part824),(kid22_part825),(kid22_part826),(kid22_part827),(kid22_part828),(kid22_part829),(kid22_part830),(kid22_part831)])

theorem kid22_part807_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part807) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid22_part808),(kid22_part809),(kid22_part810),(kid22_part811),(kid22_part812),(kid22_part813),(kid22_part814),(kid22_part815),(kid22_part816),(kid22_part817),(kid22_part818),(kid22_part819),(kid22_part820),(kid22_part821),(kid22_part822),(kid22_part823),(kid22_part824),(kid22_part825),(kid22_part826),(kid22_part827),(kid22_part828),(kid22_part829),(kid22_part830),(kid22_part831)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part808_checked

  · exact kid22_part814_checked

  · exact kid22_part820_checked

  · exact kid22_part826_checked

  · exact kid22_part809_checked

  · exact kid22_part815_checked

  · exact kid22_part821_checked

  · exact kid22_part827_checked

  · exact kid22_part810_checked

  · exact kid22_part816_checked

  · exact kid22_part822_checked

  · exact kid22_part828_checked

  · exact kid22_part811_checked

  · exact kid22_part817_checked

  · exact kid22_part823_checked

  · exact kid22_part829_checked

  · exact kid22_part812_checked

  · exact kid22_part818_checked

  · exact kid22_part824_checked

  · exact kid22_part830_checked

  · exact kid22_part813_checked

  · exact kid22_part819_checked

  · exact kid22_part825_checked

  · exact kid22_part831_checked

def kid22_part711 : Audit := .split 9 (2,true) (byMove [(kid22_part712),(kid22_part713),(kid22_part714),(kid22_part715),(kid22_part716),(kid22_part717),(kid22_part742),(kid22_part743),(kid22_part744),(kid22_part745),(kid22_part746),(kid22_part747),(kid22_part772),(kid22_part773),(kid22_part774),(kid22_part775),(kid22_part776),(kid22_part777),(kid22_part802),(kid22_part803),(kid22_part804),(kid22_part805),(kid22_part806),(kid22_part807)])

theorem kid22_part711_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (kid22_part711) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) 9 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid22_part712),(kid22_part713),(kid22_part714),(kid22_part715),(kid22_part716),(kid22_part717),(kid22_part742),(kid22_part743),(kid22_part744),(kid22_part745),(kid22_part746),(kid22_part747),(kid22_part772),(kid22_part773),(kid22_part774),(kid22_part775),(kid22_part776),(kid22_part777),(kid22_part802),(kid22_part803),(kid22_part804),(kid22_part805),(kid22_part806),(kid22_part807)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part712_checked

  · exact kid22_part742_checked

  · exact kid22_part772_checked

  · exact kid22_part802_checked

  · exact kid22_part713_checked

  · exact kid22_part743_checked

  · exact kid22_part773_checked

  · exact kid22_part803_checked

  · exact kid22_part714_checked

  · exact kid22_part744_checked

  · exact kid22_part774_checked

  · exact kid22_part804_checked

  · exact kid22_part715_checked

  · exact kid22_part745_checked

  · exact kid22_part775_checked

  · exact kid22_part805_checked

  · exact kid22_part716_checked

  · exact kid22_part746_checked

  · exact kid22_part776_checked

  · exact kid22_part806_checked

  · exact kid22_part717_checked

  · exact kid22_part747_checked

  · exact kid22_part777_checked

  · exact kid22_part807_checked

def kid22_part832 : Audit := .cycle 1 10 true (1)
theorem kid22_part832_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,3⟩)) (kid22_part832) = true := by rfl

def kid22_part834 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 12 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 14 true (1),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 34 7 false (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.cycle 28 1 false (2),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 1 16 true (1),
.last 15 (5,false),
.cycle 1 15 true (1),
.cycle 24 1 false (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 21 true (1),
.cycle 3 10 true (1),
.cycle 0 20 true (0),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 13 true (3),
.cycle 1 21 true (1),
.last 21 (5,true),
.cycle 13 1 true (5),
.cycle 11 8 true (3),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 19 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5)
]),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 9 8 true (2),
.split 13 (5,true) (byMove [
.cycle 10 8 true (2),
.cycle 23 104 true (0),
.last 15 (5,false),
.cycle 0 34 true (0),
.cycle 0 19 true (0),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 1 17 true (1),
.cycle 29 3 false (2),
.last 15 (5,false),
.cycle 5 9 true (1),
.cycle 24 1 false (0),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 5 true (3),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 12 2 true (4),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.last 20 (5,true),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 11 5 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 6 true (3),
.cycle 13 1 true (5)
])
])
theorem kid22_part834_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part834) = true := by rfl

def kid22_part835 : Audit := .cycle 0 13 true (0)
theorem kid22_part835_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part835) = true := by rfl

def kid22_part836 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.split 19 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 30 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.last 22 (5,true),
.cycle 17 6 false (3),
.last 22 (5,true),
.last 25 (5,true),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.last 25 (5,true),
.cycle 23 1 false (1),
.last 22 (5,true)
]),
.cycle 17 5 true (2),
.cycle 63 1 false (11),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.split 19 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (7),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.last 20 (5,true),
.cycle 17 11 true (2),
.last 22 (5,true),
.cycle 33 1 false (7),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 0 54 true (0),
.cycle 17 5 true (2),
.last 42 (5,true),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.last 20 (5,true)
]),
.cycle 17 5 false (3),
.cycle 16 5 false (3),
.cycle 17 7 true (1),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.split 19 (5,false) (byMove [
.last 23 (5,true),
.cycle 17 9 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.last 23 (5,true),
.cycle 24 1 false (2),
.cycle 18 2 true (1),
.cycle 17 7 true (1),
.cycle 22 1 false (2),
.last 20 (5,true),
.last 24 (5,true),
.last 22 (5,true),
.last 25 (5,true),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.last 23 (5,true),
.cycle 17 5 false (3),
.last 21 (5,true),
.cycle 17 7 true (1),
.cycle 17 3 false (3),
.last 20 (5,true)
]),
.cycle 17 5 true (2),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.split 19 (5,false) (byMove [
.last 48 (5,true),
.cycle 24 1 false (2),
.cycle 18 2 true (2),
.cycle 17 7 true (2),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.cycle 20 10 true (4),
.cycle 0 21 true (0),
.cycle 30 1 false (4),
.last 20 (5,true),
.cycle 30 1 false (4),
.cycle 16 4 true (2),
.last 21 (5,true),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 0 54 true (0),
.cycle 17 5 true (2),
.cycle 2 20 true (0),
.cycle 0 21 true (0),
.cycle 17 7 true (2),
.last 20 (5,true)
])
])
theorem kid22_part836_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part836) = true := by rfl

def kid22_part837 : Audit := .cycle 17 1 false (1)
theorem kid22_part837_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part837) = true := by rfl

def kid22_part838 : Audit := .cycle 13 1 false (-1)
theorem kid22_part838_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part838) = true := by rfl

def kid22_part840 : Audit := .cycle 0 15 true (0)
theorem kid22_part840_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part840) = true := by rfl

def kid22_part841 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 30 1 false (2),
.cycle 37 1 false (1),
.cycle 33 1 false (-1),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 54 1 false (10),
.cycle 29 1 false (3),
.cycle 35 1 false (1),
.cycle 1 20 true (1),
.cycle 42 5 false (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 27 1 false (1),
.cycle 33 1 false (-1),
.cycle 0 24 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (1),
.cycle 7 14 true (1)
])
theorem kid22_part841_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part841) = true := by rfl

def kid22_part842 : Audit := .cycle 21 1 false (1)
theorem kid22_part842_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part842) = true := by rfl

def kid22_part843 : Audit := .cycle 0 17 true (0)
theorem kid22_part843_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part843) = true := by rfl

def kid22_part844 : Audit := .cycle 14 1 false (-2)
theorem kid22_part844_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part844) = true := by rfl

def kid22_part845 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.cycle 31 1 false (5),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 12 5 false (1),
.last 14 (2,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 21 true (0),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part845_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part845) = true := by rfl

def kid22_part846 : Audit := .split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 24 true (1),
.cycle 26 1 false (2),
.cycle 29 1 false (1),
.cycle 0 43 true (-1),
.last 19 (2,true),
.cycle 11 5 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 25 1 false (3),
.cycle 18 8 true (-1),
.cycle 1 17 true (1),
.cycle 58 5 false (6),
.last 17 (2,true),
.cycle 11 7 true (2),
.cycle 23 1 false (1),
.cycle 31 1 false (-1),
.last 19 (2,true),
.cycle 11 5 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 13 10 true (2),
.cycle 1 17 true (1)
])
theorem kid22_part846_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part846) = true := by rfl

def kid22_part847 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 22 (5,true),
.cycle 0 14 true (0),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.cycle 3 10 true (1),
.cycle 1 20 true (1),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.last 15 (5,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 1 13 true (1)
])
theorem kid22_part847_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part847) = true := by rfl

def kid22_part848 : Audit := .cycle 0 13 true (0)
theorem kid22_part848_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part848) = true := by rfl

def kid22_part849 : Audit := .split 18 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 20 1 false (2),
.cycle 17 5 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 0 21 true (0),
.cycle 17 5 false (3),
.last 20 (2,true),
.cycle 17 7 true (1),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 17 7 true (1),
.cycle 17 5 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.cycle 0 21 true (0)
])
theorem kid22_part849_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part849) = true := by rfl

def kid22_part850 : Audit := .cycle 16 1 false (0)
theorem kid22_part850_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part850) = true := by rfl

def kid22_part851 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 35 1 false (9),
.cycle 23 1 false (3),
.cycle 30 1 false (6),
.cycle 13 1 true (5),
.cycle 67 5 false (6),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 13 1 true (5)
])
theorem kid22_part851_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part851) = true := by rfl

def kid22_part852 : Audit := .split 15 (5,true) (byMove [
.cycle 17 20 true (1),
.cycle 74 33 true (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 23 1 false (-3),
.cycle 16 6 false (0),
.cycle 0 20 true (0),
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 23 1 false (3),
.cycle 25 1 false (-1),
.cycle 19 11 true (2),
.cycle 21 5 false (1),
.last 20 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.cycle 23 1 false (-3),
.cycle 14 6 false (2),
.cycle 0 20 true (0),
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 1 24 true (1),
.cycle 16 8 false (2),
.cycle 6 21 true (1)
])
theorem kid22_part852_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part852) = true := by rfl

def kid22_part853 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 16 (5,true),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 14 (5,true),
.last 13 (5,true),
.last 17 (5,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 19 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.cycle 32 22 true (1),
.cycle 1 18 true (1),
.last 14 (5,true),
.last 13 (5,true),
.last 17 (5,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.last 16 (5,true)
])
theorem kid22_part853_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part853) = true := by rfl

def kid22_part854 : Audit := .split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 26 true (1),
.cycle 28 1 false (2),
.cycle 33 1 false (1),
.cycle 0 53 true (-2),
.last 23 (2,true),
.cycle 13 5 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 27 1 false (3),
.cycle 20 10 true (-2),
.cycle 1 21 true (1),
.cycle 68 5 false (6),
.last 19 (2,true),
.cycle 11 7 true (1),
.cycle 25 1 false (1),
.cycle 37 1 false (-1),
.last 23 (2,true),
.cycle 13 5 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 15 12 true (1),
.last 19 (2,true)
])
theorem kid22_part854_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part854) = true := by rfl

def kid22_part855 : Audit := .cycle 18 1 false (0)
theorem kid22_part855_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part855) = true := by rfl

def kid22_part856 : Audit := .cycle 14 1 false (-2)
theorem kid22_part856_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part856) = true := by rfl

def kid22_part857 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 0 19 true (0),
.last 13 (2,true),
.last 16 (2,true),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 21 1 false (-1),
.last 14 (2,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 21 (2,true),
.cycle 0 19 true (0),
.last 13 (2,true),
.last 16 (2,true),
.cycle 17 1 false (-1),
.cycle 17 3 true (3)
])
theorem kid22_part857_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part857) = true := by rfl

def kid22_part858 : Audit := .split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 98 9 false (6),
.last 16 (2,true),
.last 19 (2,true),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.cycle 11 5 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 33 1 false (3),
.cycle 40 1 false (0),
.cycle 1 17 true (1),
.cycle 6 19 true (2),
.last 20 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.cycle 25 1 false (-1),
.last 39 (2,true),
.cycle 11 5 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 27 13 false (3),
.cycle 1 17 true (1)
])
theorem kid22_part858_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part858) = true := by rfl

def kid22_part859 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 16 (5,true),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.cycle 3 10 true (1),
.last 16 (5,true),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.last 15 (5,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 1 13 true (1)
])
theorem kid22_part859_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part859) = true := by rfl

def kid22_part860 : Audit := .cycle 0 13 true (0)
theorem kid22_part860_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part860) = true := by rfl

def kid22_part861 : Audit := .cycle 4 7 true (1)
theorem kid22_part861_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part861) = true := by rfl

def kid22_part862 : Audit := .split 16 (5,true) (byMove [
.cycle 0 43 true (-1),
.cycle 51 3 false (5),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 19 5 true (2),
.last 18 (2,true),
.cycle 21 3 false (5),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 26 3 false (5),
.cycle 14 5 false (2),
.last 18 (2,true),
.last 23 (2,true),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 3 false (1),
.cycle 19 5 true (2),
.last 18 (2,true),
.cycle 39 34 true (0),
.cycle 27 3 false (5),
.cycle 17 3 false (1),
.cycle 21 7 true (2)
])
theorem kid22_part862_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part862) = true := by rfl

def kid22_part863 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 1 25 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 22 1 false (-2),
.cycle 15 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 35 true (1),
.cycle 3 10 true (1),
.cycle 44 1 false (0),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 20 (2,true),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 22 1 false (-2),
.cycle 17 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 27 13 false (3),
.cycle 13 1 true (5)
])
theorem kid22_part863_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part863) = true := by rfl

def kid22_part839 : Audit := .split 10 (5,false) (byMove [(kid22_part840),(kid22_part841),(kid22_part842),(kid22_part843),(kid22_part844),(kid22_part845),(kid22_part846),(kid22_part847),(kid22_part848),(kid22_part849),(kid22_part850),(kid22_part851),(kid22_part852),(kid22_part853),(kid22_part854),(kid22_part855),(kid22_part856),(kid22_part857),(kid22_part858),(kid22_part859),(kid22_part860),(kid22_part861),(kid22_part862),(kid22_part863)])

theorem kid22_part839_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part839) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part840),(kid22_part841),(kid22_part842),(kid22_part843),(kid22_part844),(kid22_part845),(kid22_part846),(kid22_part847),(kid22_part848),(kid22_part849),(kid22_part850),(kid22_part851),(kid22_part852),(kid22_part853),(kid22_part854),(kid22_part855),(kid22_part856),(kid22_part857),(kid22_part858),(kid22_part859),(kid22_part860),(kid22_part861),(kid22_part862),(kid22_part863)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part840_checked

  · exact kid22_part846_checked

  · exact kid22_part852_checked

  · exact kid22_part858_checked

  · exact kid22_part841_checked

  · exact kid22_part847_checked

  · exact kid22_part853_checked

  · exact kid22_part859_checked

  · exact kid22_part842_checked

  · exact kid22_part848_checked

  · exact kid22_part854_checked

  · exact kid22_part860_checked

  · exact kid22_part843_checked

  · exact kid22_part849_checked

  · exact kid22_part855_checked

  · exact kid22_part861_checked

  · exact kid22_part844_checked

  · exact kid22_part850_checked

  · exact kid22_part856_checked

  · exact kid22_part862_checked

  · exact kid22_part845_checked

  · exact kid22_part851_checked

  · exact kid22_part857_checked

  · exact kid22_part863_checked

def kid22_part864 : Audit := .cycle 1 10 true (1)
theorem kid22_part864_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part864) = true := by rfl

def kid22_part865 : Audit := .cycle 7 3 true (3)
theorem kid22_part865_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part865) = true := by rfl

def kid22_part866 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 31 1 false (5),
.cycle 11 8 true (0),
.cycle 16 1 false (0),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 12 8 true (0),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 26 true (0),
.cycle 31 1 false (5),
.cycle 19 1 false (1),
.cycle 11 1 true (3),
.cycle 6 12 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 12 8 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 10 14 true (0),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.cycle 31 1 false (5),
.last 18 (5,true),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (5,true),
.last 23 (5,true),
.last 20 (5,true),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
]),
.cycle 7 5 true (3),
.cycle 13 8 true (3),
.cycle 0 13 true (0),
.cycle 26 1 false (4),
.cycle 16 1 false (0),
.split 11 (5,false) (byMove [
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 25 1 false (1),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 9 20 true (0),
.last 12 (5,true),
.cycle 13 8 true (3),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 12 8 true (3),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.last 25 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 12 8 true (4),
.cycle 3 9 true (1),
.last 16 (5,true),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 12 8 true (4),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
])
theorem kid22_part866_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part866) = true := by rfl

def kid22_part867 : Audit := .cycle 0 11 true (0)
theorem kid22_part867_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part867) = true := by rfl

def kid22_part868 : Audit := .cycle 22 1 false (6)
theorem kid22_part868_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part868) = true := by rfl

def kid22_part870 : Audit := .cycle 0 11 true (0)
theorem kid22_part870_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part870) = true := by rfl

def kid22_part871 : Audit := .cycle 1 10 true (1)
theorem kid22_part871_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part871) = true := by rfl

def kid22_part872 : Audit := .cycle 31 1 false (5)
theorem kid22_part872_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part872) = true := by rfl

def kid22_part873 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.last 43 (2,true),
.cycle 42 1 false (8),
.cycle 11 8 true (0),
.cycle 24 1 false (2),
.cycle 18 1 true (4),
.last 51 (2,true),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 50 1 false (8),
.last 47 (2,true),
.cycle 30 1 false (4),
.cycle 18 1 true (4)
])
theorem kid22_part873_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part873) = true := by rfl

def kid22_part874 : Audit := .cycle 16 1 false (0)
theorem kid22_part874_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part874) = true := by rfl

def kid22_part875 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (4),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 26 true (0),
.cycle 31 1 false (5),
.cycle 19 1 false (1),
.cycle 11 1 true (3),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 27 1 false (3),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (3)
])
theorem kid22_part875_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part875) = true := by rfl

def kid22_part876 : Audit := .cycle 0 11 true (0)
theorem kid22_part876_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part876) = true := by rfl

def kid22_part877 : Audit := .cycle 1 10 true (1)
theorem kid22_part877_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part877) = true := by rfl

def kid22_part878 : Audit := .split 23 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048832, 256, 16777216, 128, 256, 32768, 524290, 1048580, 16777216, 128, 256, 2097152, 1024, 256, 16777216, 128, 256, 8, 131072, 256, 16777216, 16777216],[2, 1024, 256, 1, 32, 4, 8192, 1024, 256, 4096, 131072, 16384, 524288, 1024, 256, 262144, 8388608, 1048576, 2, 1024, 256, 1, 32, 4, 16777216],27412512⟩,
.cycle 0 27 true (0),
.cycle 25 10 true (2),
.cycle 33 1 false (5),
.cycle 29 1 false (3),
.last 24 (5,false),
.cycle 0 57 true (0),
.last 44 (5,false),
.cycle 11 14 true (0),
.cycle 0 25 true (0),
.last 25 (5,false),
.cycle 10 14 true (0),
.last 27 (5,false),
.cycle 26 10 true (4),
.cycle 0 63 true (0),
.cycle 24 10 true (2),
.cycle 29 1 false (3),
.last 24 (5,false),
.cycle 0 66 true (0),
.cycle 26 10 true (5),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.last 25 (5,false),
.last 33 (5,false)
])
theorem kid22_part878_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part878) = true := by rfl

def kid22_part879 : Audit := .cycle 0 22 true (0)
theorem kid22_part879_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part879) = true := by rfl

def kid22_part880 : Audit := .cycle 22 1 false (6)
theorem kid22_part880_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part880) = true := by rfl

def kid22_part881 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 56 1 false (10),
.cycle 31 1 false (5),
.cycle 22 1 false (4),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 10 14 true (0),
.cycle 26 1 false (8),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 47 1 false (9),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part881_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part881) = true := by rfl

def kid22_part882 : Audit := .cycle 7 5 true (3)
theorem kid22_part882_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part882) = true := by rfl

def kid22_part883 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 22 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,false),
.cycle 3 10 true (1),
.last 20 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 16 6 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
theorem kid22_part883_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part883) = true := by rfl

def kid22_part884 : Audit := .cycle 0 13 true (0)
theorem kid22_part884_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part884) = true := by rfl

def kid22_part885 : Audit := .cycle 26 1 false (4)
theorem kid22_part885_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part885) = true := by rfl

def kid22_part886 : Audit := .cycle 16 1 false (0)
theorem kid22_part886_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part886) = true := by rfl

def kid22_part887 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.last 22 (2,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 40 1 false (8),
.cycle 10 2 true (3),
.cycle 13 10 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 6 true (3),
.cycle 19 3 false (1)
])
theorem kid22_part887_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part887) = true := by rfl

def kid22_part888 : Audit := .cycle 0 11 true (0)
theorem kid22_part888_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part888) = true := by rfl

def kid22_part889 : Audit := .cycle 1 10 true (1)
theorem kid22_part889_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part889) = true := by rfl

def kid22_part890 : Audit := .cycle 2 9 true (1)
theorem kid22_part890_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part890) = true := by rfl

def kid22_part891 : Audit := .cycle 1 13 true (1)
theorem kid22_part891_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part891) = true := by rfl

def kid22_part892 : Audit := .cycle 8 3 true (3)
theorem kid22_part892_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part892) = true := by rfl

def kid22_part893 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 76 1 false (4),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 20 true (3),
.cycle 3 9 true (1),
.cycle 10 6 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.cycle 10 3 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part893_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part893) = true := by rfl

def kid22_part869 : Audit := .split 10 (5,true) (byMove [(kid22_part870),(kid22_part871),(kid22_part872),(kid22_part873),(kid22_part874),(kid22_part875),(kid22_part876),(kid22_part877),(kid22_part878),(kid22_part879),(kid22_part880),(kid22_part881),(kid22_part882),(kid22_part883),(kid22_part884),(kid22_part885),(kid22_part886),(kid22_part887),(kid22_part888),(kid22_part889),(kid22_part890),(kid22_part891),(kid22_part892),(kid22_part893)])

theorem kid22_part869_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part869) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid22_part870),(kid22_part871),(kid22_part872),(kid22_part873),(kid22_part874),(kid22_part875),(kid22_part876),(kid22_part877),(kid22_part878),(kid22_part879),(kid22_part880),(kid22_part881),(kid22_part882),(kid22_part883),(kid22_part884),(kid22_part885),(kid22_part886),(kid22_part887),(kid22_part888),(kid22_part889),(kid22_part890),(kid22_part891),(kid22_part892),(kid22_part893)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part870_checked

  · exact kid22_part876_checked

  · exact kid22_part882_checked

  · exact kid22_part888_checked

  · exact kid22_part871_checked

  · exact kid22_part877_checked

  · exact kid22_part883_checked

  · exact kid22_part889_checked

  · exact kid22_part872_checked

  · exact kid22_part878_checked

  · exact kid22_part884_checked

  · exact kid22_part890_checked

  · exact kid22_part873_checked

  · exact kid22_part879_checked

  · exact kid22_part885_checked

  · exact kid22_part891_checked

  · exact kid22_part874_checked

  · exact kid22_part880_checked

  · exact kid22_part886_checked

  · exact kid22_part892_checked

  · exact kid22_part875_checked

  · exact kid22_part881_checked

  · exact kid22_part887_checked

  · exact kid22_part893_checked

def kid22_part894 : Audit := .cycle 6 7 true (2)
theorem kid22_part894_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part894) = true := by rfl

def kid22_part895 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 19 2 true (0),
.cycle 25 1 false (1),
.cycle 16 2 true (3),
.cycle 15 2 true (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 19 2 true (3),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 16 2 true (3),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 18 2 true (2),
.cycle 20 1 false (0),
.last 13 (5,false),
.cycle 16 2 true (1),
.cycle 16 2 true (0),
.cycle 18 2 true (3),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 16 2 true (3),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 19 2 true (0),
.last 13 (5,false)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 20 2 true (4),
.cycle 0 13 true (0),
.cycle 17 2 true (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 19 2 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 20 2 true (4),
.cycle 18 2 true (4),
.cycle 9 11 true (1),
.last 13 (5,false),
.cycle 16 2 true (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 19 2 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.last 13 (5,false)
]),
.cycle 13 2 true (3),
.cycle 12 2 true (2),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 15 2 true (0),
.split 12 (5,true) (byMove [
.cycle 10 8 true (1),
.cycle 1 16 true (1),
.cycle 18 2 true (2),
.cycle 19 1 false (1),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 13 2 true (3),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.last 15 (5,false),
.cycle 14 2 true (2),
.cycle 16 2 true (0),
.cycle 5 9 true (1),
.cycle 16 2 true (2),
.cycle 18 1 false (-2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 13 2 true (3),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.cycle 13 2 true (2),
.last 15 (5,false)
]),
.cycle 1 12 true (1),
.cycle 14 2 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 12 2 true (3),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 15 2 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 13 2 true (2),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 2 true (5),
.cycle 3 10 true (1),
.cycle 15 2 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 13 2 true (3),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.cycle 13 2 true (2),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 14 2 true (3),
.last 13 (5,false)
])
])
theorem kid22_part895_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part895) = true := by rfl

def kid22_part896 : Audit := .cycle 1 12 true (1)
theorem kid22_part896_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part896) = true := by rfl

def kid22_part897 : Audit := .cycle 21 1 false (3)
theorem kid22_part897_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part897) = true := by rfl

def kid22_part898 : Audit := .cycle 13 1 false (-1)
theorem kid22_part898_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part898) = true := by rfl

def kid22_part900 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.last 17 (5,true),
.cycle 18 1 false (0),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.last 24 (5,true),
.cycle 0 15 true (0),
.cycle 24 17 true (2),
.last 14 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 22 (5,true),
.cycle 5 9 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid22_part900_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part900) = true := by rfl

def kid22_part901 : Audit := .cycle 1 14 true (1)
theorem kid22_part901_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part901) = true := by rfl

def kid22_part902 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 14 32 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.cycle 25 1 false (3),
.cycle 27 1 false (3),
.last 19 (2,true),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.cycle 23 1 false (5),
.cycle 15 8 true (1),
.last 20 (2,true),
.cycle 27 1 false (3),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.last 24 (2,true),
.cycle 17 7 true (2),
.last 19 (2,true),
.cycle 0 47 true (0),
.cycle 17 2 true (2),
.last 22 (2,true)
])
theorem kid22_part902_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part902) = true := by rfl

def kid22_part903 : Audit := .split 15 (2,true) (byMove [
.cycle 30 1 false (4),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.last 21 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 34 (5,true),
.last 24 (5,true),
.last 26 (5,true),
.cycle 0 17 true (0),
.last 23 (5,true),
.last 16 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 43 (5,true),
.last 19 (5,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid22_part903_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part903) = true := by rfl

def kid22_part904 : Audit := .cycle 14 1 false (-2)
theorem kid22_part904_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part904) = true := by rfl

def kid22_part905 : Audit := .split 12 (5,true) (byMove [
.last 25 (2,true),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 41 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 16 8 true (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 49 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part905_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part905) = true := by rfl

def kid22_part906 : Audit := .cycle 6 5 true (2)
theorem kid22_part906_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part906) = true := by rfl

def kid22_part907 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 16 (2,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 9 true (2),
.cycle 1 15 true (1),
.cycle 11 8 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 21 1 false (1),
.cycle 21 1 false (-1),
.cycle 10 4 true (2),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.cycle 1 15 true (1)
])
theorem kid22_part907_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part907) = true := by rfl

def kid22_part908 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 20 (5,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 24 (5,true),
.cycle 0 13 true (0),
.cycle 38 1 false (6),
.last 12 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 17 1 false (-1),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.last 15 (5,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid22_part908_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part908) = true := by rfl

def kid22_part909 : Audit := .cycle 1 12 true (1)
theorem kid22_part909_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part909) = true := by rfl

def kid22_part910 : Audit := .cycle 9 2 true (2)
theorem kid22_part910_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part910) = true := by rfl

def kid22_part911 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 true (3),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 38 1 false (6),
.cycle 13 1 true (5),
.cycle 11 8 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 11 7 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 2 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part911_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part911) = true := by rfl

def kid22_part912 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 29 true (-1),
.last 15 (2,true),
.cycle 59 1 false (3),
.cycle 17 1 false (-1),
.cycle 16 6 false (0),
.cycle 6 9 true (1),
.cycle 7 11 true (1),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 9 12 true (1),
.cycle 13 8 true (2),
.cycle 11 8 true (1),
.last 22 (2,true),
.last 15 (2,true),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 6 false (1),
.cycle 12 9 true (2),
.cycle 13 7 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 13 2 true (2),
.cycle 12 12 true (2)
])
theorem kid22_part912_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part912) = true := by rfl

def kid22_part913 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.last 16 (5,true),
.cycle 16 1 false (0),
.last 17 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 6 7 true (1),
.last 15 (5,true),
.last 25 (5,true),
.cycle 1 14 true (1),
.last 17 (5,true),
.last 13 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid22_part913_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part913) = true := by rfl

def kid22_part914 : Audit := .cycle 5 7 true (1)
theorem kid22_part914_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part914) = true := by rfl

def kid22_part915 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 12 30 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.last 17 (2,true),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.cycle 20 1 false (4),
.cycle 13 8 true (1),
.last 18 (2,true),
.cycle 24 1 false (2),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 23 22 true (3),
.cycle 15 7 true (2),
.last 17 (2,true),
.cycle 0 43 true (0),
.cycle 15 2 true (2),
.cycle 16 25 true (2)
])
theorem kid22_part915_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part915) = true := by rfl

def kid22_part916 : Audit := .cycle 14 1 false (-2)
theorem kid22_part916_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part916) = true := by rfl

def kid22_part917 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 23 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (3),
.cycle 25 1 false (3),
.last 13 (2,true),
.cycle 0 19 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (5),
.cycle 12 8 true (-1),
.last 14 (2,true),
.cycle 25 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 22 22 true (2),
.cycle 17 7 true (2),
.last 13 (2,true),
.cycle 0 19 true (0),
.cycle 12 2 true (0),
.cycle 15 3 true (3)
])
theorem kid22_part917_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part917) = true := by rfl

def kid22_part918 : Audit := .cycle 6 5 true (2)
theorem kid22_part918_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part918) = true := by rfl

def kid22_part919 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 35 true (-1),
.last 14 (2,true),
.cycle 47 1 false (3),
.cycle 26 1 false (-2),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 9 11 true (2),
.cycle 1 15 true (1),
.cycle 11 8 true (2),
.last 18 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 21 1 false (-1),
.cycle 19 5 false (1),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.cycle 1 15 true (1)
])
theorem kid22_part919_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part919) = true := by rfl

def kid22_part920 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 20 (5,true),
.cycle 25 1 false (1),
.last 17 (5,true),
.last 16 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 22 (5,true),
.cycle 0 13 true (0),
.last 18 (5,true),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 16 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 15 (5,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid22_part920_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part920) = true := by rfl

def kid22_part921 : Audit := .cycle 1 12 true (1)
theorem kid22_part921_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part921) = true := by rfl

def kid22_part922 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 22 1 false (2),
.last 17 (2,true),
.cycle 18 1 false (-2),
.cycle 15 6 false (1),
.cycle 6 7 true (2),
.cycle 7 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.cycle 8 8 true (2),
.cycle 11 8 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 19 1 false (1),
.cycle 18 1 false (-2),
.cycle 16 3 false (0),
.cycle 6 7 true (2),
.cycle 11 7 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 11 6 true (2)
])
theorem kid22_part922_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part922) = true := by rfl

def kid22_part923 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 31 true (-1),
.last 12 (2,true),
.cycle 43 1 false (3),
.cycle 17 1 false (-1),
.cycle 21 1 true (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 13 true (2),
.cycle 13 1 true (5),
.cycle 11 8 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 17 1 false (-1),
.cycle 15 3 false (1),
.cycle 1 12 true (1),
.cycle 11 7 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 2 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part923_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part923) = true := by rfl

def kid22_part899 : Audit := .split 10 (5,false) (byMove [(kid22_part900),(kid22_part901),(kid22_part902),(kid22_part903),(kid22_part904),(kid22_part905),(kid22_part906),(kid22_part907),(kid22_part908),(kid22_part909),(kid22_part910),(kid22_part911),(kid22_part912),(kid22_part913),(kid22_part914),(kid22_part915),(kid22_part916),(kid22_part917),(kid22_part918),(kid22_part919),(kid22_part920),(kid22_part921),(kid22_part922),(kid22_part923)])

theorem kid22_part899_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part899) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part900),(kid22_part901),(kid22_part902),(kid22_part903),(kid22_part904),(kid22_part905),(kid22_part906),(kid22_part907),(kid22_part908),(kid22_part909),(kid22_part910),(kid22_part911),(kid22_part912),(kid22_part913),(kid22_part914),(kid22_part915),(kid22_part916),(kid22_part917),(kid22_part918),(kid22_part919),(kid22_part920),(kid22_part921),(kid22_part922),(kid22_part923)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part900_checked

  · exact kid22_part906_checked

  · exact kid22_part912_checked

  · exact kid22_part918_checked

  · exact kid22_part901_checked

  · exact kid22_part907_checked

  · exact kid22_part913_checked

  · exact kid22_part919_checked

  · exact kid22_part902_checked

  · exact kid22_part908_checked

  · exact kid22_part914_checked

  · exact kid22_part920_checked

  · exact kid22_part903_checked

  · exact kid22_part909_checked

  · exact kid22_part915_checked

  · exact kid22_part921_checked

  · exact kid22_part904_checked

  · exact kid22_part910_checked

  · exact kid22_part916_checked

  · exact kid22_part922_checked

  · exact kid22_part905_checked

  · exact kid22_part911_checked

  · exact kid22_part917_checked

  · exact kid22_part923_checked

def kid22_part924 : Audit := .cycle 1 10 true (1)
theorem kid22_part924_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part924) = true := by rfl

def kid22_part925 : Audit := .cycle 7 3 true (3)
theorem kid22_part925_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part925) = true := by rfl

def kid22_part926 : Audit := .split 10 (2,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.cycle 2 18 true (0),
.cycle 0 12 true (0),
.cycle 2 10 true (1),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (0),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 26 true (0),
.cycle 31 1 false (5),
.cycle 19 1 false (1),
.last 12 (5,false),
.cycle 6 12 true (2),
.cycle 2 18 true (0),
.cycle 0 14 true (0),
.cycle 2 16 true (0),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 12 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 17 true (1),
.cycle 3 8 true (1),
.cycle 2 14 true (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (3),
.cycle 2 17 true (1),
.last 17 (5,true),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
]),
.cycle 6 5 true (2),
.cycle 2 11 true (1),
.cycle 1 14 true (1),
.cycle 1 12 true (1),
.cycle 9 2 true (3),
.split 11 (5,true) (byMove [
.cycle 10 8 true (2),
.cycle 0 15 true (0),
.last 23 (5,false),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 13 (5,false),
.cycle 2 13 true (1),
.cycle 16 4 true (0),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 16 (5,true),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
])
theorem kid22_part926_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part926) = true := by rfl

def kid22_part927 : Audit := .cycle 0 11 true (0)
theorem kid22_part927_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part927) = true := by rfl

def kid22_part928 : Audit := .cycle 8 3 true (3)
theorem kid22_part928_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part928) = true := by rfl

def kid22_part930 : Audit := .cycle 1 11 true (1)
theorem kid22_part930_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part930) = true := by rfl

def kid22_part931 : Audit := .cycle 7 4 true (3)
theorem kid22_part931_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part931) = true := by rfl

def kid22_part932 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (5,false),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 26 true (0),
.cycle 31 1 false (5),
.cycle 19 1 false (1),
.last 12 (5,false),
.cycle 6 12 true (2),
.last 16 (5,false),
.cycle 0 14 true (0),
.last 18 (5,false),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 12 (5,false)
])
theorem kid22_part932_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part932) = true := by rfl

def kid22_part933 : Audit := .cycle 0 12 true (0)
theorem kid22_part933_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part933) = true := by rfl

def kid22_part934 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 9 true (3),
.cycle 3 10 true (1),
.cycle 11 8 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4)
])
theorem kid22_part934_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part934) = true := by rfl

def kid22_part935 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 27 1 false (3),
.cycle 3 18 true (0),
.cycle 20 1 false (0),
.cycle 12 1 true (2),
.cycle 18 8 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 21 5 false (1),
.cycle 12 1 true (2)
])
theorem kid22_part935_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part935) = true := by rfl

def kid22_part936 : Audit := .cycle 0 11 true (0)
theorem kid22_part936_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part936) = true := by rfl

def kid22_part937 : Audit := .cycle 1 10 true (1)
theorem kid22_part937_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part937) = true := by rfl

def kid22_part938 : Audit := .split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (6),
.cycle 10 10 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.last 24 (2,true),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.cycle 17 3 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 9 11 true (3),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 19 1 true (7)
])
theorem kid22_part938_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part938) = true := by rfl

def kid22_part939 : Audit := .cycle 3 8 true (1)
theorem kid22_part939_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part939) = true := by rfl

def kid22_part940 : Audit := .split 16 (5,false) (byMove [
.cycle 1 17 true (1),
.cycle 7 10 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 15 2 true (5),
.cycle 9 14 true (3),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 15 9 true (5),
.cycle 3 14 true (1),
.cycle 11 6 true (3),
.cycle 16 1 true (6),
.cycle 6 11 true (2),
.cycle 15 3 true (5),
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 9 8 true (3),
.cycle 14 3 true (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 8 9 true (3),
.cycle 16 1 true (6)
])
theorem kid22_part940_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part940) = true := by rfl

def kid22_part941 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 19 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (3),
.cycle 3 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 29 1 false (7),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part941_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part941) = true := by rfl

def kid22_part942 : Audit := .cycle 6 5 true (2)
theorem kid22_part942_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part942) = true := by rfl

def kid22_part943 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 9 10 true (3),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 9 5 true (3),
.cycle 9 7 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part943_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part943) = true := by rfl

def kid22_part944 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 11 16 true (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 13 4 true (2),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 17 1 false (-1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.cycle 10 2 true (3)
])
theorem kid22_part944_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part944) = true := by rfl

def kid22_part945 : Audit := .cycle 1 12 true (1)
theorem kid22_part945_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part945) = true := by rfl

def kid22_part946 : Audit := .cycle 9 2 true (3)
theorem kid22_part946_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part946) = true := by rfl

def kid22_part947 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.last 17 (2,true),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 17 8 false (3),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 20 5 false (2),
.cycle 17 3 false (1)
])
theorem kid22_part947_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part947) = true := by rfl

def kid22_part948 : Audit := .cycle 0 11 true (0)
theorem kid22_part948_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part948) = true := by rfl

def kid22_part949 : Audit := .cycle 1 10 true (1)
theorem kid22_part949_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part949) = true := by rfl

def kid22_part950 : Audit := .cycle 2 9 true (1)
theorem kid22_part950_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part950) = true := by rfl

def kid22_part951 : Audit := .cycle 1 13 true (1)
theorem kid22_part951_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part951) = true := by rfl

def kid22_part952 : Audit := .cycle 8 3 true (3)
theorem kid22_part952_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part952) = true := by rfl

def kid22_part953 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 2 true (4),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 9 true (4),
.cycle 3 9 true (1),
.cycle 10 6 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 11 3 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 3 true (3),
.cycle 10 3 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part953_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part953) = true := by rfl

def kid22_part929 : Audit := .split 10 (5,true) (byMove [(kid22_part930),(kid22_part931),(kid22_part932),(kid22_part933),(kid22_part934),(kid22_part935),(kid22_part936),(kid22_part937),(kid22_part938),(kid22_part939),(kid22_part940),(kid22_part941),(kid22_part942),(kid22_part943),(kid22_part944),(kid22_part945),(kid22_part946),(kid22_part947),(kid22_part948),(kid22_part949),(kid22_part950),(kid22_part951),(kid22_part952),(kid22_part953)])

theorem kid22_part929_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part929) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid22_part930),(kid22_part931),(kid22_part932),(kid22_part933),(kid22_part934),(kid22_part935),(kid22_part936),(kid22_part937),(kid22_part938),(kid22_part939),(kid22_part940),(kid22_part941),(kid22_part942),(kid22_part943),(kid22_part944),(kid22_part945),(kid22_part946),(kid22_part947),(kid22_part948),(kid22_part949),(kid22_part950),(kid22_part951),(kid22_part952),(kid22_part953)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part930_checked

  · exact kid22_part936_checked

  · exact kid22_part942_checked

  · exact kid22_part948_checked

  · exact kid22_part931_checked

  · exact kid22_part937_checked

  · exact kid22_part943_checked

  · exact kid22_part949_checked

  · exact kid22_part932_checked

  · exact kid22_part938_checked

  · exact kid22_part944_checked

  · exact kid22_part950_checked

  · exact kid22_part933_checked

  · exact kid22_part939_checked

  · exact kid22_part945_checked

  · exact kid22_part951_checked

  · exact kid22_part934_checked

  · exact kid22_part940_checked

  · exact kid22_part946_checked

  · exact kid22_part952_checked

  · exact kid22_part935_checked

  · exact kid22_part941_checked

  · exact kid22_part947_checked

  · exact kid22_part953_checked

def kid22_part833 : Audit := .split 9 (4,true) (byMove [(kid22_part834),(kid22_part835),(kid22_part836),(kid22_part837),(kid22_part838),(kid22_part839),(kid22_part864),(kid22_part865),(kid22_part866),(kid22_part867),(kid22_part868),(kid22_part869),(kid22_part894),(kid22_part895),(kid22_part896),(kid22_part897),(kid22_part898),(kid22_part899),(kid22_part924),(kid22_part925),(kid22_part926),(kid22_part927),(kid22_part928),(kid22_part929)])

theorem kid22_part833_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (kid22_part833) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) 9 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid22_part834),(kid22_part835),(kid22_part836),(kid22_part837),(kid22_part838),(kid22_part839),(kid22_part864),(kid22_part865),(kid22_part866),(kid22_part867),(kid22_part868),(kid22_part869),(kid22_part894),(kid22_part895),(kid22_part896),(kid22_part897),(kid22_part898),(kid22_part899),(kid22_part924),(kid22_part925),(kid22_part926),(kid22_part927),(kid22_part928),(kid22_part929)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part834_checked

  · exact kid22_part864_checked

  · exact kid22_part894_checked

  · exact kid22_part924_checked

  · exact kid22_part835_checked

  · exact kid22_part865_checked

  · exact kid22_part895_checked

  · exact kid22_part925_checked

  · exact kid22_part836_checked

  · exact kid22_part866_checked

  · exact kid22_part896_checked

  · exact kid22_part926_checked

  · exact kid22_part837_checked

  · exact kid22_part867_checked

  · exact kid22_part897_checked

  · exact kid22_part927_checked

  · exact kid22_part838_checked

  · exact kid22_part868_checked

  · exact kid22_part898_checked

  · exact kid22_part928_checked

  · exact kid22_part839_checked

  · exact kid22_part869_checked

  · exact kid22_part899_checked

  · exact kid22_part929_checked

def kid22_part956 : Audit := .cycle 1 13 true (1)
theorem kid22_part956_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part956) = true := by rfl

def kid22_part957 : Audit := .cycle 7 12 true (2)
theorem kid22_part957_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part957) = true := by rfl

def kid22_part958 : Audit := .cycle 29 1 false (1)
theorem kid22_part958_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part958) = true := by rfl

def kid22_part959 : Audit := .cycle 0 14 true (0)
theorem kid22_part959_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part959) = true := by rfl

def kid22_part960 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 34 7 false (3),
.last 23 (5,false),
.cycle 0 15 true (0),
.last 23 (5,false),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 13 8 true (2),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 13 2 true (2),
.last 23 (5,false),
.cycle 1 15 true (1),
.last 23 (5,false),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.last 14 (5,false)
])
theorem kid22_part960_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part960) = true := by rfl

def kid22_part961 : Audit := .cycle 1 14 true (1)
theorem kid22_part961_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part961) = true := by rfl

def kid22_part962 : Audit := .cycle 0 13 true (0)
theorem kid22_part962_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part962) = true := by rfl

def kid22_part963 : Audit := .cycle 1 12 true (1)
theorem kid22_part963_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part963) = true := by rfl

def kid22_part964 : Audit := .split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 1 35 true (1),
.cycle 0 22 true (0),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 13 8 true (3),
.cycle 3 18 true (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.cycle 64 1 false (12),
.cycle 1 22 true (1),
.last 23 (5,false),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 11 13 true (3),
.last 21 (5,false)
])
theorem kid22_part964_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part964) = true := by rfl

def kid22_part965 : Audit := .cycle 3 10 true (1)
theorem kid22_part965_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part965) = true := by rfl

def kid22_part966 : Audit := .split 14 (5,false) (byMove [
.cycle 11 5 true (3),
.last 21 (4,true),
.last 27 (4,true),
.cycle 11 10 true (3),
.last 15 (4,true),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 16 true (0),
.last 17 (4,true),
.last 16 (4,true),
.last 16 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 19 (4,true),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (1)
])
theorem kid22_part966_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part966) = true := by rfl

def kid22_part967 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.cycle 1 16 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 22 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.cycle 13 1 true (5),
.cycle 11 8 true (3),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 0 20 true (0),
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5)
])
theorem kid22_part967_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part967) = true := by rfl

def kid22_part968 : Audit := .cycle 6 7 true (2)
theorem kid22_part968_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part968) = true := by rfl

def kid22_part969 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 16 true (2),
.cycle 23 5 false (1),
.cycle 0 16 true (0),
.last 27 (5,false),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (3),
.cycle 3 12 true (1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 13 2 true (3),
.cycle 23 5 false (1),
.cycle 1 16 true (1),
.last 27 (5,false),
.cycle 9 12 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 7 true (3),
.last 15 (5,false)
])
theorem kid22_part969_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part969) = true := by rfl

def kid22_part970 : Audit := .cycle 5 11 true (1)
theorem kid22_part970_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part970) = true := by rfl

def kid22_part971 : Audit := .cycle 1 14 true (1)
theorem kid22_part971_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part971) = true := by rfl

def kid22_part972 : Audit := .split 13 (4,true) (byMove [
.cycle 10 8 true (2),
.cycle 32 34 true (0),
.last 23 (5,false),
.cycle 44 1 false (4),
.last 23 (5,false),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 30 (5,false),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 6 11 true (2),
.cycle 13 2 true (2),
.last 23 (5,false),
.cycle 5 9 true (1),
.last 23 (5,false),
.last 24 (5,false),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 11 7 true (3),
.cycle 1 15 true (1)
])
theorem kid22_part972_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part972) = true := by rfl

def kid22_part973 : Audit := .cycle 9 8 true (2)
theorem kid22_part973_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part973) = true := by rfl

def kid22_part974 : Audit := .cycle 0 13 true (0)
theorem kid22_part974_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part974) = true := by rfl

def kid22_part975 : Audit := .cycle 1 12 true (1)
theorem kid22_part975_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part975) = true := by rfl

def kid22_part976 : Audit := .cycle 2 11 true (1)
theorem kid22_part976_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part976) = true := by rfl

def kid22_part977 : Audit := .cycle 1 15 true (1)
theorem kid22_part977_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part977) = true := by rfl

def kid22_part978 : Audit := .cycle 11 5 true (3)
theorem kid22_part978_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part978) = true := by rfl

def kid22_part979 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 12 2 true (4),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 11 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 6 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part979_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part979) = true := by rfl

def kid22_part955 : Audit := .split 12 (2,true) (byMove [(kid22_part956),(kid22_part957),(kid22_part958),(kid22_part959),(kid22_part960),(kid22_part961),(kid22_part962),(kid22_part963),(kid22_part964),(kid22_part965),(kid22_part966),(kid22_part967),(kid22_part968),(kid22_part969),(kid22_part970),(kid22_part971),(kid22_part972),(kid22_part973),(kid22_part974),(kid22_part975),(kid22_part976),(kid22_part977),(kid22_part978),(kid22_part979)])

theorem kid22_part955_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part955) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid22_part956),(kid22_part957),(kid22_part958),(kid22_part959),(kid22_part960),(kid22_part961),(kid22_part962),(kid22_part963),(kid22_part964),(kid22_part965),(kid22_part966),(kid22_part967),(kid22_part968),(kid22_part969),(kid22_part970),(kid22_part971),(kid22_part972),(kid22_part973),(kid22_part974),(kid22_part975),(kid22_part976),(kid22_part977),(kid22_part978),(kid22_part979)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part956_checked

  · exact kid22_part962_checked

  · exact kid22_part968_checked

  · exact kid22_part974_checked

  · exact kid22_part957_checked

  · exact kid22_part963_checked

  · exact kid22_part969_checked

  · exact kid22_part975_checked

  · exact kid22_part958_checked

  · exact kid22_part964_checked

  · exact kid22_part970_checked

  · exact kid22_part976_checked

  · exact kid22_part959_checked

  · exact kid22_part965_checked

  · exact kid22_part971_checked

  · exact kid22_part977_checked

  · exact kid22_part960_checked

  · exact kid22_part966_checked

  · exact kid22_part972_checked

  · exact kid22_part978_checked

  · exact kid22_part961_checked

  · exact kid22_part967_checked

  · exact kid22_part973_checked

  · exact kid22_part979_checked

def kid22_part980 : Audit := .cycle 0 13 true (0)
theorem kid22_part980_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part980) = true := by rfl

def kid22_part982 : Audit := .split 20 (2,true) (byMove [
.cycle 32 1 false (6),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 63 1 false (11),
.cycle 40 1 false (8),
.cycle 29 1 false (5),
.last 22 (5,false),
.last 21 (5,false),
.cycle 26 1 false (4),
.cycle 34 1 false (6),
.cycle 35 1 false (7),
.cycle 33 1 false (7),
.cycle 17 8 true (2),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 27 1 false (3),
.last 21 (5,false)
])
theorem kid22_part982_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part982) = true := by rfl

def kid22_part983 : Audit := .cycle 22 1 false (2)
theorem kid22_part983_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part983) = true := by rfl

def kid22_part984 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 18 5 true (2),
.cycle 63 1 false (11),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.last 20 (5,false),
.last 19 (5,false),
.cycle 18 5 false (3),
.cycle 16 5 false (3),
.cycle 18 7 true (1),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 18 5 true (2),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 19 (5,false)
])
theorem kid22_part984_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part984) = true := by rfl

def kid22_part985 : Audit := .split 23 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 33 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.last 25 (5,false),
.last 24 (5,false),
.cycle 19 5 true (3),
.cycle 0 49 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 25 (5,false),
.last 24 (5,false),
.cycle 19 5 false (5),
.cycle 0 35 true (0),
.cycle 18 7 true (2),
.cycle 24 1 false (2),
.last 25 (5,false),
.last 24 (5,false),
.cycle 19 5 true (3),
.cycle 1 25 true (0),
.cycle 0 26 true (0),
.cycle 31 1 false (5),
.cycle 27 1 false (3),
.last 24 (5,false)
])
theorem kid22_part985_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part985) = true := by rfl

def kid22_part986 : Audit := .split 20 (5,false) (byMove [
.last 23 (2,true),
.last 26 (2,true),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 25 true (0),
.cycle 25 1 false (1),
.last 21 (2,true),
.last 24 (2,true),
.cycle 18 3 false (2),
.cycle 23 1 false (1),
.cycle 17 7 false (3),
.last 22 (2,true),
.cycle 0 27 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 25 true (0),
.last 24 (2,true),
.last 21 (2,true),
.last 24 (2,true),
.cycle 17 4 false (3),
.last 22 (2,true)
])
theorem kid22_part986_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part986) = true := by rfl

def kid22_part987 : Audit := .cycle 20 1 false (2)
theorem kid22_part987_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part987) = true := by rfl

def kid22_part988 : Audit := .cycle 0 41 true (0)
theorem kid22_part988_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part988) = true := by rfl

def kid22_part989 : Audit := .cycle 26 20 true (4)
theorem kid22_part989_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part989) = true := by rfl

def kid22_part990 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 22 1 false (2),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 39 8 true (7),
.cycle 11 10 true (0),
.cycle 19 8 true (2),
.last 20 (5,false),
.last 19 (5,false),
.cycle 29 1 false (3),
.cycle 21 8 true (3),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 36 true (0),
.cycle 5 38 true (0),
.cycle 22 8 true (2),
.last 19 (5,false)
])
theorem kid22_part990_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part990) = true := by rfl

def kid22_part991 : Audit := .cycle 0 19 true (0)
theorem kid22_part991_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part991) = true := by rfl

def kid22_part992 : Audit := .split 20 (5,false) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.last 30 (2,true),
.last 25 (2,true),
.cycle 24 1 false (2),
.cycle 24 1 false (2),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 1040, 2, 1, 8192, 16384, 8, 2, 16, 1, 8192, 16384, 8, 2, 262144, 1, 262144],[2, 1024, 262144, 1, 16, 1040, 2, 65536, 262144, 1, 16, 262144, 2, 65536, 262144, 1, 16, 262144, 262144],327680⟩,
.cycle 7 14 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 18 3 true (4),
.cycle 42 1 false (6),
.cycle 22 5 true (4),
.last 22 (2,true),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 3, 2, 3],[128, 256, 8, 65552, 2, 1, 524288, 1048576, 32768, 2, 16, 16777216, 524288, 1048576, 8, 1024, 16777216, 1, 524288, 1048576, 32768, 2, 16842752, 16777216, 16777216],[2, 1024, 16777216, 1, 16, 65552, 8192, 4194304, 16777216, 4096, 65536, 16777216, 2, 4194304, 16777216, 1, 16, 1024, 8192, 4194304, 16777216, 4096, 65536, 16777216, 16777216],29444108⟩,
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 24 1 false (2),
.cycle 17 23 true (3),
.last 24 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 18 3 true (4),
.last 22 (2,true)
])
theorem kid22_part992_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part992) = true := by rfl

def kid22_part993 : Audit := .cycle 28 1 false (4)
theorem kid22_part993_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part993) = true := by rfl

def kid22_part994 : Audit := .cycle 26 1 false (4)
theorem kid22_part994_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part994) = true := by rfl

def kid22_part995 : Audit := .cycle 16 2 true (2)
theorem kid22_part995_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part995) = true := by rfl

def kid22_part996 : Audit := .split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 32, 64, 64],[9, 5, 1, 9, 4, 4, 64],112⟩,
.cycle 14 32 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 24 1 false (4),
.cycle 26 1 false (4),
.cycle 22 1 false (6),
.cycle 31 1 false (7),
.cycle 33 1 false (7),
.cycle 21 1 false (3),
.cycle 15 8 true (1),
.cycle 16 5 false (3),
.cycle 26 1 false (4),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 27 24 true (3),
.cycle 1 27 true (0),
.cycle 2 19 true (0),
.cycle 0 47 true (0),
.cycle 17 2 true (2),
.last 21 (5,false)
])
theorem kid22_part996_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part996) = true := by rfl

def kid22_part997 : Audit := .cycle 24 1 false (4)
theorem kid22_part997_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part997) = true := by rfl

def kid22_part998 : Audit := .split 20 (5,false) (byMove [
.last 23 (2,true),
.cycle 53 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 15 6 true (0),
.cycle 16 5 false (3),
.last 21 (2,true),
.cycle 34 1 false (4),
.cycle 18 3 false (2),
.cycle 23 1 false (1),
.cycle 17 7 false (3),
.last 22 (2,true),
.cycle 14 8 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 28 1 false (0),
.cycle 17 6 false (3),
.last 21 (2,true),
.cycle 5 23 true (0),
.cycle 17 4 false (3),
.last 22 (2,true)
])
theorem kid22_part998_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part998) = true := by rfl

def kid22_part999 : Audit := .cycle 20 1 false (2)
theorem kid22_part999_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part999) = true := by rfl

def kid22_part1000 : Audit := .cycle 0 48 true (0)
theorem kid22_part1000_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part1000) = true := by rfl

def kid22_part1001 : Audit := .split 21 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (2),
.cycle 18 5 true (3),
.cycle 1 43 true (0),
.cycle 0 24 true (0),
.cycle 1 27 true (0),
.last 23 (5,false),
.last 22 (5,false),
.cycle 27 1 false (3),
.cycle 1 27 true (0),
.cycle 42 1 false (8),
.cycle 38 1 false (8),
.last 28 (5,false),
.cycle 24 1 false (2),
.cycle 18 5 true (3),
.cycle 1 23 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 28 1 false (2),
.last 22 (5,false)
])
theorem kid22_part1001_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part1001) = true := by rfl

def kid22_part1002 : Audit := .split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 32, 64, 64],[9, 13, 1, 9, 9, 4, 64],112⟩,
.cycle 2 29 true (0),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 2 18 true (0),
.last 21 (5,false),
.cycle 0 19 true (0),
.cycle 2 46 true (0),
.cycle 2 25 true (0),
.cycle 3 16 true (0),
.last 20 (5,false),
.last 19 (5,false),
.cycle 2 28 true (0),
.cycle 2 19 true (0),
.cycle 28 1 false (4),
.cycle 2 43 true (0),
.cycle 17 2 true (3),
.last 21 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 28 1 false (2),
.last 19 (5,false)
])
theorem kid22_part1002_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part1002) = true := by rfl

def kid22_part1003 : Audit := .cycle 0 19 true (0)
theorem kid22_part1003_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part1003) = true := by rfl

def kid22_part1004 : Audit := .split 21 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 27 true (0),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 19 5 true (3),
.cycle 17 25 true (3),
.cycle 0 24 true (0),
.cycle 31 1 false (5),
.last 23 (5,false),
.last 22 (5,false),
.cycle 27 1 false (3),
.cycle 21 7 false (4),
.cycle 42 1 false (8),
.cycle 38 1 false (8),
.last 28 (5,false),
.cycle 24 1 false (2),
.cycle 19 5 true (3),
.cycle 1 23 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.cycle 28 1 false (2),
.last 22 (5,false)
])
theorem kid22_part1004_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part1004) = true := by rfl

def kid22_part1005 : Audit := .split 19 (2,true) (byMove [
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.last 21 (5,false),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 19 22 true (2),
.last 28 (5,false),
.cycle 28 1 false (4),
.last 21 (5,false),
.last 20 (5,false),
.cycle 25 1 false (3),
.last 22 (5,false),
.cycle 34 1 false (6),
.cycle 32 1 false (6),
.last 24 (5,false),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.last 49 (5,false),
.cycle 26 1 false (2),
.last 20 (5,false)
])
theorem kid22_part1005_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part1005) = true := by rfl

def kid22_part981 : Audit := .split 17 (4,true) (byMove [(kid22_part982),(kid22_part983),(kid22_part984),(kid22_part985),(kid22_part986),(kid22_part987),(kid22_part988),(kid22_part989),(kid22_part990),(kid22_part991),(kid22_part992),(kid22_part993),(kid22_part994),(kid22_part995),(kid22_part996),(kid22_part997),(kid22_part998),(kid22_part999),(kid22_part1000),(kid22_part1001),(kid22_part1002),(kid22_part1003),(kid22_part1004),(kid22_part1005)])

theorem kid22_part981_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part981) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (4,true) (some mv)) (byMove [(kid22_part982),(kid22_part983),(kid22_part984),(kid22_part985),(kid22_part986),(kid22_part987),(kid22_part988),(kid22_part989),(kid22_part990),(kid22_part991),(kid22_part992),(kid22_part993),(kid22_part994),(kid22_part995),(kid22_part996),(kid22_part997),(kid22_part998),(kid22_part999),(kid22_part1000),(kid22_part1001),(kid22_part1002),(kid22_part1003),(kid22_part1004),(kid22_part1005)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part982_checked

  · exact kid22_part988_checked

  · exact kid22_part994_checked

  · exact kid22_part1000_checked

  · exact kid22_part983_checked

  · exact kid22_part989_checked

  · exact kid22_part995_checked

  · exact kid22_part1001_checked

  · exact kid22_part984_checked

  · exact kid22_part990_checked

  · exact kid22_part996_checked

  · exact kid22_part1002_checked

  · exact kid22_part985_checked

  · exact kid22_part991_checked

  · exact kid22_part997_checked

  · exact kid22_part1003_checked

  · exact kid22_part986_checked

  · exact kid22_part992_checked

  · exact kid22_part998_checked

  · exact kid22_part1004_checked

  · exact kid22_part987_checked

  · exact kid22_part993_checked

  · exact kid22_part999_checked

  · exact kid22_part1005_checked

def kid22_part1006 : Audit := .cycle 17 1 false (1)
theorem kid22_part1006_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part1006) = true := by rfl

def kid22_part1008 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.last 26 (4,true),
.cycle 17 1 false (1),
.cycle 0 20 true (0),
.last 15 (4,true),
.last 22 (4,true),
.last 19 (4,true),
.cycle 13 16 true (1),
.cycle 0 17 true (0),
.last 20 (4,true),
.last 20 (4,true),
.cycle 0 20 true (0),
.cycle 17 11 false (3),
.last 16 (4,true),
.cycle 29 13 false (8),
.cycle 13 20 true (1),
.last 15 (4,true),
.last 22 (4,true),
.last 19 (4,true),
.cycle 1 16 true (0),
.cycle 0 17 true (0),
.cycle 4 11 true (0),
.last 17 (4,true),
.cycle 13 20 true (1)
])
theorem kid22_part1008_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1008) = true := by rfl

def kid22_part1009 : Audit := .split 22 (4,true) (byMove [
.last 75 (2,true),
.cycle 67 21 true (0),
.last 23 (2,true),
.last 26 (2,true),
.cycle 10 15 false (2),
.cycle 1 25 false (4),
.cycle 22 5 true (2),
.last 24 (2,true),
.cycle 0 25 true (-3),
.cycle 29 29 true (2),
.cycle 60 25 true (3),
.last 54 (2,true),
.cycle 8 19 false (4),
.cycle 21 2 true (1),
.last 23 (2,true),
.last 26 (2,true),
.cycle 10 15 false (2),
.cycle 41 9 true (0),
.cycle 22 5 true (2),
.last 24 (2,true),
.last 50 (2,true),
.cycle 4 36 true (-3),
.cycle 8 21 false (4),
.cycle 7 27 false (4)
])
theorem kid22_part1009_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1009) = true := by rfl

def kid22_part1010 : Audit := .split 12 (2,true) (byMove [
.last 21 (4,true),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 17 (4,true),
.last 34 (4,true),
.last 19 (4,true),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 17 (4,true),
.last 16 (4,true),
.last 19 (4,true),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 17 (4,true),
.cycle 1 16 true (0),
.last 19 (4,true),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid22_part1010_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1010) = true := by rfl

def kid22_part1011 : Audit := .split 17 (4,true) (byMove [
.cycle 0 54 true (0),
.cycle 31 1 false (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 21 true (0),
.last 19 (2,true),
.cycle 32 1 false (4),
.cycle 18 1 false (2),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 13 5 false (3),
.last 19 (2,true),
.last 23 (2,true),
.cycle 18 1 false (0),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 21 true (0),
.last 19 (2,true),
.cycle 0 48 true (0),
.cycle 46 1 false (2),
.cycle 22 1 false (-2),
.cycle 0 25 true (0)
])
theorem kid22_part1011_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1011) = true := by rfl

def kid22_part1012 : Audit := .split 12 (4,true) (byMove [
.cycle 0 26 true (-1),
.cycle 24 2 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 21 true (0),
.last 14 (2,true),
.cycle 0 22 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 12 5 false (1),
.last 14 (2,true),
.last 25 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 21 true (0),
.last 14 (2,true),
.cycle 0 22 true (0),
.cycle 19 2 false (1),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part1012_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1012) = true := by rfl

def kid22_part1013 : Audit := .cycle 14 1 false (-2)
theorem kid22_part1013_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1013) = true := by rfl

def kid22_part1014 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.last 23 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 18 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 3 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 6 9 true (1),
.last 16 (4,true),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 9 6 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 17 (4,true),
.cycle 0 16 true (0)
])
theorem kid22_part1014_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1014) = true := by rfl

def kid22_part1015 : Audit := .cycle 15 5 false (1)
theorem kid22_part1015_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1015) = true := by rfl

def kid22_part1016 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 20 (4,true),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 15 3 false (-1),
.last 21 (4,true),
.last 17 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 19 (4,true),
.last 16 (4,true),
.last 27 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 19 (4,true),
.cycle 22 1 false (0),
.cycle 15 3 false (-1),
.cycle 11 2 true (1),
.last 17 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 15 5 false (1),
.last 23 (4,true)
])
theorem kid22_part1016_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1016) = true := by rfl

def kid22_part1017 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 7 19 true (1),
.last 26 (2,true),
.cycle 33 1 false (1),
.last 23 (2,true),
.cycle 0 34 true (0),
.cycle 13 5 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 61 true (0),
.cycle 1 21 true (1),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 1, 8, 128, 256, 8, 2, 1024, 8, 4096],[2, 1024, 4096, 1, 1024, 1152, 2, 1024, 4096, 1, 1024, 1024, 4096],4096⟩,
.last 19 (2,true),
.cycle 12 7 true (2),
.last 27 (2,true),
.last 23 (2,true),
.cycle 11 7 true (1),
.cycle 13 5 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 1, 8, 128, 256, 8, 2, 1024, 8, 4096],[2, 1024, 4096, 1, 1024, 1152, 2, 1024, 4096, 1, 1024, 1024, 4096],4096⟩,
.cycle 0 20 true (0)
])
theorem kid22_part1017_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1017) = true := by rfl

def kid22_part1018 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 7 14 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 15 3 false (-1),
.cycle 10 4 true (1),
.cycle 12 5 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.cycle 16 3 true (4),
.cycle 13 4 true (3),
.cycle 24 5 false (1),
.last 14 (2,true),
.cycle 12 7 true (1),
.cycle 22 1 false (0),
.cycle 15 3 false (-1),
.cycle 11 2 true (1),
.cycle 12 5 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 15 5 false (1),
.cycle 13 4 true (3)
])
theorem kid22_part1018_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1018) = true := by rfl

def kid22_part1019 : Audit := .cycle 14 3 false (0)
theorem kid22_part1019_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1019) = true := by rfl

def kid22_part1020 : Audit := .split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 12 20 false (2),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 7 false (2),
.cycle 21 6 false (-1),
.cycle 14 5 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 13 18 true (1),
.cycle 24 5 true (4),
.cycle 14 10 true (2),
.cycle 17 11 false (3),
.cycle 13 2 true (1),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 7 false (2),
.cycle 17 6 false (0),
.cycle 14 5 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 4 11 true (0),
.cycle 14 13 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩
])
theorem kid22_part1020_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1020) = true := by rfl

def kid22_part1021 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.last 20 (2,true),
.last 14 (2,true),
.cycle 20 1 false (0),
.last 18 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 14 (2,true),
.last 42 (2,true),
.last 18 (2,true),
.last 20 (2,true),
.last 24 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.last 22 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.last 14 (2,true),
.last 29 (2,true),
.last 26 (2,true),
.cycle 23 3 true (3)
])
theorem kid22_part1021_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1021) = true := by rfl

def kid22_part1022 : Audit := .split 12 (2,true) (byMove [
.cycle 0 23 true (-1),
.cycle 14 10 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 18 (4,true),
.cycle 0 41 true (-1),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 13 14 true (1),
.last 13 (4,true),
.cycle 0 44 true (-2),
.last 15 (4,true),
.last 16 (4,true),
.cycle 28 20 true (1),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.last 28 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 13 19 true (1),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid22_part1022_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1022) = true := by rfl

def kid22_part1023 : Audit := .cycle 19 1 false (-1)
theorem kid22_part1023_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1023) = true := by rfl

def kid22_part1024 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 17 2 false (1),
.last 16 (2,true),
.last 13 (2,true),
.last 16 (2,true),
.cycle 15 2 false (3),
.cycle 14 2 false (0),
.cycle 6 13 false (4),
.last 14 (2,true),
.cycle 19 2 false (1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 19 2 false (-1),
.last 16 (2,true),
.last 13 (2,true),
.last 16 (2,true),
.cycle 23 2 false (-1),
.cycle 11 4 true (0)
])
theorem kid22_part1024_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1024) = true := by rfl

def kid22_part1025 : Audit := .cycle 14 1 false (-2)
theorem kid22_part1025_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1025) = true := by rfl

def kid22_part1026 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.last 20 (4,true),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 3 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 6 9 true (1),
.last 16 (4,true),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 17 (4,true),
.cycle 0 16 true (0)
])
theorem kid22_part1026_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1026) = true := by rfl

def kid22_part1027 : Audit := .split 15 (4,true) (byMove [
.cycle 17 20 true (1),
.cycle 15 17 false (1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 16 6 false (0),
.last 29 (2,true),
.cycle 0 19 true (0),
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 0 23 true (0),
.cycle 20 10 true (4),
.cycle 1 19 true (1),
.cycle 22 5 false (1),
.cycle 15 2 true (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 6 false (1),
.cycle 18 5 false (0),
.cycle 0 19 true (0),
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 1 23 true (1),
.cycle 16 8 false (2),
.cycle 1 19 true (1)
])
theorem kid22_part1027_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1027) = true := by rfl

def kid22_part1028 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 13 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 18 (4,true),
.last 16 (4,true),
.cycle 2 14 true (1),
.cycle 17 7 false (1),
.last 14 (4,true),
.cycle 32 22 true (1),
.cycle 1 18 true (1),
.last 13 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (4,true),
.cycle 2 14 true (1)
])
theorem kid22_part1028_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1028) = true := by rfl

def kid22_part1029 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 7 19 true (1),
.last 32 (2,true),
.cycle 0 24 true (0),
.last 26 (2,true),
.last 23 (2,true),
.cycle 13 5 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 26 true (0),
.cycle 1 21 true (1),
.cycle 0 20 true (0),
.cycle 338 51 false (3),
.last 19 (2,true),
.cycle 12 7 true (2),
.cycle 1 31 true (1),
.last 26 (2,true),
.cycle 11 7 true (1),
.cycle 13 5 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 34 12 false (2),
.cycle 0 20 true (0)
])
theorem kid22_part1029_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1029) = true := by rfl

def kid22_part1030 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 24 6 false (2),
.last 13 (2,true),
.last 16 (2,true),
.cycle 13 4 false (1),
.cycle 17 4 false (-1),
.cycle 12 5 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 3 16 true (1),
.cycle 16 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 17 7 false (1),
.cycle 12 2 true (1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 13 4 false (1),
.cycle 15 4 false (0),
.cycle 12 5 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 15 8 false (2),
.cycle 12 6 true (2)
])
theorem kid22_part1030_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1030) = true := by rfl

def kid22_part1031 : Audit := .split 13 (4,true) (byMove [
.cycle 15 23 true (1),
.cycle 14 13 false (1),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 14 4 false (0),
.cycle 34 1 true (-4),
.last 16 (2,true),
.cycle 0 17 true (0),
.last 22 (2,true),
.cycle 25 1 false (1),
.cycle 10 4 true (1),
.cycle 18 1 true (4),
.cycle 20 5 false (0),
.cycle 13 2 true (0),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 14 4 false (0),
.cycle 16 3 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.last 18 (2,true),
.cycle 15 6 false (1),
.cycle 18 1 true (4)
])
theorem kid22_part1031_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1031) = true := by rfl

def kid22_part1007 : Audit := .split 11 (5,false) (byMove [(kid22_part1008),(kid22_part1009),(kid22_part1010),(kid22_part1011),(kid22_part1012),(kid22_part1013),(kid22_part1014),(kid22_part1015),(kid22_part1016),(kid22_part1017),(kid22_part1018),(kid22_part1019),(kid22_part1020),(kid22_part1021),(kid22_part1022),(kid22_part1023),(kid22_part1024),(kid22_part1025),(kid22_part1026),(kid22_part1027),(kid22_part1028),(kid22_part1029),(kid22_part1030),(kid22_part1031)])

theorem kid22_part1007_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part1007) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (5,false) (some mv)) (byMove [(kid22_part1008),(kid22_part1009),(kid22_part1010),(kid22_part1011),(kid22_part1012),(kid22_part1013),(kid22_part1014),(kid22_part1015),(kid22_part1016),(kid22_part1017),(kid22_part1018),(kid22_part1019),(kid22_part1020),(kid22_part1021),(kid22_part1022),(kid22_part1023),(kid22_part1024),(kid22_part1025),(kid22_part1026),(kid22_part1027),(kid22_part1028),(kid22_part1029),(kid22_part1030),(kid22_part1031)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1008_checked

  · exact kid22_part1014_checked

  · exact kid22_part1020_checked

  · exact kid22_part1026_checked

  · exact kid22_part1009_checked

  · exact kid22_part1015_checked

  · exact kid22_part1021_checked

  · exact kid22_part1027_checked

  · exact kid22_part1010_checked

  · exact kid22_part1016_checked

  · exact kid22_part1022_checked

  · exact kid22_part1028_checked

  · exact kid22_part1011_checked

  · exact kid22_part1017_checked

  · exact kid22_part1023_checked

  · exact kid22_part1029_checked

  · exact kid22_part1012_checked

  · exact kid22_part1018_checked

  · exact kid22_part1024_checked

  · exact kid22_part1030_checked

  · exact kid22_part1013_checked

  · exact kid22_part1019_checked

  · exact kid22_part1025_checked

  · exact kid22_part1031_checked

def kid22_part1033 : Audit := .cycle 0 15 true (0)
theorem kid22_part1033_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1033) = true := by rfl

def kid22_part1034 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (1),
.last 19 (2,true),
.cycle 0 20 true (0),
.last 42 (2,true),
.cycle 1 20 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 13 8 true (1),
.cycle 3 16 true (1),
.cycle 0 39 true (0),
.cycle 1 19 true (1),
.cycle 6 13 true (1),
.cycle 17 2 true (3),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 57 19 true (0),
.cycle 9 10 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 1025, 8, 128, 256, 8, 2, 1024, 1024, 4096],[2, 1024, 4096, 1, 1024, 1024, 2, 1024, 4096, 1, 1024, 1024, 4096],4096⟩,
.cycle 1 46 true (1)
])
theorem kid22_part1034_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1034) = true := by rfl

def kid22_part1035 : Audit := .cycle 21 1 false (1)
theorem kid22_part1035_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1035) = true := by rfl

def kid22_part1036 : Audit := .cycle 0 17 true (0)
theorem kid22_part1036_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1036) = true := by rfl

def kid22_part1037 : Audit := .cycle 13 2 false (-1)
theorem kid22_part1037_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1037) = true := by rfl

def kid22_part1038 : Audit := .cycle 13 1 false (-1)
theorem kid22_part1038_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1038) = true := by rfl

def kid22_part1039 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 12 8 true (2),
.last 29 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 0 23 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 27 (4,true),
.cycle 3 17 true (1),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 6 14 true (2),
.last 21 (4,true),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 14 6 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 0 29 true (0),
.cycle 0 21 true (0)
])
theorem kid22_part1039_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1039) = true := by rfl

def kid22_part1040 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 21 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 7 8 true (2),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 0 20 true (0),
.cycle 1 13 true (1)
])
theorem kid22_part1040_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1040) = true := by rfl

def kid22_part1041 : Audit := .cycle 0 13 true (0)
theorem kid22_part1041_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1041) = true := by rfl

def kid22_part1042 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 22 1 false (2),
.last 18 (2,true),
.cycle 25 1 false (3),
.last 24 (2,true),
.cycle 20 1 false (2),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.cycle 28 1 false (4),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 24 1 false (4),
.cycle 34 1 false (4),
.cycle 20 1 false (2),
.cycle 0 48 true (0),
.cycle 24 1 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 24 1 false (2),
.cycle 22 1 false (2)
])
theorem kid22_part1042_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1042) = true := by rfl

def kid22_part1043 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.last 22 (2,true),
.cycle 25 1 false (1),
.cycle 20 3 false (0),
.cycle 10 4 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 3 true (4),
.cycle 15 4 true (3),
.cycle 6 11 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 29 1 false (3),
.cycle 20 3 false (0),
.cycle 12 2 true (2),
.cycle 1 14 true (1),
.last 23 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 16 4 true (2)
])
theorem kid22_part1043_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1043) = true := by rfl

def kid22_part1044 : Audit := .cycle 13 1 true (3)
theorem kid22_part1044_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1044) = true := by rfl

def kid22_part1045 : Audit := .cycle 15 6 false (1)
theorem kid22_part1045_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1045) = true := by rfl

def kid22_part1046 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 16 6 false (0),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 13 (4,true),
.cycle 14 4 false (0),
.last 20 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 18 (4,true),
.last 16 (4,true),
.last 19 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 32 22 true (1),
.cycle 1 18 true (1),
.last 13 (4,true),
.cycle 14 4 false (0),
.last 39 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 15 6 false (1),
.last 15 (4,true)
])
theorem kid22_part1046_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1046) = true := by rfl

def kid22_part1047 : Audit := .split 23 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 14 10 true (1),
.last 33 (4,true),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 0 29 true (0),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.last 31 (4,true),
.cycle 3 21 true (1),
.last 27 (4,true),
.cycle 0 27 true (0),
.last 32 (4,true),
.last 25 (4,true),
.cycle 5 22 true (1),
.cycle 1 25 true (1),
.last 24 (4,true),
.cycle 16 8 true (1),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 0 35 true (0),
.cycle 0 33 true (0)
])
theorem kid22_part1047_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1047) = true := by rfl

def kid22_part1048 : Audit := .cycle 18 1 false (0)
theorem kid22_part1048_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1048) = true := by rfl

def kid22_part1049 : Audit := .cycle 13 2 false (-1)
theorem kid22_part1049_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1049) = true := by rfl

def kid22_part1050 : Audit := .cycle 13 1 false (-1)
theorem kid22_part1050_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1050) = true := by rfl

def kid22_part1051 : Audit := .cycle 0 22 true (0)
theorem kid22_part1051_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1051) = true := by rfl

def kid22_part1052 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 15 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.last 34 (4,true),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 0 19 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 25 (4,true),
.cycle 1 13 true (1)
])
theorem kid22_part1052_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1052) = true := by rfl

def kid22_part1053 : Audit := .cycle 0 13 true (0)
theorem kid22_part1053_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1053) = true := by rfl

def kid22_part1054 : Audit := .cycle 4 7 true (1)
theorem kid22_part1054_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1054) = true := by rfl

def kid22_part1055 : Audit := .cycle 16 3 false (0)
theorem kid22_part1055_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1055) = true := by rfl

def kid22_part1056 : Audit := .cycle 15 1 true (1)
theorem kid22_part1056_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1056) = true := by rfl

def kid22_part1032 : Audit := .split 10 (5,false) (byMove [(kid22_part1033),(kid22_part1034),(kid22_part1035),(kid22_part1036),(kid22_part1037),(kid22_part1038),(kid22_part1039),(kid22_part1040),(kid22_part1041),(kid22_part1042),(kid22_part1043),(kid22_part1044),(kid22_part1045),(kid22_part1046),(kid22_part1047),(kid22_part1048),(kid22_part1049),(kid22_part1050),(kid22_part1051),(kid22_part1052),(kid22_part1053),(kid22_part1054),(kid22_part1055),(kid22_part1056)])

theorem kid22_part1032_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part1032) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part1033),(kid22_part1034),(kid22_part1035),(kid22_part1036),(kid22_part1037),(kid22_part1038),(kid22_part1039),(kid22_part1040),(kid22_part1041),(kid22_part1042),(kid22_part1043),(kid22_part1044),(kid22_part1045),(kid22_part1046),(kid22_part1047),(kid22_part1048),(kid22_part1049),(kid22_part1050),(kid22_part1051),(kid22_part1052),(kid22_part1053),(kid22_part1054),(kid22_part1055),(kid22_part1056)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1033_checked

  · exact kid22_part1039_checked

  · exact kid22_part1045_checked

  · exact kid22_part1051_checked

  · exact kid22_part1034_checked

  · exact kid22_part1040_checked

  · exact kid22_part1046_checked

  · exact kid22_part1052_checked

  · exact kid22_part1035_checked

  · exact kid22_part1041_checked

  · exact kid22_part1047_checked

  · exact kid22_part1053_checked

  · exact kid22_part1036_checked

  · exact kid22_part1042_checked

  · exact kid22_part1048_checked

  · exact kid22_part1054_checked

  · exact kid22_part1037_checked

  · exact kid22_part1043_checked

  · exact kid22_part1049_checked

  · exact kid22_part1055_checked

  · exact kid22_part1038_checked

  · exact kid22_part1044_checked

  · exact kid22_part1050_checked

  · exact kid22_part1056_checked

def kid22_part1057 : Audit := .cycle 1 10 true (1)
theorem kid22_part1057_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part1057) = true := by rfl

def kid22_part1058 : Audit := .cycle 7 3 true (3)
theorem kid22_part1058_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part1058) = true := by rfl

def kid22_part1060 : Audit := .cycle 0 11 true (0)
theorem kid22_part1060_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part1060) = true := by rfl

def kid22_part1061 : Audit := .cycle 1 10 true (1)
theorem kid22_part1061_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part1061) = true := by rfl

def kid22_part1062 : Audit := .split 19 (4,true) (byMove [
.cycle 25 1 false (3),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 36 1 false (6),
.last 22 (5,false),
.cycle 0 23 true (0),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.cycle 31 1 false (5),
.cycle 0 21 true (0),
.last 22 (5,false),
.cycle 11 10 true (0),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.cycle 22 1 false (2),
.cycle 27 1 false (5),
.last 22 (5,false),
.cycle 23 1 false (3),
.cycle 0 54 true (0),
.cycle 2 22 true (0),
.cycle 24 1 false (2),
.cycle 0 21 true (0),
.cycle 2 22 true (0),
.last 29 (5,false)
])
theorem kid22_part1062_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part1062) = true := by rfl

def kid22_part1063 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 19 1 false (1),
.cycle 0 19 true (0),
.last 20 (5,false),
.cycle 20 1 false (4),
.cycle 0 18 true (0),
.cycle 48 1 false (6),
.cycle 11 8 true (0),
.cycle 26 1 false (4),
.last 19 (5,false),
.last 18 (5,false),
.cycle 23 1 false (3),
.cycle 16 2 true (2),
.cycle 19 1 false (1),
.cycle 30 1 false (6),
.last 20 (5,false),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 34 1 false (6),
.last 18 (5,false)
])
theorem kid22_part1063_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part1063) = true := by rfl

def kid22_part1064 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.last 19 (4,true),
.last 18 (4,true),
.cycle 16 2 false (0),
.cycle 16 1 false (2),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 23 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 26 9 false (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true)
])
theorem kid22_part1064_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part1064) = true := by rfl

def kid22_part1065 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 11 1 true (3),
.cycle 6 12 true (2),
.last 23 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (3)
])
theorem kid22_part1065_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part1065) = true := by rfl

def kid22_part1066 : Audit := .cycle 0 11 true (0)
theorem kid22_part1066_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part1066) = true := by rfl

def kid22_part1067 : Audit := .cycle 1 10 true (1)
theorem kid22_part1067_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part1067) = true := by rfl

def kid22_part1068 : Audit := .split 21 (4,true) (byMove [
.cycle 73 1 false (17),
.cycle 30 1 false (8),
.cycle 31 1 false (9),
.cycle 24 15 true (4),
.last 24 (5,false),
.cycle 31 1 false (9),
.cycle 0 25 true (0),
.cycle 36 26 true (6),
.cycle 10 14 true (0),
.cycle 44 30 true (4),
.last 26 (5,false),
.cycle 10 14 true (0),
.cycle 37 1 false (9),
.cycle 20 2 true (2),
.cycle 28 1 false (8),
.cycle 33 1 false (9),
.last 24 (5,false),
.cycle 28 1 false (8),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.cycle 2 53 true (0),
.cycle 5 17 true (0),
.cycle 23 13 true (5),
.last 55 (5,false)
])
theorem kid22_part1068_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part1068) = true := by rfl

def kid22_part1069 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 36 1 false (10),
.cycle 21 1 false (3),
.cycle 0 25 true (0),
.last 22 (5,false),
.cycle 34 1 false (10),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.cycle 0 22 true (0),
.cycle 0 49 true (0),
.last 23 (5,false),
.cycle 22 10 true (2),
.cycle 31 1 false (7),
.cycle 18 2 true (2),
.cycle 27 1 false (7),
.cycle 36 1 false (10),
.last 22 (5,false),
.cycle 34 1 false (10),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.cycle 0 22 true (0),
.cycle 20 28 true (3),
.cycle 21 10 true (4),
.last 29 (5,false)
])
theorem kid22_part1069_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part1069) = true := by rfl

def kid22_part1070 : Audit := .split 12 (5,false) (byMove [
.cycle 14 5 true (4),
.cycle 0 16 true (0),
.last 21 (4,true),
.last 19 (4,true),
.cycle 18 2 false (2),
.cycle 18 1 false (2),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 25 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 19 (4,true),
.last 18 (4,true),
.last 18 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true)
])
theorem kid22_part1070_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part1070) = true := by rfl

def kid22_part1071 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.cycle 18 1 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.last 14 (4,true),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 16 (4,true),
.cycle 22 1 false (6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1071_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part1071) = true := by rfl

def kid22_part1072 : Audit := .cycle 7 5 true (3)
theorem kid22_part1072_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part1072) = true := by rfl

def kid22_part1073 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 25 5 false (1),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 46 1 false (10),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (3),
.cycle 3 12 true (1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 13 2 true (3),
.cycle 25 5 false (1),
.cycle 1 16 true (1),
.last 17 (5,false),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.last 15 (5,false)
])
theorem kid22_part1073_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part1073) = true := by rfl

def kid22_part1074 : Audit := .cycle 0 13 true (0)
theorem kid22_part1074_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part1074) = true := by rfl

def kid22_part1075 : Audit := .split 17 (4,true) (byMove [
.cycle 33 1 false (7),
.cycle 22 1 false (2),
.cycle 19 1 false (1),
.cycle 31 1 false (5),
.last 20 (5,false),
.cycle 0 21 true (0),
.cycle 0 41 true (0),
.cycle 26 20 true (4),
.cycle 26 1 false (4),
.cycle 0 19 true (0),
.last 20 (5,false),
.cycle 11 10 true (0),
.cycle 26 1 false (4),
.cycle 16 2 true (2),
.cycle 19 1 false (1),
.cycle 24 1 false (4),
.last 20 (5,false),
.cycle 20 1 false (2),
.cycle 0 48 true (0),
.cycle 4 18 true (0),
.cycle 2 43 true (0),
.cycle 0 19 true (0),
.cycle 4 18 true (0),
.last 27 (5,false)
])
theorem kid22_part1075_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part1075) = true := by rfl

def kid22_part1076 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 1 16 true (1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 16 2 false (0),
.cycle 16 1 false (2),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 9 4 true (2),
.last 15 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 23 7 false (2)
])
theorem kid22_part1076_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part1076) = true := by rfl

def kid22_part1077 : Audit := .split 11 (5,false) (byMove [
.cycle 9 12 true (2),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 23 (4,true),
.last 14 (4,true),
.last 23 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 20 (4,true)
])
theorem kid22_part1077_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part1077) = true := by rfl

def kid22_part1078 : Audit := .cycle 0 11 true (0)
theorem kid22_part1078_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part1078) = true := by rfl

def kid22_part1079 : Audit := .cycle 1 10 true (1)
theorem kid22_part1079_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part1079) = true := by rfl

def kid22_part1080 : Audit := .cycle 2 9 true (1)
theorem kid22_part1080_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part1080) = true := by rfl

def kid22_part1081 : Audit := .cycle 1 13 true (1)
theorem kid22_part1081_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part1081) = true := by rfl

def kid22_part1082 : Audit := .cycle 8 3 true (3)
theorem kid22_part1082_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part1082) = true := by rfl

def kid22_part1083 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 23 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 13 (4,true),
.last 21 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1083_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part1083) = true := by rfl

def kid22_part1059 : Audit := .split 10 (2,true) (byMove [(kid22_part1060),(kid22_part1061),(kid22_part1062),(kid22_part1063),(kid22_part1064),(kid22_part1065),(kid22_part1066),(kid22_part1067),(kid22_part1068),(kid22_part1069),(kid22_part1070),(kid22_part1071),(kid22_part1072),(kid22_part1073),(kid22_part1074),(kid22_part1075),(kid22_part1076),(kid22_part1077),(kid22_part1078),(kid22_part1079),(kid22_part1080),(kid22_part1081),(kid22_part1082),(kid22_part1083)])

theorem kid22_part1059_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part1059) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid22_part1060),(kid22_part1061),(kid22_part1062),(kid22_part1063),(kid22_part1064),(kid22_part1065),(kid22_part1066),(kid22_part1067),(kid22_part1068),(kid22_part1069),(kid22_part1070),(kid22_part1071),(kid22_part1072),(kid22_part1073),(kid22_part1074),(kid22_part1075),(kid22_part1076),(kid22_part1077),(kid22_part1078),(kid22_part1079),(kid22_part1080),(kid22_part1081),(kid22_part1082),(kid22_part1083)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1060_checked

  · exact kid22_part1066_checked

  · exact kid22_part1072_checked

  · exact kid22_part1078_checked

  · exact kid22_part1061_checked

  · exact kid22_part1067_checked

  · exact kid22_part1073_checked

  · exact kid22_part1079_checked

  · exact kid22_part1062_checked

  · exact kid22_part1068_checked

  · exact kid22_part1074_checked

  · exact kid22_part1080_checked

  · exact kid22_part1063_checked

  · exact kid22_part1069_checked

  · exact kid22_part1075_checked

  · exact kid22_part1081_checked

  · exact kid22_part1064_checked

  · exact kid22_part1070_checked

  · exact kid22_part1076_checked

  · exact kid22_part1082_checked

  · exact kid22_part1065_checked

  · exact kid22_part1071_checked

  · exact kid22_part1077_checked

  · exact kid22_part1083_checked

def kid22_part1084 : Audit := .cycle 0 11 true (0)
theorem kid22_part1084_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part1084) = true := by rfl

def kid22_part1086 : Audit := .cycle 0 11 true (0)
theorem kid22_part1086_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part1086) = true := by rfl

def kid22_part1087 : Audit := .cycle 1 10 true (1)
theorem kid22_part1087_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part1087) = true := by rfl

def kid22_part1088 : Audit := .split 20 (2,true) (byMove [
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 36 1 false (6),
.cycle 70 1 false (12),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.last 22 (5,false),
.last 21 (5,false),
.cycle 49 1 false (5),
.cycle 18 5 false (3),
.cycle 38 1 false (6),
.cycle 21 1 false (1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 2 24 true (0),
.cycle 1 22 true (0),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 21 (5,false)
])
theorem kid22_part1088_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part1088) = true := by rfl

def kid22_part1089 : Audit := .cycle 0 19 true (0)
theorem kid22_part1089_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part1089) = true := by rfl

def kid22_part1090 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 24 1 false (0),
.last 17 (2,true),
.cycle 16 2 false (0),
.cycle 16 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 3 false (1),
.cycle 11 3 true (2),
.cycle 16 7 false (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 21 1 false (-1),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 26 9 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 17 4 false (1),
.cycle 11 3 true (2)
])
theorem kid22_part1090_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part1090) = true := by rfl

def kid22_part1091 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 36 1 false (8),
.cycle 10 4 true (3),
.cycle 11 1 true (3),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (3)
])
theorem kid22_part1091_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part1091) = true := by rfl

def kid22_part1092 : Audit := .cycle 0 11 true (0)
theorem kid22_part1092_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part1092) = true := by rfl

def kid22_part1093 : Audit := .cycle 1 10 true (1)
theorem kid22_part1093_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part1093) = true := by rfl

def kid22_part1094 : Audit := .split 22 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1284, 4096, 4096, 128, 256, 8, 2, 4, 4096, 4096],[2, 1024, 256, 1, 4, 16, 2, 1024, 256, 1, 4, 16, 4096],6192⟩,
.cycle 1 58 true (0),
.cycle 41 1 false (9),
.cycle 58 1 false (14),
.cycle 40 1 false (12),
.last 23 (5,false),
.cycle 41 8 true (7),
.cycle 23 8 true (5),
.cycle 11 14 true (0),
.cycle 0 57 true (0),
.last 26 (5,false),
.cycle 9 14 true (0),
.cycle 24 15 true (4),
.cycle 35 8 true (5),
.cycle 44 8 true (6),
.cycle 37 1 false (9),
.last 28 (5,false),
.last 23 (5,false),
.cycle 63 8 true (13),
.cycle 23 8 true (5),
.cycle 2 23 true (0),
.cycle 49 8 true (9),
.cycle 39 8 true (8),
.last 35 (5,false)
])
theorem kid22_part1094_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part1094) = true := by rfl

def kid22_part1095 : Audit := .cycle 0 49 true (0)
theorem kid22_part1095_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part1095) = true := by rfl

def kid22_part1096 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 46 (2,true),
.last 40 (2,true),
.cycle 18 2 false (2),
.cycle 18 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 3 true (4),
.cycle 14 5 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 48 1 false (8),
.cycle 22 2 false (6),
.cycle 23 1 false (5),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 3 true (4)
])
theorem kid22_part1096_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part1096) = true := by rfl

def kid22_part1097 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 56 1 false (10),
.last 27 (2,true),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 49 (2,true),
.cycle 0 28 true (0),
.cycle 10 4 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 47 1 false (9),
.cycle 22 2 false (6),
.cycle 22 1 false (6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1097_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part1097) = true := by rfl

def kid22_part1098 : Audit := .cycle 7 5 true (3)
theorem kid22_part1098_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part1098) = true := by rfl

def kid22_part1099 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 20 2 true (2),
.cycle 0 14 true (0),
.cycle 19 2 true (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 2 true (5),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 13 2 true (3),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 19 2 true (0),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
theorem kid22_part1099_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part1099) = true := by rfl

def kid22_part1100 : Audit := .cycle 0 13 true (0)
theorem kid22_part1100_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part1100) = true := by rfl

def kid22_part1101 : Audit := .cycle 24 1 false (4)
theorem kid22_part1101_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part1101) = true := by rfl

def kid22_part1102 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 24 1 false (0),
.last 17 (2,true),
.cycle 16 2 false (0),
.cycle 16 1 false (0),
.cycle 6 7 true (2),
.cycle 23 5 false (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 19 3 false (1),
.cycle 9 4 true (2),
.cycle 16 7 false (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 21 1 false (-1),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 6 7 true (2),
.cycle 19 6 false (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 17 4 false (1),
.cycle 23 7 false (2)
])
theorem kid22_part1102_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part1102) = true := by rfl

def kid22_part1103 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 11 3 true (3),
.cycle 9 12 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 15 2 false (-1),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 11 3 true (3)
])
theorem kid22_part1103_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part1103) = true := by rfl

def kid22_part1104 : Audit := .cycle 0 11 true (0)
theorem kid22_part1104_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part1104) = true := by rfl

def kid22_part1105 : Audit := .cycle 1 10 true (1)
theorem kid22_part1105_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part1105) = true := by rfl

def kid22_part1106 : Audit := .cycle 2 9 true (1)
theorem kid22_part1106_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part1106) = true := by rfl

def kid22_part1107 : Audit := .cycle 1 13 true (1)
theorem kid22_part1107_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part1107) = true := by rfl

def kid22_part1108 : Audit := .cycle 8 3 true (3)
theorem kid22_part1108_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part1108) = true := by rfl

def kid22_part1109 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 10 4 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 9 8 true (3),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1109_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part1109) = true := by rfl

def kid22_part1085 : Audit := .split 10 (4,true) (byMove [(kid22_part1086),(kid22_part1087),(kid22_part1088),(kid22_part1089),(kid22_part1090),(kid22_part1091),(kid22_part1092),(kid22_part1093),(kid22_part1094),(kid22_part1095),(kid22_part1096),(kid22_part1097),(kid22_part1098),(kid22_part1099),(kid22_part1100),(kid22_part1101),(kid22_part1102),(kid22_part1103),(kid22_part1104),(kid22_part1105),(kid22_part1106),(kid22_part1107),(kid22_part1108),(kid22_part1109)])

theorem kid22_part1085_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part1085) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid22_part1086),(kid22_part1087),(kid22_part1088),(kid22_part1089),(kid22_part1090),(kid22_part1091),(kid22_part1092),(kid22_part1093),(kid22_part1094),(kid22_part1095),(kid22_part1096),(kid22_part1097),(kid22_part1098),(kid22_part1099),(kid22_part1100),(kid22_part1101),(kid22_part1102),(kid22_part1103),(kid22_part1104),(kid22_part1105),(kid22_part1106),(kid22_part1107),(kid22_part1108),(kid22_part1109)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1086_checked

  · exact kid22_part1092_checked

  · exact kid22_part1098_checked

  · exact kid22_part1104_checked

  · exact kid22_part1087_checked

  · exact kid22_part1093_checked

  · exact kid22_part1099_checked

  · exact kid22_part1105_checked

  · exact kid22_part1088_checked

  · exact kid22_part1094_checked

  · exact kid22_part1100_checked

  · exact kid22_part1106_checked

  · exact kid22_part1089_checked

  · exact kid22_part1095_checked

  · exact kid22_part1101_checked

  · exact kid22_part1107_checked

  · exact kid22_part1090_checked

  · exact kid22_part1096_checked

  · exact kid22_part1102_checked

  · exact kid22_part1108_checked

  · exact kid22_part1091_checked

  · exact kid22_part1097_checked

  · exact kid22_part1103_checked

  · exact kid22_part1109_checked

def kid22_part1111 : Audit := .cycle 0 12 true (0)
theorem kid22_part1111_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1111) = true := by rfl

def kid22_part1112 : Audit := .cycle 1 11 true (1)
theorem kid22_part1112_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1112) = true := by rfl

def kid22_part1113 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 30 1 false (6),
.last 22 (2,true),
.cycle 0 27 true (0),
.cycle 26 1 false (0),
.cycle 25 1 false (3),
.cycle 6 16 true (0),
.cycle 46 14 true (8),
.last 22 (2,true),
.cycle 0 53 true (0),
.last 46 (2,true),
.cycle 56 1 false (10),
.cycle 35 1 false (7),
.cycle 20 2 true (2),
.last 22 (2,true),
.cycle 40 1 false (10),
.cycle 26 1 false (0),
.cycle 28 1 false (6),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 22 (2,true),
.cycle 22 30 true (3),
.cycle 23 12 true (4),
.last 34 (2,true)
])
theorem kid22_part1113_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1113) = true := by rfl

def kid22_part1114 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 26 1 false (4),
.last 20 (2,true),
.cycle 36 1 false (6),
.cycle 23 1 false (-1),
.cycle 22 1 false (2),
.cycle 0 45 true (0),
.cycle 30 22 true (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 27 (2,true),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 27 1 false (5),
.cycle 23 1 false (-1),
.cycle 24 1 false (4),
.cycle 0 54 true (0),
.cycle 3 22 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 3 22 true (0),
.cycle 0 59 true (0)
])
theorem kid22_part1114_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1114) = true := by rfl

def kid22_part1115 : Audit := .split 16 (4,true) (byMove [
.cycle 0 34 true (-1),
.cycle 29 2 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 29 2 false (3),
.last 18 (2,true),
.cycle 0 30 true (0),
.cycle 17 1 false (1),
.cycle 17 2 false (1),
.cycle 17 2 false (1),
.cycle 29 2 false (1),
.last 18 (2,true),
.cycle 31 2 false (3),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 13 16 true (0),
.last 18 (2,true),
.cycle 0 30 true (0),
.cycle 25 2 false (5),
.cycle 21 2 false (3),
.cycle 15 2 true (0)
])
theorem kid22_part1115_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1115) = true := by rfl

def kid22_part1116 : Audit := .cycle 17 1 false (1)
theorem kid22_part1116_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1116) = true := by rfl

def kid22_part1117 : Audit := .cycle 0 12 true (0)
theorem kid22_part1117_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1117) = true := by rfl

def kid22_part1118 : Audit := .cycle 1 11 true (1)
theorem kid22_part1118_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1118) = true := by rfl

def kid22_part1119 : Audit := .split 23 (4,true) (byMove [
.last 26 (2,true),
.cycle 34 1 false (10),
.last 24 (2,true),
.cycle 0 33 true (0),
.last 27 (2,true),
.last 26 (2,true),
.cycle 0 59 true (0),
.cycle 52 18 true (10),
.last 24 (2,true),
.cycle 0 81 true (0),
.last 30 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1056, 4096, 4, 128, 256, 8, 2, 32, 4, 4096],[2, 1024, 4096, 1, 32, 32, 2, 1024, 4096, 1, 32, 32, 4096],4112⟩,
.cycle 43 1 false (11),
.cycle 22 2 true (2),
.last 24 (2,true),
.cycle 46 1 false (14),
.last 27 (2,true),
.cycle 32 1 false (10),
.cycle 0 75 true (0),
.cycle 1 27 true (0),
.last 24 (2,true),
.cycle 29 31 true (6),
.cycle 25 16 true (5),
.cycle 9 17 true (0)
])
theorem kid22_part1119_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1119) = true := by rfl

def kid22_part1120 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 30 1 false (8),
.last 22 (2,true),
.cycle 24 15 true (4),
.last 28 (2,true),
.cycle 31 1 false (9),
.cycle 0 25 true (0),
.cycle 36 26 true (6),
.last 22 (2,true),
.cycle 44 30 true (4),
.cycle 0 28 true (0),
.cycle 9 14 true (0),
.cycle 37 1 false (9),
.cycle 20 2 true (2),
.last 22 (2,true),
.cycle 33 1 false (9),
.cycle 53 1 false (9),
.cycle 28 1 false (8),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 23 13 true (5),
.cycle 3 53 true (0)
])
theorem kid22_part1120_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1120) = true := by rfl

def kid22_part1121 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 26 (2,true),
.cycle 0 29 true (0),
.cycle 31 3 false (3),
.cycle 11 4 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 28 (2,true),
.cycle 0 87 true (0),
.cycle 12 3 true (5),
.cycle 11 4 true (5),
.cycle 7 9 true (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 38 1 false (8),
.cycle 36 3 false (8),
.cycle 13 2 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5)
])
theorem kid22_part1121_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1121) = true := by rfl

def kid22_part1122 : Audit := .cycle 11 1 true (5)
theorem kid22_part1122_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1122) = true := by rfl

def kid22_part1123 : Audit := .cycle 7 6 true (3)
theorem kid22_part1123_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1123) = true := by rfl

def kid22_part1124 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.last 17 (4,true),
.cycle 11 3 true (4),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 9 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.last 16 (4,true)
])
theorem kid22_part1124_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1124) = true := by rfl

def kid22_part1125 : Audit := .cycle 0 14 true (0)
theorem kid22_part1125_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1125) = true := by rfl

def kid22_part1126 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 27 1 false (5),
.last 20 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (2),
.cycle 6 14 true (0),
.cycle 42 12 true (8),
.last 20 (2,true),
.cycle 0 49 true (0),
.cycle 47 1 false (9),
.cycle 47 1 false (9),
.cycle 32 1 false (6),
.cycle 18 2 true (2),
.last 20 (2,true),
.cycle 37 1 false (9),
.cycle 23 1 false (-1),
.cycle 25 1 false (5),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 20 28 true (3),
.cycle 21 10 true (4),
.cycle 9 46 true (0)
])
theorem kid22_part1126_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1126) = true := by rfl

def kid22_part1127 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 42, 49, 64],[2, 16, 64, 1, 42, 32, 64],64⟩,
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 6 14 true (0),
.cycle 16 27 true (0),
.last 17 (2,true),
.cycle 0 22 true (0),
.cycle 22 2 false (6),
.cycle 22 2 false (6),
.cycle 54 2 false (8),
.last 18 (2,true),
.last 22 (2,true),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 66 true (0),
.cycle 18 10 true (2),
.last 17 (2,true),
.cycle 0 22 true (0),
.cycle 18 10 true (2),
.cycle 35 2 false (7)
])
theorem kid22_part1127_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1127) = true := by rfl

def kid22_part1128 : Audit := .cycle 22 1 false (6)
theorem kid22_part1128_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1128) = true := by rfl

def kid22_part1129 : Audit := .cycle 0 12 true (0)
theorem kid22_part1129_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1129) = true := by rfl

def kid22_part1130 : Audit := .cycle 1 11 true (1)
theorem kid22_part1130_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1130) = true := by rfl

def kid22_part1131 : Audit := .cycle 2 10 true (1)
theorem kid22_part1131_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1131) = true := by rfl

def kid22_part1132 : Audit := .cycle 1 14 true (1)
theorem kid22_part1132_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1132) = true := by rfl

def kid22_part1133 : Audit := .cycle 8 4 true (3)
theorem kid22_part1133_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1133) = true := by rfl

def kid22_part1134 : Audit := .cycle 11 1 true (5)
theorem kid22_part1134_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1134) = true := by rfl

def kid22_part1110 : Audit := .split 11 (5,false) (byMove [(kid22_part1111),(kid22_part1112),(kid22_part1113),(kid22_part1114),(kid22_part1115),(kid22_part1116),(kid22_part1117),(kid22_part1118),(kid22_part1119),(kid22_part1120),(kid22_part1121),(kid22_part1122),(kid22_part1123),(kid22_part1124),(kid22_part1125),(kid22_part1126),(kid22_part1127),(kid22_part1128),(kid22_part1129),(kid22_part1130),(kid22_part1131),(kid22_part1132),(kid22_part1133),(kid22_part1134)])

theorem kid22_part1110_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part1110) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part1111),(kid22_part1112),(kid22_part1113),(kid22_part1114),(kid22_part1115),(kid22_part1116),(kid22_part1117),(kid22_part1118),(kid22_part1119),(kid22_part1120),(kid22_part1121),(kid22_part1122),(kid22_part1123),(kid22_part1124),(kid22_part1125),(kid22_part1126),(kid22_part1127),(kid22_part1128),(kid22_part1129),(kid22_part1130),(kid22_part1131),(kid22_part1132),(kid22_part1133),(kid22_part1134)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1111_checked

  · exact kid22_part1117_checked

  · exact kid22_part1123_checked

  · exact kid22_part1129_checked

  · exact kid22_part1112_checked

  · exact kid22_part1118_checked

  · exact kid22_part1124_checked

  · exact kid22_part1130_checked

  · exact kid22_part1113_checked

  · exact kid22_part1119_checked

  · exact kid22_part1125_checked

  · exact kid22_part1131_checked

  · exact kid22_part1114_checked

  · exact kid22_part1120_checked

  · exact kid22_part1126_checked

  · exact kid22_part1132_checked

  · exact kid22_part1115_checked

  · exact kid22_part1121_checked

  · exact kid22_part1127_checked

  · exact kid22_part1133_checked

  · exact kid22_part1116_checked

  · exact kid22_part1122_checked

  · exact kid22_part1128_checked

  · exact kid22_part1134_checked

def kid22_part1136 : Audit := .cycle 1 13 true (1)
theorem kid22_part1136_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part1136) = true := by rfl

def kid22_part1137 : Audit := .cycle 7 12 true (2)
theorem kid22_part1137_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part1137) = true := by rfl

def kid22_part1138 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 34 7 false (3),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 29 1 false (1),
.last 23 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 55 1 false (9),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 21 5 false (1),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 24 (5,false),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.last 14 (5,false)
])
theorem kid22_part1138_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part1138) = true := by rfl

def kid22_part1139 : Audit := .cycle 0 14 true (0)
theorem kid22_part1139_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part1139) = true := by rfl

def kid22_part1140 : Audit := .split 23 (5,false) (byMove [
.last 26 (2,true),
.cycle 8 34 false (4),
.cycle 25 1 false (-3),
.cycle 24 1 false (-4),
.cycle 22 2 false (-2),
.cycle 23 1 false (-3),
.cycle 15 17 true (-3),
.cycle 15 10 false (1),
.last 24 (2,true),
.cycle 0 25 false (4),
.cycle 21 3 false (-1),
.cycle 20 11 false (0),
.cycle 17 7 false (1),
.last 25 (2,true),
.cycle 15 19 true (-4),
.cycle 24 1 false (-4),
.cycle 22 2 false (-2),
.cycle 23 1 false (-3),
.cycle 15 17 true (-3),
.cycle 20 9 false (0),
.last 24 (2,true),
.cycle 19 26 false (3),
.cycle 20 4 false (0),
.cycle 15 12 false (1)
])
theorem kid22_part1140_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part1140) = true := by rfl

def kid22_part1141 : Audit := .cycle 6 8 true (2)
theorem kid22_part1141_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part1141) = true := by rfl

def kid22_part1142 : Audit := .cycle 0 13 true (0)
theorem kid22_part1142_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part1142) = true := by rfl

def kid22_part1143 : Audit := .cycle 1 12 true (1)
theorem kid22_part1143_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part1143) = true := by rfl

def kid22_part1144 : Audit := .cycle 11 8 true (3)
theorem kid22_part1144_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part1144) = true := by rfl

def kid22_part1145 : Audit := .cycle 3 10 true (1)
theorem kid22_part1145_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part1145) = true := by rfl

def kid22_part1146 : Audit := .split 14 (5,false) (byMove [
.last 17 (2,true),
.cycle 0 27 true (0),
.last 15 (2,true),
.cycle 11 10 true (3),
.cycle 32 2 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 11 10 true (3),
.cycle 11 5 true (3),
.last 21 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 82 2 false (10),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 6 10 true (2)
])
theorem kid22_part1146_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part1146) = true := by rfl

def kid22_part1147 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 12 true (2),
.cycle 6 10 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 18 true (3),
.cycle 11 8 true (3),
.cycle 12 4 true (4),
.cycle 13 1 true (5),
.cycle 11 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 14 true (3),
.cycle 17 14 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5)
])
theorem kid22_part1147_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part1147) = true := by rfl

def kid22_part1148 : Audit := .cycle 6 7 true (2)
theorem kid22_part1148_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part1148) = true := by rfl

def kid22_part1149 : Audit := .cycle 11 2 true (3)
theorem kid22_part1149_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part1149) = true := by rfl

def kid22_part1150 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 0 70 true (0),
.cycle 29 1 false (1),
.cycle 31 1 false (1),
.last 26 (5,false),
.last 23 (5,false),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 48 1 false (10),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 11 9 true (3),
.cycle 10 8 true (2),
.cycle 21 5 false (1),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 5 11 true (1),
.last 24 (5,false),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.cycle 6 9 true (2)
])
theorem kid22_part1150_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part1150) = true := by rfl

def kid22_part1151 : Audit := .cycle 1 14 true (1)
theorem kid22_part1151_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part1151) = true := by rfl

def kid22_part1152 : Audit := .split 23 (5,false) (byMove [
.last 26 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 19, 27, 64],[2, 16, 64, 1, 18, 16, 64],64⟩,
.cycle 25 1 false (-3),
.cycle 24 1 false (-4),
.cycle 22 2 false (-2),
.cycle 23 1 false (-3),
.cycle 20 6 true (-3),
.cycle 20 5 false (0),
.last 24 (2,true),
.cycle 41 19 true (0),
.cycle 21 3 false (-1),
.cycle 16 8 false (1),
.cycle 17 7 false (1),
.last 25 (2,true),
.cycle 20 8 true (-4),
.cycle 24 1 false (-4),
.cycle 22 2 false (-2),
.cycle 23 1 false (-3),
.cycle 13 13 false (3),
.cycle 18 6 false (1),
.last 24 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 19, 8, 64],[2, 16, 64, 1, 18, 16, 64],64⟩,
.cycle 20 4 false (0),
.cycle 20 7 false (0)
])
theorem kid22_part1152_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part1152) = true := by rfl

def kid22_part1153 : Audit := .cycle 9 8 true (2)
theorem kid22_part1153_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part1153) = true := by rfl

def kid22_part1154 : Audit := .cycle 0 13 true (0)
theorem kid22_part1154_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part1154) = true := by rfl

def kid22_part1155 : Audit := .cycle 1 12 true (1)
theorem kid22_part1155_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part1155) = true := by rfl

def kid22_part1156 : Audit := .cycle 2 11 true (1)
theorem kid22_part1156_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part1156) = true := by rfl

def kid22_part1157 : Audit := .cycle 1 15 true (1)
theorem kid22_part1157_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part1157) = true := by rfl

def kid22_part1158 : Audit := .cycle 11 5 true (3)
theorem kid22_part1158_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part1158) = true := by rfl

def kid22_part1159 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 6 9 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 6 10 true (2),
.cycle 11 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 6 true (3),
.cycle 13 1 true (5)
])
theorem kid22_part1159_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part1159) = true := by rfl

def kid22_part1135 : Audit := .split 12 (4,true) (byMove [(kid22_part1136),(kid22_part1137),(kid22_part1138),(kid22_part1139),(kid22_part1140),(kid22_part1141),(kid22_part1142),(kid22_part1143),(kid22_part1144),(kid22_part1145),(kid22_part1146),(kid22_part1147),(kid22_part1148),(kid22_part1149),(kid22_part1150),(kid22_part1151),(kid22_part1152),(kid22_part1153),(kid22_part1154),(kid22_part1155),(kid22_part1156),(kid22_part1157),(kid22_part1158),(kid22_part1159)])

theorem kid22_part1135_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part1135) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (4,true) (some mv)) (byMove [(kid22_part1136),(kid22_part1137),(kid22_part1138),(kid22_part1139),(kid22_part1140),(kid22_part1141),(kid22_part1142),(kid22_part1143),(kid22_part1144),(kid22_part1145),(kid22_part1146),(kid22_part1147),(kid22_part1148),(kid22_part1149),(kid22_part1150),(kid22_part1151),(kid22_part1152),(kid22_part1153),(kid22_part1154),(kid22_part1155),(kid22_part1156),(kid22_part1157),(kid22_part1158),(kid22_part1159)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1136_checked

  · exact kid22_part1142_checked

  · exact kid22_part1148_checked

  · exact kid22_part1154_checked

  · exact kid22_part1137_checked

  · exact kid22_part1143_checked

  · exact kid22_part1149_checked

  · exact kid22_part1155_checked

  · exact kid22_part1138_checked

  · exact kid22_part1144_checked

  · exact kid22_part1150_checked

  · exact kid22_part1156_checked

  · exact kid22_part1139_checked

  · exact kid22_part1145_checked

  · exact kid22_part1151_checked

  · exact kid22_part1157_checked

  · exact kid22_part1140_checked

  · exact kid22_part1146_checked

  · exact kid22_part1152_checked

  · exact kid22_part1158_checked

  · exact kid22_part1141_checked

  · exact kid22_part1147_checked

  · exact kid22_part1153_checked

  · exact kid22_part1159_checked

def kid22_part1161 : Audit := .cycle 1 15 true (1)
theorem kid22_part1161_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part1161) = true := by rfl

def kid22_part1162 : Audit := .split 21 (4,true) (byMove [
.cycle 23 5 false (2),
.cycle 22 5 false (1),
.cycle 56 5 false (5),
.cycle 24 7 true (2),
.last 24 (5,false),
.cycle 22 5 false (0),
.cycle 0 25 true (0),
.cycle 32 30 true (2),
.cycle 1 70 true (0),
.cycle 48 42 true (0),
.last 26 (5,false),
.cycle 14 8 true (0),
.cycle 32 5 false (5),
.cycle 20 2 true (0),
.cycle 0 33 true (-1),
.cycle 28 5 false (5),
.last 24 (5,false),
.cycle 22 5 false (0),
.cycle 0 25 true (0),
.cycle 22 5 true (2),
.cycle 16 6 true (0),
.cycle 5 17 true (0),
.cycle 23 5 true (3),
.last 31 (5,false)
])
theorem kid22_part1162_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part1162) = true := by rfl

def kid22_part1163 : Audit := .cycle 25 1 false (1)
theorem kid22_part1163_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part1163) = true := by rfl

def kid22_part1164 : Audit := .split 18 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 14 14 true (2),
.cycle 37 1 false (1),
.cycle 12 7 true (2),
.last 21 (5,false),
.cycle 0 27 true (0),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 1 22 true (1),
.cycle 0 20 true (0),
.last 21 (5,false),
.cycle 0 23 true (0),
.cycle 6 16 true (2),
.cycle 17 2 true (3),
.cycle 47 1 false (3),
.cycle 5 14 true (1),
.last 21 (5,false),
.cycle 16 10 true (2),
.cycle 1 19 true (1),
.cycle 14 5 true (3),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 15 5 true (3),
.last 22 (5,false)
])
theorem kid22_part1164_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part1164) = true := by rfl

def kid22_part1165 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 7 14 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 19 (5,false),
.last 13 (5,false),
.cycle 1 19 true (1),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 19 true (1),
.cycle 15 2 true (0),
.last 23 (5,false),
.cycle 22 1 false (0),
.last 19 (5,false),
.last 13 (5,false),
.cycle 1 19 true (1),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 23 5 true (3),
.last 13 (5,false)
])
theorem kid22_part1165_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part1165) = true := by rfl

def kid22_part1166 : Audit := .split 17 (4,true) (byMove [
.cycle 36 3 false (6),
.cycle 20 3 false (0),
.last 19 (5,false),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 24 true (0),
.cycle 0 21 true (0),
.last 27 (5,false),
.cycle 24 3 false (2),
.last 19 (5,false),
.last 18 (5,false),
.cycle 21 3 false (1),
.cycle 16 2 true (0),
.last 19 (5,false),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 24 true (0),
.cycle 0 21 true (0),
.cycle 2 23 true (0),
.cycle 30 37 true (0),
.cycle 27 5 true (3),
.last 18 (5,false)
])
theorem kid22_part1166_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part1166) = true := by rfl

def kid22_part1167 : Audit := .cycle 1 12 true (1)
theorem kid22_part1167_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part1167) = true := by rfl

def kid22_part1168 : Audit := .cycle 7 5 true (2)
theorem kid22_part1168_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part1168) = true := by rfl

def kid22_part1169 : Audit := .split 21 (4,true) (byMove [
.cycle 1 33 true (1),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 32, 64, 64],[0, 2, 8, 0, 2, 2, 64],112⟩,
.cycle 0 25 true (0),
.cycle 20 7 true (4),
.last 24 (5,false),
.cycle 0 27 true (0),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 12 10 true (2),
.cycle 0 23 true (0),
.last 24 (5,false),
.last 33 (5,false),
.cycle 6 19 true (2),
.cycle 20 2 true (4),
.cycle 46 1 false (10),
.cycle 5 17 true (1),
.last 24 (5,false),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 32, 64, 64],[0, 2, 8, 0, 32, 2, 64],112⟩,
.cycle 1 22 true (1),
.cycle 20 5 true (4),
.cycle 2 29 true (1),
.cycle 0 23 true (0),
.cycle 20 5 true (4),
.last 25 (5,false)
])
theorem kid22_part1169_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part1169) = true := by rfl

def kid22_part1170 : Audit := .cycle 0 13 true (0)
theorem kid22_part1170_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part1170) = true := by rfl

def kid22_part1171 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 24 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,false),
.cycle 3 17 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 16 true (2),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 24 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.last 13 (5,false)
])
theorem kid22_part1171_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part1171) = true := by rfl

def kid22_part1172 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.last 19 (4,true),
.last 19 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 24 (4,true),
.last 22 (4,true),
.last 18 (4,true),
.cycle 15 1 true (5),
.last 21 (4,true),
.cycle 13 3 true (3),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 19 (4,true),
.last 19 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 8 8 true (2),
.cycle 15 1 true (5)
])
theorem kid22_part1172_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part1172) = true := by rfl

def kid22_part1173 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 37 7 false (2),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 6 12 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 8 true (2),
.cycle 3 12 true (1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 13 2 true (3),
.cycle 11 8 true (2),
.cycle 1 16 true (1),
.last 17 (5,false),
.cycle 9 6 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 5 true (3),
.last 15 (5,false)
])
theorem kid22_part1173_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part1173) = true := by rfl

def kid22_part1174 : Audit := .split 13 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 24 7 false (1),
.cycle 19 5 false (1),
.cycle 12 7 true (2),
.last 23 (5,false),
.cycle 20 5 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 17 8 true (3),
.cycle 0 15 true (0),
.last 16 (5,false),
.last 19 (5,false),
.cycle 6 11 true (2),
.cycle 12 2 true (2),
.cycle 19 5 false (1),
.cycle 5 9 true (1),
.last 23 (5,false),
.cycle 20 5 false (1),
.cycle 1 14 true (1),
.cycle 12 5 true (2),
.cycle 2 15 true (1),
.cycle 0 15 true (0),
.cycle 12 5 true (2),
.last 17 (5,false)
])
theorem kid22_part1174_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part1174) = true := by rfl

def kid22_part1175 : Audit := .cycle 5 9 true (1)
theorem kid22_part1175_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part1175) = true := by rfl

def kid22_part1176 : Audit := .cycle 5 7 true (1)
theorem kid22_part1176_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part1176) = true := by rfl

def kid22_part1177 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (1),
.cycle 1 16 true (1),
.last 22 (5,false),
.cycle 19 1 false (1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 1 14 true (1),
.last 16 (5,false),
.cycle 9 4 true (2),
.cycle 6 13 true (1),
.cycle 15 2 true (0),
.cycle 5 9 true (1),
.cycle 26 1 false (2),
.last 19 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.cycle 13 5 true (3),
.last 19 (5,false)
])
theorem kid22_part1177_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part1177) = true := by rfl

def kid22_part1178 : Audit := .split 17 (4,true) (byMove [
.cycle 19 3 false (2),
.cycle 20 3 false (0),
.last 19 (5,false),
.cycle 20 7 true (2),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 21 true (0),
.cycle 26 24 true (2),
.last 19 (5,false),
.cycle 38 32 true (0),
.last 22 (5,false),
.cycle 12 6 true (0),
.cycle 30 3 false (4),
.cycle 16 2 true (0),
.last 19 (5,false),
.cycle 26 3 false (4),
.last 20 (5,false),
.cycle 18 3 false (0),
.cycle 0 21 true (0),
.cycle 18 5 true (2),
.cycle 14 4 true (0),
.cycle 5 13 true (0),
.cycle 19 5 true (3),
.last 27 (5,false)
])
theorem kid22_part1178_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part1178) = true := by rfl

def kid22_part1179 : Audit := .cycle 1 12 true (1)
theorem kid22_part1179_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part1179) = true := by rfl

def kid22_part1180 : Audit := .split 16 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 32 17 false (3),
.cycle 1 19 true (1),
.cycle 12 7 true (3),
.last 31 (5,false),
.cycle 0 26 true (0),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.last 19 (5,false),
.cycle 1 19 true (1),
.cycle 6 14 true (2),
.cycle 15 2 true (3),
.cycle 11 9 true (3),
.cycle 5 12 true (1),
.last 29 (5,false),
.cycle 26 11 false (3),
.cycle 1 17 true (1),
.cycle 12 5 true (3),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.cycle 13 5 true (3),
.last 20 (5,false)
])
theorem kid22_part1180_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part1180) = true := by rfl

def kid22_part1181 : Audit := .cycle 2 11 true (1)
theorem kid22_part1181_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part1181) = true := by rfl

def kid22_part1182 : Audit := .cycle 0 13 true (0)
theorem kid22_part1182_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part1182) = true := by rfl

def kid22_part1183 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 28 11 false (2),
.cycle 28 11 false (2),
.cycle 0 14 true (0),
.last 23 (5,false),
.cycle 23 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 8 true (3),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 23 (5,false),
.cycle 22 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 5 true (3),
.last 13 (5,false)
])
theorem kid22_part1183_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part1183) = true := by rfl

def kid22_part1184 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 30 13 false (2),
.last 16 (5,false),
.cycle 0 16 true (0),
.last 27 (5,false),
.last 21 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 13 8 true (3),
.cycle 3 12 true (1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 13 2 true (3),
.cycle 11 4 true (3),
.cycle 1 16 true (1),
.last 27 (5,false),
.cycle 24 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 5 true (3),
.last 15 (5,false)
])
theorem kid22_part1184_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part1184) = true := by rfl

def kid22_part1160 : Audit := .split 11 (2,true) (byMove [(kid22_part1161),(kid22_part1162),(kid22_part1163),(kid22_part1164),(kid22_part1165),(kid22_part1166),(kid22_part1167),(kid22_part1168),(kid22_part1169),(kid22_part1170),(kid22_part1171),(kid22_part1172),(kid22_part1173),(kid22_part1174),(kid22_part1175),(kid22_part1176),(kid22_part1177),(kid22_part1178),(kid22_part1179),(kid22_part1180),(kid22_part1181),(kid22_part1182),(kid22_part1183),(kid22_part1184)])

theorem kid22_part1160_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part1160) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid22_part1161),(kid22_part1162),(kid22_part1163),(kid22_part1164),(kid22_part1165),(kid22_part1166),(kid22_part1167),(kid22_part1168),(kid22_part1169),(kid22_part1170),(kid22_part1171),(kid22_part1172),(kid22_part1173),(kid22_part1174),(kid22_part1175),(kid22_part1176),(kid22_part1177),(kid22_part1178),(kid22_part1179),(kid22_part1180),(kid22_part1181),(kid22_part1182),(kid22_part1183),(kid22_part1184)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1161_checked

  · exact kid22_part1167_checked

  · exact kid22_part1173_checked

  · exact kid22_part1179_checked

  · exact kid22_part1162_checked

  · exact kid22_part1168_checked

  · exact kid22_part1174_checked

  · exact kid22_part1180_checked

  · exact kid22_part1163_checked

  · exact kid22_part1169_checked

  · exact kid22_part1175_checked

  · exact kid22_part1181_checked

  · exact kid22_part1164_checked

  · exact kid22_part1170_checked

  · exact kid22_part1176_checked

  · exact kid22_part1182_checked

  · exact kid22_part1165_checked

  · exact kid22_part1171_checked

  · exact kid22_part1177_checked

  · exact kid22_part1183_checked

  · exact kid22_part1166_checked

  · exact kid22_part1172_checked

  · exact kid22_part1178_checked

  · exact kid22_part1184_checked

def kid22_part1185 : Audit := .cycle 1 12 true (1)
theorem kid22_part1185_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part1185) = true := by rfl

def kid22_part1187 : Audit := .split 18 (2,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.cycle 0 20 true (0),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 56 1 false (10),
.cycle 37 1 false (7),
.cycle 26 1 false (4),
.last 20 (5,false),
.last 19 (5,false),
.cycle 23 1 false (3),
.cycle 31 1 false (5),
.cycle 32 1 false (6),
.cycle 30 1 false (6),
.cycle 15 8 true (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 26 1 false (4),
.last 19 (5,false)
])
theorem kid22_part1187_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part1187) = true := by rfl

def kid22_part1188 : Audit := .cycle 19 1 false (1)
theorem kid22_part1188_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part1188) = true := by rfl

def kid22_part1189 : Audit := .split 16 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 26 1 false (4),
.cycle 56 1 false (10),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.last 18 (5,false),
.last 17 (5,false),
.cycle 35 1 false (3),
.cycle 14 5 false (3),
.cycle 28 1 false (4),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 5 16 true (0),
.cycle 1 18 true (0),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 19 1 false (1),
.last 17 (5,false)
])
theorem kid22_part1189_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part1189) = true := by rfl

def kid22_part1190 : Audit := .cycle 26 1 false (4)
theorem kid22_part1190_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part1190) = true := by rfl

def kid22_part1191 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.last 24 (2,true),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 0 23 true (0),
.cycle 22 1 false (0),
.last 19 (2,true),
.last 22 (2,true),
.cycle 16 3 false (2),
.cycle 20 1 false (0),
.cycle 15 7 false (3),
.last 20 (2,true),
.cycle 0 25 true (-1),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 0 23 true (0),
.cycle 27 1 false (1),
.last 19 (2,true),
.last 22 (2,true),
.cycle 15 4 false (3),
.cycle 0 25 true (0)
])
theorem kid22_part1191_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part1191) = true := by rfl

def kid22_part1192 : Audit := .cycle 17 1 false (1)
theorem kid22_part1192_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part1192) = true := by rfl

def kid22_part1193 : Audit := .cycle 0 37 true (0)
theorem kid22_part1193_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part1193) = true := by rfl

def kid22_part1194 : Audit := .cycle 22 18 true (4)
theorem kid22_part1194_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part1194) = true := by rfl

def kid22_part1195 : Audit := .split 16 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 35 8 true (7),
.cycle 10 10 true (0),
.cycle 17 8 true (2),
.last 18 (5,false),
.last 17 (5,false),
.cycle 5 16 true (0),
.cycle 19 8 true (3),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 32 true (0),
.cycle 5 34 true (0),
.cycle 19 8 true (2),
.last 17 (5,false)
])
theorem kid22_part1195_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part1195) = true := by rfl

def kid22_part1196 : Audit := .cycle 0 17 true (0)
theorem kid22_part1196_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part1196) = true := by rfl

def kid22_part1197 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.last 28 (2,true),
.last 23 (2,true),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 1, 64],[2, 16, 64, 1, 16, 18, 64],64⟩,
.cycle 7 12 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 16 3 true (4),
.cycle 35 1 false (5),
.cycle 20 5 true (4),
.last 20 (2,true),
.far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 2, 3],[128, 256, 8, 65552, 2, 1, 128, 256, 32768, 2, 1040, 16777216, 524288, 1048576, 8, 1024, 16777216, 1, 524288, 1048576, 32768, 2, 66560, 16777216, 16777216],[2, 1024, 16777216, 1, 16, 65552, 8192, 1024, 16777216, 4096, 65536, 2, 2, 4194304, 16777216, 1, 16, 1024, 8192, 4194304, 16777216, 4096, 65536, 2, 16777216],29444108⟩,
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 15 21 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 2, 64],[2, 16, 64, 1, 16, 18, 64],64⟩,
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 16 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 32, 64],[2, 16, 64, 1, 16, 18, 64],64⟩
])
theorem kid22_part1197_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part1197) = true := by rfl

def kid22_part1198 : Audit := .cycle 23 1 false (3)
theorem kid22_part1198_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part1198) = true := by rfl

def kid22_part1199 : Audit := .cycle 23 1 false (3)
theorem kid22_part1199_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part1199) = true := by rfl

def kid22_part1200 : Audit := .cycle 14 2 true (2)
theorem kid22_part1200_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part1200) = true := by rfl

def kid22_part1201 : Audit := .split 16 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 9, 1, 8, 4, 8, 64],112⟩,
.cycle 12 30 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.cycle 20 1 false (6),
.cycle 28 1 false (6),
.cycle 30 1 false (6),
.cycle 18 1 false (2),
.cycle 13 8 true (1),
.cycle 14 5 false (3),
.cycle 23 1 false (3),
.cycle 17 1 false (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 23 22 true (3),
.cycle 5 18 true (0),
.cycle 2 17 true (0),
.cycle 0 43 true (0),
.cycle 15 2 true (2),
.cycle 23 1 false (3)
])
theorem kid22_part1201_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part1201) = true := by rfl

def kid22_part1202 : Audit := .cycle 21 1 false (3)
theorem kid22_part1202_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part1202) = true := by rfl

def kid22_part1203 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 48 1 false (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 13 6 true (0),
.cycle 14 5 false (3),
.last 19 (2,true),
.cycle 31 1 false (3),
.cycle 16 3 false (2),
.cycle 20 1 false (0),
.cycle 15 7 false (3),
.last 20 (2,true),
.cycle 12 8 true (-1),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 25 1 false (-1),
.cycle 15 6 false (3),
.last 19 (2,true),
.cycle 5 21 true (0),
.cycle 15 4 false (3),
.cycle 12 8 true (0)
])
theorem kid22_part1203_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part1203) = true := by rfl

def kid22_part1204 : Audit := .cycle 17 1 false (1)
theorem kid22_part1204_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part1204) = true := by rfl

def kid22_part1205 : Audit := .cycle 0 42 true (0)
theorem kid22_part1205_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part1205) = true := by rfl

def kid22_part1206 : Audit := .cycle 5 14 true (0)
theorem kid22_part1206_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part1206) = true := by rfl

def kid22_part1207 : Audit := .split 16 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 64, 64],[8, 8, 1, 8, 8, 8, 64],112⟩,
.cycle 25 1 false (3),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 2 16 true (0),
.cycle 29 1 false (5),
.cycle 0 17 true (0),
.cycle 2 40 true (0),
.cycle 2 23 true (0),
.cycle 3 14 true (0),
.last 18 (5,false),
.last 17 (5,false),
.cycle 2 24 true (0),
.cycle 2 17 true (0),
.cycle 25 1 false (3),
.cycle 2 39 true (0),
.cycle 15 2 true (3),
.cycle 23 1 false (3),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 18 20 true (3),
.cycle 5 14 true (0),
.last 17 (5,false)
])
theorem kid22_part1207_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part1207) = true := by rfl

def kid22_part1208 : Audit := .cycle 0 17 true (0)
theorem kid22_part1208_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part1208) = true := by rfl

def kid22_part1209 : Audit := .cycle 5 14 true (0)
theorem kid22_part1209_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part1209) = true := by rfl

def kid22_part1210 : Audit := .split 41 (5,false) (byMove [
.cycle 5 55 true (0),
.cycle 23 22 true (2),
.last 42 (2,true),
.cycle 0 43 true (0),
.cycle 40 2 true (8),
.cycle 5 65 true (0),
.cycle 0 42 true (0),
.cycle 5 54 true (0),
.cycle 37 9 true (5),
.cycle 3 39 true (0),
.cycle 40 4 true (8),
.cycle 41 1 true (9),
.cycle 37 10 true (5),
.cycle 39 3 true (7),
.last 42 (2,true),
.cycle 17 25 true (2),
.cycle 15 27 true (2),
.cycle 23 20 true (2),
.cycle 0 42 true (0),
.cycle 1 41 true (0),
.cycle 2 40 true (0),
.cycle 17 26 true (2),
.cycle 5 39 true (0),
.cycle 41 1 true (9)
])
theorem kid22_part1210_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part1210) = true := by rfl

def kid22_part1186 : Audit := .split 15 (4,true) (byMove [(kid22_part1187),(kid22_part1188),(kid22_part1189),(kid22_part1190),(kid22_part1191),(kid22_part1192),(kid22_part1193),(kid22_part1194),(kid22_part1195),(kid22_part1196),(kid22_part1197),(kid22_part1198),(kid22_part1199),(kid22_part1200),(kid22_part1201),(kid22_part1202),(kid22_part1203),(kid22_part1204),(kid22_part1205),(kid22_part1206),(kid22_part1207),(kid22_part1208),(kid22_part1209),(kid22_part1210)])

theorem kid22_part1186_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part1186) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) 15 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (4,true) (some mv)) (byMove [(kid22_part1187),(kid22_part1188),(kid22_part1189),(kid22_part1190),(kid22_part1191),(kid22_part1192),(kid22_part1193),(kid22_part1194),(kid22_part1195),(kid22_part1196),(kid22_part1197),(kid22_part1198),(kid22_part1199),(kid22_part1200),(kid22_part1201),(kid22_part1202),(kid22_part1203),(kid22_part1204),(kid22_part1205),(kid22_part1206),(kid22_part1207),(kid22_part1208),(kid22_part1209),(kid22_part1210)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1187_checked

  · exact kid22_part1193_checked

  · exact kid22_part1199_checked

  · exact kid22_part1205_checked

  · exact kid22_part1188_checked

  · exact kid22_part1194_checked

  · exact kid22_part1200_checked

  · exact kid22_part1206_checked

  · exact kid22_part1189_checked

  · exact kid22_part1195_checked

  · exact kid22_part1201_checked

  · exact kid22_part1207_checked

  · exact kid22_part1190_checked

  · exact kid22_part1196_checked

  · exact kid22_part1202_checked

  · exact kid22_part1208_checked

  · exact kid22_part1191_checked

  · exact kid22_part1197_checked

  · exact kid22_part1203_checked

  · exact kid22_part1209_checked

  · exact kid22_part1192_checked

  · exact kid22_part1198_checked

  · exact kid22_part1204_checked

  · exact kid22_part1210_checked

def kid22_part1212 : Audit := .split 14 (2,true) (byMove [
.cycle 13 21 true (1),
.last 26 (4,true),
.cycle 17 1 false (1),
.last 18 (4,true),
.last 15 (4,true),
.last 22 (4,true),
.cycle 6 9 true (0),
.last 16 (4,true),
.last 26 (4,true),
.cycle 13 16 true (1),
.last 15 (4,true),
.last 26 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 22 (4,true),
.last 21 (4,true),
.last 16 (4,true),
.cycle 2 15 true (0),
.cycle 13 16 true (1),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid22_part1212_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1212) = true := by rfl

def kid22_part1213 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 45 9 true (0),
.last 23 (2,true),
.proven (BB6.Agent11Raw39B0RBPumps.M1979.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M1979.never m hm),
.last 31 (2,true),
.last 31 (2,true),
.cycle 6 17 true (-3),
.cycle 29 9 true (4),
.last 23 (2,true),
.cycle 29 9 true (4),
.cycle 61 38 true (5),
.cycle 1 45 true (-3),
.cycle 29 9 true (1),
.cycle 21 2 true (1),
.last 23 (2,true),
.cycle 33 9 true (4),
.cycle 42 9 true (0),
.cycle 41 9 true (0),
.cycle 38 9 true (5),
.cycle 22 25 true (2),
.last 23 (2,true),
.cycle 29 9 true (4),
.cycle 22 5 true (2),
.cycle 22 2 true (2)
])
theorem kid22_part1213_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1213) = true := by rfl

def kid22_part1214 : Audit := .split 12 (2,true) (byMove [
.last 29 (4,true),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 22 1 false (2),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 17 (4,true),
.last 16 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 15 (4,true),
.last 16 (4,true),
.last 27 (4,true),
.last 17 (4,true),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid22_part1214_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1214) = true := by rfl

def kid22_part1215 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.last 33 (2,true),
.last 16 (2,true),
.last 26 (2,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.proven (BB6.Agent11Raw39B0RBPumps.M1980.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M1980.never m hm),
.last 41 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.last 23 (2,true),
.cycle 23 1 false (-1),
.cycle 6 13 true (0),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 5 11 true (0),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.last 32 (2,true),
.cycle 1 21 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 5 true (3),
.cycle 15 2 true (3)
])
theorem kid22_part1215_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1215) = true := by rfl

def kid22_part1216 : Audit := .split 12 (4,true) (byMove [
.last 28 (2,true),
.cycle 24 2 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 6 33 true (0),
.last 14 (2,true),
.cycle 19 2 false (3),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 43 2 false (-3),
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 77 true (0),
.last 14 (2,true),
.cycle 23 2 false (-1),
.cycle 0 19 true (0),
.cycle 15 2 false (-1),
.cycle 11 2 true (0)
])
theorem kid22_part1216_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1216) = true := by rfl

def kid22_part1217 : Audit := .cycle 14 1 false (-2)
theorem kid22_part1217_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1217) = true := by rfl

def kid22_part1218 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 18 true (1),
.cycle 6 12 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 8 true (2),
.cycle 3 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 6 9 true (1),
.cycle 13 2 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 10 6 true (1),
.cycle 9 6 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 5 true (3),
.cycle 0 16 true (0)
])
theorem kid22_part1218_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1218) = true := by rfl

def kid22_part1219 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 17 7 false (1),
.last 14 (2,true),
.last 45 (2,true),
.cycle 15 10 false (1),
.cycle 16 5 false (0),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 2, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 10 true (1),
.cycle 16 7 false (2),
.cycle 6 11 true (1),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 17 5 false (0),
.cycle 16 5 false (0),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 5 true (3),
.cycle 13 2 true (3)
])
theorem kid22_part1219_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1219) = true := by rfl

def kid22_part1220 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.last 19 (4,true),
.last 23 (4,true),
.cycle 15 3 false (-1),
.cycle 1 16 true (1),
.cycle 6 7 true (1),
.last 14 (4,true),
.last 25 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 9 4 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.cycle 15 3 false (-1),
.cycle 11 2 true (1),
.last 26 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid22_part1220_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1220) = true := by rfl

def kid22_part1221 : Audit := .cycle 5 7 true (1)
theorem kid22_part1221_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1221) = true := by rfl

def kid22_part1222 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.last 20 (2,true),
.last 17 (2,true),
.cycle 15 3 false (-1),
.cycle 10 4 true (1),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 14 3 true (4),
.cycle 9 4 true (1),
.cycle 6 13 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 26 1 false (2),
.cycle 15 3 false (-1),
.cycle 11 2 true (1),
.cycle 23 28 true (-1),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 12 5 true (2),
.cycle 12 2 true (2)
])
theorem kid22_part1222_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1222) = true := by rfl

def kid22_part1223 : Audit := .cycle 14 3 false (0)
theorem kid22_part1223_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1223) = true := by rfl

def kid22_part1224 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 14 30 false (2),
.last 15 (2,true),
.cycle 0 20 true (0),
.cycle 14 7 false (2),
.cycle 21 6 false (-1),
.cycle 6 9 true (0),
.cycle 13 16 true (1),
.last 15 (2,true),
.cycle 13 16 true (1),
.cycle 20 5 true (4),
.cycle 17 10 false (1),
.cycle 13 15 true (1),
.cycle 13 2 true (1),
.last 15 (2,true),
.cycle 13 20 true (1),
.cycle 14 7 false (2),
.cycle 17 6 false (0),
.cycle 13 25 true (1),
.cycle 1 16 true (0),
.last 15 (2,true),
.cycle 13 16 true (1),
.cycle 14 5 true (2),
.cycle 14 2 true (2)
])
theorem kid22_part1224_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1224) = true := by rfl

def kid22_part1225 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.last 20 (2,true),
.last 14 (2,true),
.last 28 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.cycle 0 17 true (0),
.last 26 (2,true),
.last 14 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.last 20 (2,true),
.last 30 (2,true),
.cycle 12 2 true (0),
.last 14 (2,true),
.last 26 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.cycle 0 17 true (0),
.cycle 1 21 true (0),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 14 5 true (2),
.cycle 13 2 true (1)
])
theorem kid22_part1225_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1225) = true := by rfl

def kid22_part1226 : Audit := .split 12 (2,true) (byMove [
.last 41 (4,true),
.last 18 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 18 1 false (6),
.last 16 (4,true),
.last 13 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.last 16 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 2 15 true (0),
.last 16 (4,true),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid22_part1226_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1226) = true := by rfl

def kid22_part1227 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 21 1 false (-1),
.last 16 (2,true),
.cycle 22 1 false (2),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 37 true (0),
.cycle 23 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 33 1 false (3),
.cycle 21 1 false (-1),
.cycle 25 1 false (1),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 23 1 false (1),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 27 true (1),
.cycle 1 21 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 5 true (3),
.cycle 15 2 true (3)
])
theorem kid22_part1227_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1227) = true := by rfl

def kid22_part1228 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 26 2 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 37 true (0),
.cycle 32 2 false (0),
.last 13 (2,true),
.cycle 24 2 false (4),
.cycle 17 2 false (5),
.cycle 14 2 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 37 true (0),
.cycle 1 16 true (0),
.last 13 (2,true),
.cycle 18 20 true (3),
.cycle 14 5 true (2),
.cycle 12 2 true (0)
])
theorem kid22_part1228_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1228) = true := by rfl

def kid22_part1229 : Audit := .cycle 14 1 false (-2)
theorem kid22_part1229_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1229) = true := by rfl

def kid22_part1230 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 38 10 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 23 (2,true),
.cycle 31 8 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 8 true (2),
.cycle 3 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 6 9 true (1),
.cycle 13 2 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 19 8 false (1),
.cycle 19 8 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 5 true (3),
.cycle 0 16 true (0)
])
theorem kid22_part1230_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1230) = true := by rfl

def kid22_part1231 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 69 15 true (0),
.last 14 (2,true),
.last 24 (2,true),
.cycle 16 6 false (0),
.last 25 (2,true),
.cycle 1 14 true (1),
.cycle 1 23 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 8 true (3),
.cycle 20 9 false (1),
.cycle 6 11 true (1),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 14 6 false (2),
.cycle 18 5 false (0),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 5 true (3),
.cycle 13 2 true (3)
])
theorem kid22_part1231_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1231) = true := by rfl

def kid22_part1232 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.last 16 (4,true),
.cycle 16 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.last 14 (4,true),
.cycle 6 7 true (1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid22_part1232_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1232) = true := by rfl

def kid22_part1233 : Audit := .cycle 5 7 true (1)
theorem kid22_part1233_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1233) = true := by rfl

def kid22_part1234 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 32 6 false (0),
.last 13 (2,true),
.cycle 0 18 true (0),
.cycle 13 4 false (1),
.cycle 17 4 false (-1),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 14 3 true (4),
.cycle 17 6 false (1),
.cycle 6 13 true (1),
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 1 18 true (1),
.cycle 13 4 false (1),
.cycle 15 4 false (0),
.cycle 1 23 true (1),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 12 5 true (2),
.cycle 12 2 true (2)
])
theorem kid22_part1234_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1234) = true := by rfl

def kid22_part1235 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 53 11 true (0),
.last 14 (2,true),
.last 28 (2,true),
.cycle 14 4 false (0),
.cycle 11 9 false (2),
.cycle 0 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 32, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 5 true (3),
.cycle 16 5 false (0),
.cycle 15 17 true (1),
.cycle 13 2 true (0),
.last 14 (2,true),
.cycle 27 1 false (1),
.cycle 14 4 false (0),
.cycle 16 3 false (-1),
.cycle 0 17 true (0),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 14 5 true (2),
.cycle 12 2 true (1)
])
theorem kid22_part1235_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1235) = true := by rfl

def kid22_part1211 : Audit := .split 11 (5,false) (byMove [(kid22_part1212),(kid22_part1213),(kid22_part1214),(kid22_part1215),(kid22_part1216),(kid22_part1217),(kid22_part1218),(kid22_part1219),(kid22_part1220),(kid22_part1221),(kid22_part1222),(kid22_part1223),(kid22_part1224),(kid22_part1225),(kid22_part1226),(kid22_part1227),(kid22_part1228),(kid22_part1229),(kid22_part1230),(kid22_part1231),(kid22_part1232),(kid22_part1233),(kid22_part1234),(kid22_part1235)])

theorem kid22_part1211_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part1211) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (5,false) (some mv)) (byMove [(kid22_part1212),(kid22_part1213),(kid22_part1214),(kid22_part1215),(kid22_part1216),(kid22_part1217),(kid22_part1218),(kid22_part1219),(kid22_part1220),(kid22_part1221),(kid22_part1222),(kid22_part1223),(kid22_part1224),(kid22_part1225),(kid22_part1226),(kid22_part1227),(kid22_part1228),(kid22_part1229),(kid22_part1230),(kid22_part1231),(kid22_part1232),(kid22_part1233),(kid22_part1234),(kid22_part1235)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1212_checked

  · exact kid22_part1218_checked

  · exact kid22_part1224_checked

  · exact kid22_part1230_checked

  · exact kid22_part1213_checked

  · exact kid22_part1219_checked

  · exact kid22_part1225_checked

  · exact kid22_part1231_checked

  · exact kid22_part1214_checked

  · exact kid22_part1220_checked

  · exact kid22_part1226_checked

  · exact kid22_part1232_checked

  · exact kid22_part1215_checked

  · exact kid22_part1221_checked

  · exact kid22_part1227_checked

  · exact kid22_part1233_checked

  · exact kid22_part1216_checked

  · exact kid22_part1222_checked

  · exact kid22_part1228_checked

  · exact kid22_part1234_checked

  · exact kid22_part1217_checked

  · exact kid22_part1223_checked

  · exact kid22_part1229_checked

  · exact kid22_part1235_checked

def kid22_part1237 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 17 8 false (1),
.cycle 18 1 false (0),
.last 27 (4,true),
.last 14 (4,true),
.cycle 15 6 false (1),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 20 true (0),
.last 16 (4,true),
.last 15 (4,true),
.last 21 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 15 6 false (1),
.cycle 1 14 true (1),
.last 26 (4,true),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 8 false (3)
])
theorem kid22_part1237_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1237) = true := by rfl

def kid22_part1238 : Audit := .cycle 1 14 true (1)
theorem kid22_part1238_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1238) = true := by rfl

def kid22_part1239 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 23 1 false (1),
.last 18 (2,true),
.cycle 26 1 false (2),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 0 41 true (0),
.last 22 (2,true),
.last 18 (2,true),
.cycle 0 19 true (0),
.last 30 (2,true),
.last 20 (2,true),
.cycle 27 1 false (3),
.cycle 16 2 true (2),
.last 18 (2,true),
.cycle 25 1 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.last 42 (2,true),
.cycle 25 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1)
])
theorem kid22_part1239_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1239) = true := by rfl

def kid22_part1240 : Audit := .split 15 (2,true) (byMove [
.cycle 30 1 false (4),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 23 1 false (1),
.last 16 (4,true),
.cycle 18 1 false (0),
.last 33 (4,true),
.last 23 (4,true),
.last 25 (4,true),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 25 1 false (1),
.last 18 (4,true),
.last 17 (4,true),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.last 16 (4,true),
.cycle 18 1 false (0),
.last 42 (4,true),
.cycle 22 1 false (0),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 20 1 false (0)
])
theorem kid22_part1240_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1240) = true := by rfl

def kid22_part1241 : Audit := .cycle 13 2 false (-1)
theorem kid22_part1241_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1241) = true := by rfl

def kid22_part1242 : Audit := .cycle 13 1 false (-1)
theorem kid22_part1242_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1242) = true := by rfl

def kid22_part1243 : Audit := .cycle 6 5 true (2)
theorem kid22_part1243_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1243) = true := by rfl

def kid22_part1244 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 9 false (1),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 7 8 true (2),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 21 5 false (1),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 2, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1)
])
theorem kid22_part1244_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1244) = true := by rfl

def kid22_part1245 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 17 3 false (0),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.cycle 17 3 false (0),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.last 19 (4,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (2)
])
theorem kid22_part1245_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1245) = true := by rfl

def kid22_part1246 : Audit := .cycle 1 12 true (1)
theorem kid22_part1246_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1246) = true := by rfl

def kid22_part1247 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 17 3 false (0),
.cycle 10 4 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 13 4 true (3),
.cycle 6 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 17 3 false (0),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 9 4 true (2)
])
theorem kid22_part1247_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1247) = true := by rfl

def kid22_part1248 : Audit := .cycle 9 2 true (2)
theorem kid22_part1248_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1248) = true := by rfl

def kid22_part1249 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 17 8 false (1),
.last 14 (2,true),
.cycle 0 29 true (0),
.cycle 14 7 false (2),
.cycle 15 6 false (1),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 5 true (4),
.cycle 28 26 true (2),
.cycle 6 11 true (1),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 14 7 false (2),
.cycle 15 6 false (1),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 16, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 14 (2,true),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 15 8 false (3)
])
theorem kid22_part1249_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1249) = true := by rfl

def kid22_part1250 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 16 6 false (0),
.cycle 16 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 14 4 false (0),
.cycle 6 7 true (1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 14 4 false (0),
.last 19 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 14 6 false (2)
])
theorem kid22_part1250_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1250) = true := by rfl

def kid22_part1251 : Audit := .cycle 5 7 true (1)
theorem kid22_part1251_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1251) = true := by rfl

def kid22_part1252 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 20 1 false (0),
.last 16 (2,true),
.cycle 23 1 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 37 true (0),
.cycle 22 18 true (4),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 32 1 false (4),
.cycle 24 1 false (2),
.cycle 24 1 false (2),
.cycle 14 2 true (2),
.last 16 (2,true),
.cycle 22 1 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 42 true (0),
.cycle 22 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0)
])
theorem kid22_part1252_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1252) = true := by rfl

def kid22_part1253 : Audit := .cycle 13 2 false (-1)
theorem kid22_part1253_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1253) = true := by rfl

def kid22_part1254 : Audit := .cycle 13 1 false (-1)
theorem kid22_part1254_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1254) = true := by rfl

def kid22_part1255 : Audit := .cycle 6 5 true (2)
theorem kid22_part1255_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1255) = true := by rfl

def kid22_part1256 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 23 7 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 16 11 false (1),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 25 10 true (5),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 17 6 false (1),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 2, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1)
])
theorem kid22_part1256_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1256) = true := by rfl

def kid22_part1257 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 20 5 false (0),
.cycle 25 1 false (1),
.last 23 (4,true),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 21 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 18 5 false (2)
])
theorem kid22_part1257_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1257) = true := by rfl

def kid22_part1258 : Audit := .cycle 1 12 true (1)
theorem kid22_part1258_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1258) = true := by rfl

def kid22_part1259 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 20 5 false (0),
.last 12 (2,true),
.cycle 0 25 true (0),
.cycle 15 4 false (0),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 8 8 true (2),
.cycle 6 9 true (2),
.cycle 11 2 true (2),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 15 4 false (0),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 16, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 12 (2,true),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 18 5 false (2)
])
theorem kid22_part1259_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1259) = true := by rfl

def kid22_part1260 : Audit := .cycle 15 3 false (1)
theorem kid22_part1260_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1260) = true := by rfl

def kid22_part1236 : Audit := .split 10 (5,false) (byMove [(kid22_part1237),(kid22_part1238),(kid22_part1239),(kid22_part1240),(kid22_part1241),(kid22_part1242),(kid22_part1243),(kid22_part1244),(kid22_part1245),(kid22_part1246),(kid22_part1247),(kid22_part1248),(kid22_part1249),(kid22_part1250),(kid22_part1251),(kid22_part1252),(kid22_part1253),(kid22_part1254),(kid22_part1255),(kid22_part1256),(kid22_part1257),(kid22_part1258),(kid22_part1259),(kid22_part1260)])

theorem kid22_part1236_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part1236) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid22_part1237),(kid22_part1238),(kid22_part1239),(kid22_part1240),(kid22_part1241),(kid22_part1242),(kid22_part1243),(kid22_part1244),(kid22_part1245),(kid22_part1246),(kid22_part1247),(kid22_part1248),(kid22_part1249),(kid22_part1250),(kid22_part1251),(kid22_part1252),(kid22_part1253),(kid22_part1254),(kid22_part1255),(kid22_part1256),(kid22_part1257),(kid22_part1258),(kid22_part1259),(kid22_part1260)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1237_checked

  · exact kid22_part1243_checked

  · exact kid22_part1249_checked

  · exact kid22_part1255_checked

  · exact kid22_part1238_checked

  · exact kid22_part1244_checked

  · exact kid22_part1250_checked

  · exact kid22_part1256_checked

  · exact kid22_part1239_checked

  · exact kid22_part1245_checked

  · exact kid22_part1251_checked

  · exact kid22_part1257_checked

  · exact kid22_part1240_checked

  · exact kid22_part1246_checked

  · exact kid22_part1252_checked

  · exact kid22_part1258_checked

  · exact kid22_part1241_checked

  · exact kid22_part1247_checked

  · exact kid22_part1253_checked

  · exact kid22_part1259_checked

  · exact kid22_part1242_checked

  · exact kid22_part1248_checked

  · exact kid22_part1254_checked

  · exact kid22_part1260_checked

def kid22_part1261 : Audit := .cycle 1 10 true (1)
theorem kid22_part1261_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part1261) = true := by rfl

def kid22_part1262 : Audit := .cycle 7 3 true (3)
theorem kid22_part1262_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part1262) = true := by rfl

def kid22_part1264 : Audit := .cycle 1 11 true (1)
theorem kid22_part1264_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part1264) = true := by rfl

def kid22_part1265 : Audit := .cycle 7 4 true (3)
theorem kid22_part1265_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part1265) = true := by rfl

def kid22_part1266 : Audit := .split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.last 22 (5,false),
.cycle 32 1 false (4),
.cycle 0 20 true (0),
.cycle 56 1 false (6),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.last 21 (5,false),
.last 20 (5,false),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.cycle 22 1 false (2),
.cycle 34 1 false (6),
.last 22 (5,false),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.cycle 26 1 false (2),
.last 20 (5,false)
])
theorem kid22_part1266_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part1266) = true := by rfl

def kid22_part1267 : Audit := .cycle 0 12 true (0)
theorem kid22_part1267_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part1267) = true := by rfl

def kid22_part1268 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,false),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 28 1 false (4),
.cycle 0 21 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 12 true (2),
.cycle 17 2 true (0),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 12 (5,false)
])
theorem kid22_part1268_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part1268) = true := by rfl

def kid22_part1269 : Audit := .cycle 2 10 true (1)
theorem kid22_part1269_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part1269) = true := by rfl

def kid22_part1270 : Audit := .cycle 0 11 true (0)
theorem kid22_part1270_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part1270) = true := by rfl

def kid22_part1271 : Audit := .cycle 1 10 true (1)
theorem kid22_part1271_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part1271) = true := by rfl

def kid22_part1272 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 40 1 false (8),
.cycle 0 20 true (0),
.last 21 (5,false),
.cycle 2 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.last 20 (5,false),
.last 19 (5,false),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.cycle 42 1 false (10),
.cycle 1 20 true (1),
.last 21 (5,false),
.cycle 9 10 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.last 19 (5,false)
])
theorem kid22_part1272_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part1272) = true := by rfl

def kid22_part1273 : Audit := .cycle 3 8 true (1)
theorem kid22_part1273_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part1273) = true := by rfl

def kid22_part1274 : Audit := .split 12 (5,false) (byMove [
.cycle 10 5 true (3),
.last 17 (4,true),
.last 23 (4,true),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 12 true (1)
])
theorem kid22_part1274_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part1274) = true := by rfl

def kid22_part1275 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 2 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.cycle 11 1 true (5),
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
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1275_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part1275) = true := by rfl

def kid22_part1276 : Audit := .cycle 6 5 true (2)
theorem kid22_part1276_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part1276) = true := by rfl

def kid22_part1277 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 23 5 false (1),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.last 13 (5,false)
])
theorem kid22_part1277_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part1277) = true := by rfl

def kid22_part1278 : Audit := .cycle 1 14 true (1)
theorem kid22_part1278_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part1278) = true := by rfl

def kid22_part1279 : Audit := .cycle 1 12 true (1)
theorem kid22_part1279_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part1279) = true := by rfl

def kid22_part1280 : Audit := .split 11 (4,true) (byMove [
.cycle 10 8 true (2),
.cycle 0 15 true (0),
.last 22 (5,false),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 2 11 true (1),
.cycle 6 9 true (2),
.cycle 17 2 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 2 11 true (1)
])
theorem kid22_part1280_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part1280) = true := by rfl

def kid22_part1281 : Audit := .cycle 9 2 true (3)
theorem kid22_part1281_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part1281) = true := by rfl

def kid22_part1282 : Audit := .cycle 0 11 true (0)
theorem kid22_part1282_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part1282) = true := by rfl

def kid22_part1283 : Audit := .cycle 1 10 true (1)
theorem kid22_part1283_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part1283) = true := by rfl

def kid22_part1284 : Audit := .cycle 2 9 true (1)
theorem kid22_part1284_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part1284) = true := by rfl

def kid22_part1285 : Audit := .cycle 1 13 true (1)
theorem kid22_part1285_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part1285) = true := by rfl

def kid22_part1286 : Audit := .cycle 8 3 true (3)
theorem kid22_part1286_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part1286) = true := by rfl

def kid22_part1287 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1287_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part1287) = true := by rfl

def kid22_part1263 : Audit := .split 10 (2,true) (byMove [(kid22_part1264),(kid22_part1265),(kid22_part1266),(kid22_part1267),(kid22_part1268),(kid22_part1269),(kid22_part1270),(kid22_part1271),(kid22_part1272),(kid22_part1273),(kid22_part1274),(kid22_part1275),(kid22_part1276),(kid22_part1277),(kid22_part1278),(kid22_part1279),(kid22_part1280),(kid22_part1281),(kid22_part1282),(kid22_part1283),(kid22_part1284),(kid22_part1285),(kid22_part1286),(kid22_part1287)])

theorem kid22_part1263_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part1263) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid22_part1264),(kid22_part1265),(kid22_part1266),(kid22_part1267),(kid22_part1268),(kid22_part1269),(kid22_part1270),(kid22_part1271),(kid22_part1272),(kid22_part1273),(kid22_part1274),(kid22_part1275),(kid22_part1276),(kid22_part1277),(kid22_part1278),(kid22_part1279),(kid22_part1280),(kid22_part1281),(kid22_part1282),(kid22_part1283),(kid22_part1284),(kid22_part1285),(kid22_part1286),(kid22_part1287)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1264_checked

  · exact kid22_part1270_checked

  · exact kid22_part1276_checked

  · exact kid22_part1282_checked

  · exact kid22_part1265_checked

  · exact kid22_part1271_checked

  · exact kid22_part1277_checked

  · exact kid22_part1283_checked

  · exact kid22_part1266_checked

  · exact kid22_part1272_checked

  · exact kid22_part1278_checked

  · exact kid22_part1284_checked

  · exact kid22_part1267_checked

  · exact kid22_part1273_checked

  · exact kid22_part1279_checked

  · exact kid22_part1285_checked

  · exact kid22_part1268_checked

  · exact kid22_part1274_checked

  · exact kid22_part1280_checked

  · exact kid22_part1286_checked

  · exact kid22_part1269_checked

  · exact kid22_part1275_checked

  · exact kid22_part1281_checked

  · exact kid22_part1287_checked

def kid22_part1288 : Audit := .cycle 0 11 true (0)
theorem kid22_part1288_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part1288) = true := by rfl

def kid22_part1290 : Audit := .cycle 1 11 true (1)
theorem kid22_part1290_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part1290) = true := by rfl

def kid22_part1291 : Audit := .cycle 7 4 true (3)
theorem kid22_part1291_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part1291) = true := by rfl

def kid22_part1292 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 38 1 false (10),
.cycle 21 1 false (3),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 12 true (2),
.cycle 21 5 false (1),
.cycle 0 14 true (0),
.cycle 19 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 12 (5,false)
])
theorem kid22_part1292_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part1292) = true := by rfl

def kid22_part1293 : Audit := .cycle 0 12 true (0)
theorem kid22_part1293_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part1293) = true := by rfl

def kid22_part1294 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.last 26 (2,true),
.last 14 (2,true),
.cycle 24 1 false (-2),
.cycle 15 2 false (-1),
.cycle 20 1 false (-2),
.cycle 1 14 true (1),
.cycle 19 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 3 false (0),
.cycle 19 7 false (1),
.cycle 16 7 false (2),
.last 20 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 15 2 false (-1),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 18 8 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 4 false (1),
.cycle 18 8 false (2)
])
theorem kid22_part1294_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part1294) = true := by rfl

def kid22_part1295 : Audit := .cycle 8 4 true (3)
theorem kid22_part1295_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part1295) = true := by rfl

def kid22_part1296 : Audit := .cycle 0 11 true (0)
theorem kid22_part1296_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part1296) = true := by rfl

def kid22_part1297 : Audit := .cycle 1 10 true (1)
theorem kid22_part1297_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part1297) = true := by rfl

def kid22_part1298 : Audit := .cycle 10 8 true (3)
theorem kid22_part1298_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part1298) = true := by rfl

def kid22_part1299 : Audit := .cycle 3 8 true (1)
theorem kid22_part1299_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part1299) = true := by rfl

def kid22_part1300 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 0 23 true (0),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 19 2 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 6 true (3),
.cycle 10 5 true (3),
.last 19 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 29 2 false (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 6 true (3)
])
theorem kid22_part1300_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part1300) = true := by rfl

def kid22_part1301 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 8 6 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 14 true (3),
.cycle 10 8 true (3),
.cycle 10 4 true (4),
.cycle 11 1 true (5),
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
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1301_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part1301) = true := by rfl

def kid22_part1302 : Audit := .cycle 6 5 true (2)
theorem kid22_part1302_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part1302) = true := by rfl

def kid22_part1303 : Audit := .cycle 10 2 true (3)
theorem kid22_part1303_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part1303) = true := by rfl

def kid22_part1304 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 30 1 false (8),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.cycle 8 5 true (3),
.cycle 10 8 true (2),
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.cycle 19 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 8 5 true (3)
])
theorem kid22_part1304_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part1304) = true := by rfl

def kid22_part1305 : Audit := .cycle 1 12 true (1)
theorem kid22_part1305_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part1305) = true := by rfl

def kid22_part1306 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 44 11 true (0),
.last 14 (2,true),
.cycle 22 1 false (-2),
.cycle 15 2 false (-1),
.cycle 20 1 false (-2),
.cycle 10 6 true (1),
.cycle 19 5 false (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 18 3 false (0),
.cycle 18 5 false (1),
.cycle 16 7 false (2),
.last 20 (2,true),
.last 14 (2,true),
.cycle 21 1 false (-1),
.cycle 15 2 false (-1),
.cycle 18 1 false (-2),
.cycle 21 10 false (1),
.cycle 16 6 false (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 15 4 false (1),
.cycle 16 6 false (2)
])
theorem kid22_part1306_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part1306) = true := by rfl

def kid22_part1307 : Audit := .cycle 9 2 true (3)
theorem kid22_part1307_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part1307) = true := by rfl

def kid22_part1308 : Audit := .cycle 0 11 true (0)
theorem kid22_part1308_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part1308) = true := by rfl

def kid22_part1309 : Audit := .cycle 1 10 true (1)
theorem kid22_part1309_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part1309) = true := by rfl

def kid22_part1310 : Audit := .cycle 2 9 true (1)
theorem kid22_part1310_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part1310) = true := by rfl

def kid22_part1311 : Audit := .cycle 1 13 true (1)
theorem kid22_part1311_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part1311) = true := by rfl

def kid22_part1312 : Audit := .cycle 8 3 true (3)
theorem kid22_part1312_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part1312) = true := by rfl

def kid22_part1313 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (4),
.cycle 8 5 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (4),
.cycle 3 9 true (1),
.cycle 10 4 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 10 3 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 8 6 true (3),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5)
])
theorem kid22_part1313_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part1313) = true := by rfl

def kid22_part1289 : Audit := .split 10 (4,true) (byMove [(kid22_part1290),(kid22_part1291),(kid22_part1292),(kid22_part1293),(kid22_part1294),(kid22_part1295),(kid22_part1296),(kid22_part1297),(kid22_part1298),(kid22_part1299),(kid22_part1300),(kid22_part1301),(kid22_part1302),(kid22_part1303),(kid22_part1304),(kid22_part1305),(kid22_part1306),(kid22_part1307),(kid22_part1308),(kid22_part1309),(kid22_part1310),(kid22_part1311),(kid22_part1312),(kid22_part1313)])

theorem kid22_part1289_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part1289) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid22_part1290),(kid22_part1291),(kid22_part1292),(kid22_part1293),(kid22_part1294),(kid22_part1295),(kid22_part1296),(kid22_part1297),(kid22_part1298),(kid22_part1299),(kid22_part1300),(kid22_part1301),(kid22_part1302),(kid22_part1303),(kid22_part1304),(kid22_part1305),(kid22_part1306),(kid22_part1307),(kid22_part1308),(kid22_part1309),(kid22_part1310),(kid22_part1311),(kid22_part1312),(kid22_part1313)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1290_checked

  · exact kid22_part1296_checked

  · exact kid22_part1302_checked

  · exact kid22_part1308_checked

  · exact kid22_part1291_checked

  · exact kid22_part1297_checked

  · exact kid22_part1303_checked

  · exact kid22_part1309_checked

  · exact kid22_part1292_checked

  · exact kid22_part1298_checked

  · exact kid22_part1304_checked

  · exact kid22_part1310_checked

  · exact kid22_part1293_checked

  · exact kid22_part1299_checked

  · exact kid22_part1305_checked

  · exact kid22_part1311_checked

  · exact kid22_part1294_checked

  · exact kid22_part1300_checked

  · exact kid22_part1306_checked

  · exact kid22_part1312_checked

  · exact kid22_part1295_checked

  · exact kid22_part1301_checked

  · exact kid22_part1307_checked

  · exact kid22_part1313_checked

def kid22_part1315 : Audit := .cycle 1 12 true (1)
theorem kid22_part1315_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1315) = true := by rfl

def kid22_part1316 : Audit := .cycle 7 5 true (3)
theorem kid22_part1316_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1316) = true := by rfl

def kid22_part1317 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 21 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.last 25 (4,true),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 11 2 true (4)
])
theorem kid22_part1317_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1317) = true := by rfl

def kid22_part1318 : Audit := .cycle 0 13 true (0)
theorem kid22_part1318_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1318) = true := by rfl

def kid22_part1319 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 17 2 false (-1),
.cycle 25 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 8 true (3),
.cycle 3 10 true (1),
.cycle 21 2 false (1),
.cycle 8 6 true (3),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 17 2 false (-1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 11 2 true (4)
])
theorem kid22_part1319_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1319) = true := by rfl

def kid22_part1320 : Audit := .cycle 10 2 true (4)
theorem kid22_part1320_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1320) = true := by rfl

def kid22_part1321 : Audit := .cycle 0 12 true (0)
theorem kid22_part1321_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1321) = true := by rfl

def kid22_part1322 : Audit := .cycle 1 11 true (1)
theorem kid22_part1322_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1322) = true := by rfl

def kid22_part1323 : Audit := .split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 23 (2,true),
.cycle 10 10 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 12 8 true (4),
.cycle 3 17 true (1),
.last 22 (2,true),
.cycle 10 20 true (4),
.cycle 6 14 true (2),
.cycle 18 2 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 23 (2,true),
.cycle 9 11 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (3),
.cycle 11 9 true (4)
])
theorem kid22_part1323_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1323) = true := by rfl

def kid22_part1324 : Audit := .cycle 3 9 true (1)
theorem kid22_part1324_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1324) = true := by rfl

def kid22_part1325 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 3 19 true (1),
.cycle 12 3 true (5),
.cycle 11 4 true (5),
.cycle 7 9 true (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 9 8 true (3),
.cycle 13 2 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5)
])
theorem kid22_part1325_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1325) = true := by rfl

def kid22_part1326 : Audit := .cycle 11 1 true (5)
theorem kid22_part1326_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1326) = true := by rfl

def kid22_part1327 : Audit := .cycle 6 6 true (2)
theorem kid22_part1327_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1327) = true := by rfl

def kid22_part1328 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 24 (2,true),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 8 true (4),
.cycle 3 11 true (1),
.last 22 (2,true),
.last 16 (2,true),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 24 (2,true),
.cycle 9 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (4)
])
theorem kid22_part1328_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1328) = true := by rfl

def kid22_part1329 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 9 7 true (3),
.last 21 (4,true),
.cycle 7 8 true (3),
.last 13 (4,true),
.last 21 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (4),
.last 15 (4,true),
.last 14 (4,true),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 9 5 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (4)
])
theorem kid22_part1329_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1329) = true := by rfl

def kid22_part1330 : Audit := .cycle 1 13 true (1)
theorem kid22_part1330_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1330) = true := by rfl

def kid22_part1331 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 9 7 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 17 2 false (-1),
.cycle 29 2 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 10 true (3),
.cycle 10 3 true (4),
.cycle 6 10 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 17 2 false (-1),
.cycle 9 5 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 10 3 true (4)
])
theorem kid22_part1331_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1331) = true := by rfl

def kid22_part1332 : Audit := .cycle 9 3 true (3)
theorem kid22_part1332_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1332) = true := by rfl

def kid22_part1333 : Audit := .cycle 0 12 true (0)
theorem kid22_part1333_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1333) = true := by rfl

def kid22_part1334 : Audit := .cycle 1 11 true (1)
theorem kid22_part1334_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1334) = true := by rfl

def kid22_part1335 : Audit := .cycle 2 10 true (1)
theorem kid22_part1335_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1335) = true := by rfl

def kid22_part1336 : Audit := .cycle 1 14 true (1)
theorem kid22_part1336_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1336) = true := by rfl

def kid22_part1337 : Audit := .cycle 8 4 true (3)
theorem kid22_part1337_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1337) = true := by rfl

def kid22_part1338 : Audit := .cycle 11 1 true (5)
theorem kid22_part1338_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1338) = true := by rfl

def kid22_part1314 : Audit := .split 11 (5,false) (byMove [(kid22_part1315),(kid22_part1316),(kid22_part1317),(kid22_part1318),(kid22_part1319),(kid22_part1320),(kid22_part1321),(kid22_part1322),(kid22_part1323),(kid22_part1324),(kid22_part1325),(kid22_part1326),(kid22_part1327),(kid22_part1328),(kid22_part1329),(kid22_part1330),(kid22_part1331),(kid22_part1332),(kid22_part1333),(kid22_part1334),(kid22_part1335),(kid22_part1336),(kid22_part1337),(kid22_part1338)])

theorem kid22_part1314_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part1314) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part1315),(kid22_part1316),(kid22_part1317),(kid22_part1318),(kid22_part1319),(kid22_part1320),(kid22_part1321),(kid22_part1322),(kid22_part1323),(kid22_part1324),(kid22_part1325),(kid22_part1326),(kid22_part1327),(kid22_part1328),(kid22_part1329),(kid22_part1330),(kid22_part1331),(kid22_part1332),(kid22_part1333),(kid22_part1334),(kid22_part1335),(kid22_part1336),(kid22_part1337),(kid22_part1338)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1315_checked

  · exact kid22_part1321_checked

  · exact kid22_part1327_checked

  · exact kid22_part1333_checked

  · exact kid22_part1316_checked

  · exact kid22_part1322_checked

  · exact kid22_part1328_checked

  · exact kid22_part1334_checked

  · exact kid22_part1317_checked

  · exact kid22_part1323_checked

  · exact kid22_part1329_checked

  · exact kid22_part1335_checked

  · exact kid22_part1318_checked

  · exact kid22_part1324_checked

  · exact kid22_part1330_checked

  · exact kid22_part1336_checked

  · exact kid22_part1319_checked

  · exact kid22_part1325_checked

  · exact kid22_part1331_checked

  · exact kid22_part1337_checked

  · exact kid22_part1320_checked

  · exact kid22_part1326_checked

  · exact kid22_part1332_checked

  · exact kid22_part1338_checked

def kid22_part954 : Audit := .split 9 (5,true) (byMove [(kid22_part955),(kid22_part980),(kid22_part981),(kid22_part1006),(kid22_part1007),(kid22_part1032),(kid22_part1057),(kid22_part1058),(kid22_part1059),(kid22_part1084),(kid22_part1085),(kid22_part1110),(kid22_part1135),(kid22_part1160),(kid22_part1185),(kid22_part1186),(kid22_part1211),(kid22_part1236),(kid22_part1261),(kid22_part1262),(kid22_part1263),(kid22_part1288),(kid22_part1289),(kid22_part1314)])

theorem kid22_part954_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (kid22_part954) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) 9 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part955),(kid22_part980),(kid22_part981),(kid22_part1006),(kid22_part1007),(kid22_part1032),(kid22_part1057),(kid22_part1058),(kid22_part1059),(kid22_part1084),(kid22_part1085),(kid22_part1110),(kid22_part1135),(kid22_part1160),(kid22_part1185),(kid22_part1186),(kid22_part1211),(kid22_part1236),(kid22_part1261),(kid22_part1262),(kid22_part1263),(kid22_part1288),(kid22_part1289),(kid22_part1314)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part955_checked

  · exact kid22_part1057_checked

  · exact kid22_part1135_checked

  · exact kid22_part1261_checked

  · exact kid22_part980_checked

  · exact kid22_part1058_checked

  · exact kid22_part1160_checked

  · exact kid22_part1262_checked

  · exact kid22_part981_checked

  · exact kid22_part1059_checked

  · exact kid22_part1185_checked

  · exact kid22_part1263_checked

  · exact kid22_part1006_checked

  · exact kid22_part1084_checked

  · exact kid22_part1186_checked

  · exact kid22_part1288_checked

  · exact kid22_part1007_checked

  · exact kid22_part1085_checked

  · exact kid22_part1211_checked

  · exact kid22_part1289_checked

  · exact kid22_part1032_checked

  · exact kid22_part1110_checked

  · exact kid22_part1236_checked

  · exact kid22_part1314_checked

def kid22_part1339 : Audit := .cycle 0 9 true (0)
theorem kid22_part1339_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,0⟩)) (kid22_part1339) = true := by rfl

def kid22_part1340 : Audit := .cycle 1 8 true (1)
theorem kid22_part1340_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,1⟩)) (kid22_part1340) = true := by rfl

def kid22_part1341 : Audit := .cycle 2 7 true (1)
theorem kid22_part1341_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,2⟩)) (kid22_part1341) = true := by rfl

def kid22_part1342 : Audit := .cycle 1 11 true (1)
theorem kid22_part1342_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,3⟩)) (kid22_part1342) = true := by rfl

def kid22_part1343 : Audit := .cycle 8 1 true (4)
theorem kid22_part1343_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,4⟩)) (kid22_part1343) = true := by rfl

def kid22_part1345 : Audit := .cycle 1 10 true (1)
theorem kid22_part1345_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid22_part1345) = true := by rfl

def kid22_part1346 : Audit := .cycle 7 3 true (3)
theorem kid22_part1346_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid22_part1346) = true := by rfl

def kid22_part1348 : Audit := .cycle 1 11 true (1)
theorem kid22_part1348_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part1348) = true := by rfl

def kid22_part1349 : Audit := .cycle 7 4 true (3)
theorem kid22_part1349_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part1349) = true := by rfl

def kid22_part1350 : Audit := .split 19 (4,true) (byMove [
.cycle 33 1 false (5),
.cycle 26 1 false (2),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 25 1 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 56 1 false (6),
.cycle 12 8 true (0),
.cycle 30 1 false (4),
.cycle 34 1 false (4),
.cycle 32 1 false (4),
.cycle 27 1 false (3),
.cycle 18 2 true (2),
.cycle 22 1 false (2),
.cycle 34 1 false (6),
.last 22 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.cycle 26 1 false (2),
.cycle 24 1 false (2)
])
theorem kid22_part1350_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part1350) = true := by rfl

def kid22_part1351 : Audit := .cycle 0 12 true (0)
theorem kid22_part1351_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part1351) = true := by rfl

def kid22_part1352 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 20 3 false (2),
.cycle 21 1 false (1),
.cycle 19 3 false (0),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 28 1 false (4),
.cycle 0 21 true (0),
.cycle 25 3 false (2),
.last 22 (5,true),
.cycle 6 12 true (2),
.cycle 17 2 true (0),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.last 13 (5,true),
.last 20 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 21 3 false (1)
])
theorem kid22_part1352_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part1352) = true := by rfl

def kid22_part1353 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 23 (4,true),
.last 21 (4,true),
.cycle 6 12 true (2),
.last 19 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 29 1 false (1)
])
theorem kid22_part1353_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part1353) = true := by rfl

def kid22_part1354 : Audit := .cycle 0 11 true (0)
theorem kid22_part1354_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part1354) = true := by rfl

def kid22_part1355 : Audit := .cycle 1 10 true (1)
theorem kid22_part1355_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part1355) = true := by rfl

def kid22_part1356 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 40 1 false (8),
.cycle 0 20 true (0),
.cycle 39 1 false (3),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 26, 64],[2, 16, 4, 1, 16, 64, 64],64⟩,
.cycle 2 18 true (1),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.cycle 42 1 false (10),
.cycle 1 20 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 9 10 true (3)
])
theorem kid22_part1356_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part1356) = true := by rfl

def kid22_part1357 : Audit := .cycle 3 8 true (1)
theorem kid22_part1357_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part1357) = true := by rfl

def kid22_part1358 : Audit := .cycle 8 3 true (4)
theorem kid22_part1358_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part1358) = true := by rfl

def kid22_part1359 : Audit := .cycle 2 10 true (1)
theorem kid22_part1359_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part1359) = true := by rfl

def kid22_part1360 : Audit := .cycle 6 5 true (2)
theorem kid22_part1360_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part1360) = true := by rfl

def kid22_part1361 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.cycle 21 8 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.cycle 10 7 true (3),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 23 5 false (1),
.cycle 1 14 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 9 4 true (3)
])
theorem kid22_part1361_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part1361) = true := by rfl

def kid22_part1362 : Audit := .cycle 1 14 true (1)
theorem kid22_part1362_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part1362) = true := by rfl

def kid22_part1363 : Audit := .cycle 1 12 true (1)
theorem kid22_part1363_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part1363) = true := by rfl

def kid22_part1364 : Audit := .split 11 (4,true) (byMove [
.cycle 10 8 true (2),
.cycle 0 15 true (0),
.last 22 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 17 (5,true),
.last 12 (5,true),
.cycle 6 9 true (2),
.cycle 17 2 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.last 13 (5,true),
.last 20 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.last 12 (5,true)
])
theorem kid22_part1364_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part1364) = true := by rfl

def kid22_part1365 : Audit := .split 11 (5,true) (byMove [
.cycle 10 8 true (2),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 0 20 true (0),
.cycle 19 1 false (-1),
.cycle 25 1 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 23 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3)
])
theorem kid22_part1365_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part1365) = true := by rfl

def kid22_part1366 : Audit := .cycle 0 11 true (0)
theorem kid22_part1366_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part1366) = true := by rfl

def kid22_part1367 : Audit := .cycle 1 10 true (1)
theorem kid22_part1367_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part1367) = true := by rfl

def kid22_part1368 : Audit := .cycle 2 9 true (1)
theorem kid22_part1368_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part1368) = true := by rfl

def kid22_part1369 : Audit := .cycle 1 13 true (1)
theorem kid22_part1369_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part1369) = true := by rfl

def kid22_part1370 : Audit := .cycle 8 3 true (4)
theorem kid22_part1370_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part1370) = true := by rfl

def kid22_part1371 : Audit := .cycle 9 2 true (4)
theorem kid22_part1371_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part1371) = true := by rfl

def kid22_part1347 : Audit := .split 10 (2,true) (byMove [(kid22_part1348),(kid22_part1349),(kid22_part1350),(kid22_part1351),(kid22_part1352),(kid22_part1353),(kid22_part1354),(kid22_part1355),(kid22_part1356),(kid22_part1357),(kid22_part1358),(kid22_part1359),(kid22_part1360),(kid22_part1361),(kid22_part1362),(kid22_part1363),(kid22_part1364),(kid22_part1365),(kid22_part1366),(kid22_part1367),(kid22_part1368),(kid22_part1369),(kid22_part1370),(kid22_part1371)])

theorem kid22_part1347_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid22_part1347) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid22_part1348),(kid22_part1349),(kid22_part1350),(kid22_part1351),(kid22_part1352),(kid22_part1353),(kid22_part1354),(kid22_part1355),(kid22_part1356),(kid22_part1357),(kid22_part1358),(kid22_part1359),(kid22_part1360),(kid22_part1361),(kid22_part1362),(kid22_part1363),(kid22_part1364),(kid22_part1365),(kid22_part1366),(kid22_part1367),(kid22_part1368),(kid22_part1369),(kid22_part1370),(kid22_part1371)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1348_checked

  · exact kid22_part1354_checked

  · exact kid22_part1360_checked

  · exact kid22_part1366_checked

  · exact kid22_part1349_checked

  · exact kid22_part1355_checked

  · exact kid22_part1361_checked

  · exact kid22_part1367_checked

  · exact kid22_part1350_checked

  · exact kid22_part1356_checked

  · exact kid22_part1362_checked

  · exact kid22_part1368_checked

  · exact kid22_part1351_checked

  · exact kid22_part1357_checked

  · exact kid22_part1363_checked

  · exact kid22_part1369_checked

  · exact kid22_part1352_checked

  · exact kid22_part1358_checked

  · exact kid22_part1364_checked

  · exact kid22_part1370_checked

  · exact kid22_part1353_checked

  · exact kid22_part1359_checked

  · exact kid22_part1365_checked

  · exact kid22_part1371_checked

def kid22_part1372 : Audit := .cycle 0 11 true (0)
theorem kid22_part1372_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid22_part1372) = true := by rfl

def kid22_part1373 : Audit := .split 10 (4,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 29 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 38 1 false (10),
.cycle 21 1 false (3),
.last 26 (5,true),
.cycle 30 1 false (2),
.cycle 6 12 true (2),
.cycle 21 5 false (1),
.cycle 0 14 true (0),
.cycle 19 1 false (1),
.last 13 (5,true),
.cycle 22 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 26 1 false (2)
]),
.cycle 0 12 true (0),
.cycle 18 3 false (0),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 15 4 false (1),
.cycle 17 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 38 1 false (10),
.cycle 21 1 false (3),
.cycle 19 4 false (1),
.cycle 21 4 false (1),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 1 false (1),
.cycle 15 4 false (1),
.cycle 17 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 19 4 false (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 10 8 true (3),
.cycle 3 8 true (1),
.cycle 8 3 true (4),
.cycle 8 4 true (4),
.cycle 6 5 true (2),
.cycle 10 2 true (3),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 18 (5,true),
.cycle 14 9 true (1),
.last 26 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 30 1 false (8),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 12 (5,true),
.cycle 10 8 true (2),
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.cycle 19 1 false (1),
.last 13 (5,true),
.last 27 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true)
]),
.cycle 1 12 true (1),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 32, 63, 64],[2, 16, 64, 1, 59, 40, 64],64⟩,
.last 14 (2,true),
.cycle 19 8 true (2),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 0, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 10 6 true (2),
.cycle 21 5 false (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 1 14 true (1),
.cycle 25 7 false (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 0, 64],[2, 16, 64, 1, 32, 32, 64],64⟩
]),
.split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 15 4 false (1),
.cycle 17 4 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 4 false (1),
.cycle 21 4 false (1),
.cycle 10 8 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 19 1 false (1),
.cycle 15 4 false (1),
.cycle 17 4 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid22_part1373_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid22_part1373) = true := by rfl

def kid22_part1374 : Audit := .split 10 (5,true) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (3),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 29 1 false (1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 23 (4,true),
.cycle 18 1 false (0),
.cycle 6 12 true (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 18 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.last 21 (4,true)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 19 3 false (0),
.cycle 13 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 25 3 false (2),
.cycle 15 3 false (1),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 31 1 false (5),
.cycle 18 3 false (0),
.cycle 13 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (3),
.cycle 21 3 false (1)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 39 1 false (3),
.cycle 40 1 false (8),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 3 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 62, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.last 35 (2,true),
.cycle 6 13 true (2),
.cycle 17 2 true (5),
.last 19 (2,true),
.cycle 1 20 true (1),
.last 22 (2,true),
.last 20 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (3),
.cycle 9 10 true (3)
]),
.cycle 3 8 true (1),
.cycle 8 3 true (4),
.cycle 19 1 false (1),
.cycle 6 5 true (2),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 18 (2,true),
.last 15 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 8 true (3),
.cycle 3 10 true (1),
.last 17 (2,true),
.last 17 (2,true),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 23 5 false (1),
.last 15 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (3),
.cycle 9 4 true (3)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 18 7 true (2),
.last 23 (4,true),
.cycle 0 21 true (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 22 1 false (0),
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
.cycle 0 15 true (0),
.last 20 (2,true),
.cycle 18 7 true (2),
.cycle 18 6 false (0),
.cycle 18 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 7 true (3),
.cycle 10 4 true (3),
.cycle 6 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 18 3 false (0),
.cycle 18 1 false (-2),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 10 2 true (3)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid22_part1374_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid22_part1374) = true := by rfl

def kid22_part1375 : Audit := .cycle 0 10 true (0)
theorem kid22_part1375_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid22_part1375) = true := by rfl

def kid22_part1376 : Audit := .cycle 1 9 true (1)
theorem kid22_part1376_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid22_part1376) = true := by rfl

def kid22_part1377 : Audit := .split 17 (4,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (3),
.split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 40 1 false (2),
.cycle 3 16 true (1),
.cycle 8 11 true (4),
.cycle 45 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 32 true (1),
.cycle 39 1 false (3),
.cycle 8 11 true (4),
.last 34 (5,true),
.cycle 7 13 true (3),
.cycle 41 5 false (1),
.cycle 0 21 true (0),
.cycle 35 1 false (1),
.last 20 (5,true),
.cycle 18 2 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (4),
.cycle 9 10 true (4)
]),
.cycle 0 19 true (0),
.cycle 8 11 true (4),
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 40 1 false (2),
.cycle 3 16 true (1),
.cycle 8 11 true (4),
.cycle 45 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 32 true (1),
.cycle 39 1 false (3),
.cycle 8 11 true (4),
.last 33 (2,true),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 35 1 false (1),
.cycle 0 25 true (0),
.last 20 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 11 true (4),
.cycle 9 10 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 8 true (4),
.cycle 3 15 true (1),
.cycle 8 10 true (4),
.split 28 (5,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 8 21 true (4),
.cycle 9 20 true (4),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 19 10 true (6),
.cycle 11 18 true (4),
.cycle 8 21 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 4 25 true (1),
.cycle 27 4 true (9),
.last 30 (2,true),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 8 21 true (4),
.cycle 9 20 true (4)
]),
.cycle 6 12 true (2),
.cycle 16 2 true (6),
.split 18 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 0 22 true (0),
.cycle 40 1 false (2),
.last 25 (5,true),
.cycle 8 14 true (4),
.cycle 0 22 true (0),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 63 1 false (13),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.last 19 (5,true),
.cycle 15 8 true (5),
.cycle 41 5 false (1),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.last 20 (5,true),
.cycle 18 2 true (5),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.cycle 17 2 true (6),
.last 19 (5,true)
]),
.cycle 1 19 true (1),
.split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 7 17 true (3),
.last 21 (2,true),
.cycle 7 16 true (3),
.cycle 32 3 false (0),
.cycle 52 1 false (2),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 8 16 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 15 6 true (5),
.cycle 39 5 false (1),
.last 21 (2,true),
.cycle 5 16 true (1),
.cycle 32 3 false (0),
.last 23 (2,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 38 5 false (2),
.cycle 9 13 true (4)
]),
.split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 40 1 false (2),
.cycle 0 27 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.last 21 (2,true),
.cycle 72 1 false (16),
.cycle 15 8 true (5),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.last 23 (2,true),
.last 20 (2,true),
.cycle 1 19 true (1),
.cycle 7 12 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 17 2 true (6),
.cycle 9 11 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (4),
.cycle 9 9 true (4)
])
theorem kid22_part1377_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid22_part1377) = true := by rfl

def kid22_part1378 : Audit := .cycle 3 7 true (1)
theorem kid22_part1378_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid22_part1378) = true := by rfl

def kid22_part1379 : Audit := .cycle 8 2 true (4)
theorem kid22_part1379_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid22_part1379) = true := by rfl

def kid22_part1380 : Audit := .cycle 9 1 true (5)
theorem kid22_part1380_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid22_part1380) = true := by rfl

def kid22_part1381 : Audit := .cycle 6 4 true (2)
theorem kid22_part1381_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid22_part1381) = true := by rfl

def kid22_part1382 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 24 1 false (2),
.cycle 0 14 true (0),
.cycle 20 5 false (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 12 3 true (4),
.cycle 6 7 true (2),
.cycle 25 5 false (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 24 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4)
]),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 16 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.last 15 (2,true),
.cycle 6 7 true (2),
.last 17 (2,true),
.last 13 (2,true),
.cycle 1 14 true (1),
.last 16 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 8 true (4),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 32 1 false (2),
.cycle 0 16 true (0),
.cycle 11 4 true (5),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (4),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 12 3 true (5),
.cycle 6 9 true (2),
.cycle 10 5 true (4),
.cycle 5 24 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4)
]),
.cycle 6 6 true (2),
.cycle 10 2 true (4),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 24 1 false (2),
.cycle 7 8 true (3),
.last 67 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 49 1 false (11),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.last 13 (5,true),
.cycle 10 8 true (3),
.cycle 25 5 false (1),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.cycle 5 10 true (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 11 2 true (4),
.last 13 (5,true)
]),
.cycle 1 13 true (1),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 3072, 2048, 4096, 128, 256, 8, 2, 2048, 2048, 4096],[2, 1024, 4096, 1, 2048, 8, 2, 1024, 4096, 1, 2048, 2048, 4096],4128⟩,
.last 16 (2,true),
.cycle 10 8 true (2),
.cycle 20 3 false (0),
.last 26 (2,true),
.cycle 6 10 true (2),
.cycle 7 14 true (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 16 10 true (3),
.last 20 (2,true),
.cycle 12 6 true (2),
.cycle 23 5 false (1),
.last 16 (2,true),
.cycle 5 18 true (1),
.cycle 20 3 false (0),
.last 26 (2,true),
.cycle 6 10 true (2),
.cycle 25 7 false (3),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 22 5 false (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 3072, 2048, 4096, 128, 256, 8, 2, 2048, 2048, 4096],[2, 1024, 4096, 1, 2048, 2048, 2, 1024, 4096, 1, 2048, 2048, 4096],4128⟩
]),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 7 9 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.last 16 (2,true),
.last 16 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 21 (2,true),
.last 16 (2,true),
.cycle 10 8 true (3),
.last 17 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.last 16 (2,true),
.last 16 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (4),
.cycle 9 5 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1382_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid22_part1382) = true := by rfl

def kid22_part1384 : Audit := .cycle 1 14 true (1)
theorem kid22_part1384_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid22_part1384) = true := by rfl

def kid22_part1385 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 7 8 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 19 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 0 20 true (0),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 10 4 true (3),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 21 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1385_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid22_part1385) = true := by rfl

def kid22_part1386 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 26 1 false (2),
.cycle 22 1 false (2),
.cycle 27 1 false (3),
.cycle 25 1 false (1),
.last 20 (5,true),
.cycle 38 1 false (4),
.cycle 34 1 false (4),
.cycle 0 22 true (0),
.cycle 36 1 false (6),
.last 21 (5,true),
.last 46 (5,true),
.last 23 (5,true),
.cycle 18 2 true (2),
.cycle 22 1 false (2),
.cycle 26 1 false (4),
.last 22 (5,true),
.last 20 (5,true),
.cycle 30 1 false (2),
.cycle 26 1 false (2),
.cycle 0 22 true (0),
.cycle 4 16 true (0),
.last 21 (5,true),
.cycle 24 1 false (2)
])
theorem kid22_part1386_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid22_part1386) = true := by rfl

def kid22_part1387 : Audit := .cycle 7 6 true (3)
theorem kid22_part1387_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid22_part1387) = true := by rfl

def kid22_part1388 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 7 13 true (2),
.cycle 20 3 false (2),
.cycle 21 1 false (1),
.cycle 19 3 false (0),
.last 19 (5,true),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 0 49 true (0),
.last 13 (5,true),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 17 2 true (0),
.last 57 (5,true),
.cycle 23 1 false (3),
.last 13 (5,true),
.cycle 1 22 true (1),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.cycle 21 3 false (1)
])
theorem kid22_part1388_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid22_part1388) = true := by rfl

def kid22_part1389 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 19 (4,true),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.last 19 (4,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 263170, 2048, 65553, 128, 256, 32768, 2, 2048, 66576, 2, 4, 8, 1024, 32, 1, 262144],[2, 1024, 2208, 1, 262144, 16, 8192, 1024, 2080, 4096, 262144, 65536, 2, 16, 2080, 1, 262144, 16, 262144],286732⟩,
.cycle 1 15 true (1),
.cycle 6 10 true (2),
.last 19 (4,true),
.cycle 18 10 true (2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 1 22 true (1),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 6 true (3),
.last 19 (4,true)
])
theorem kid22_part1389_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid22_part1389) = true := by rfl

def kid22_part1390 : Audit := .cycle 1 11 true (1)
theorem kid22_part1390_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid22_part1390) = true := by rfl

def kid22_part1391 : Audit := .cycle 7 4 true (3)
theorem kid22_part1391_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid22_part1391) = true := by rfl

def kid22_part1392 : Audit := .split 20 (4,true) (byMove [
.cycle 1 32 true (1),
.last 23 (5,true),
.cycle 0 24 true (0),
.cycle 7 16 true (3),
.cycle 0 28 true (0),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 11 10 true (3),
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 5, 64],[2, 16, 4, 1, 16, 64, 64],64⟩,
.last 21 (5,true),
.cycle 6 18 true (2),
.cycle 19 2 true (5),
.cycle 47 1 false (11),
.cycle 5 16 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 2 28 true (1),
.cycle 0 22 true (0),
.cycle 8 14 true (3),
.last 21 (5,true)
])
theorem kid22_part1392_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid22_part1392) = true := by rfl

def kid22_part1393 : Audit := .cycle 0 12 true (0)
theorem kid22_part1393_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid22_part1393) = true := by rfl

def kid22_part1394 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 0 18 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 5, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.cycle 3 16 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.cycle 5 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1394_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid22_part1394) = true := by rfl

def kid22_part1395 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 0 18 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,true),
.last 18 (4,true),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (4,true),
.cycle 5 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1395_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid22_part1395) = true := by rfl

def kid22_part1396 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 7 9 true (3),
.cycle 0 15 true (0),
.cycle 28 8 false (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 8 true (3),
.cycle 3 11 true (1),
.cycle 12 6 true (4),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 10 8 true (3),
.cycle 1 15 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1396_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid22_part1396) = true := by rfl

def kid22_part1397 : Audit := .split 12 (4,true) (byMove [
.cycle 1 18 true (1),
.last 15 (5,true),
.cycle 23 5 false (1),
.cycle 7 8 true (3),
.cycle 21 8 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 16 8 true (4),
.cycle 0 14 true (0),
.cycle 10 8 true (3),
.last 13 (5,true),
.cycle 6 10 true (2),
.cycle 11 2 true (3),
.cycle 23 5 false (1),
.cycle 5 8 true (1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.last 13 (5,true)
])
theorem kid22_part1397_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid22_part1397) = true := by rfl

def kid22_part1398 : Audit := .cycle 5 8 true (1)
theorem kid22_part1398_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid22_part1398) = true := by rfl

def kid22_part1399 : Audit := .cycle 5 6 true (1)
theorem kid22_part1399_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid22_part1399) = true := by rfl

def kid22_part1400 : Audit := .split 11 (4,true) (byMove [
.cycle 10 8 true (2),
.cycle 1 15 true (1),
.last 22 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.last 18 (5,true),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.last 14 (5,true),
.cycle 1 13 true (1),
.last 18 (5,true),
.last 12 (5,true),
.cycle 6 12 true (2),
.cycle 17 2 true (0),
.cycle 5 8 true (1),
.cycle 35 1 false (7),
.last 13 (5,true),
.last 18 (5,true),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.cycle 10 2 true (3),
.cycle 1 13 true (1),
.cycle 8 6 true (3),
.last 12 (5,true)
])
theorem kid22_part1400_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid22_part1400) = true := by rfl

def kid22_part1401 : Audit := .split 11 (5,true) (byMove [
.cycle 10 8 true (2),
.cycle 1 15 true (1),
.last 19 (4,true),
.last 29 (4,true),
.last 22 (4,true),
.last 17 (4,true),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 5 10 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 0 17 true (0),
.last 14 (4,true),
.last 19 (4,true),
.cycle 5 8 true (1),
.last 17 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 10 2 true (3),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 5 true (3)
])
theorem kid22_part1401_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid22_part1401) = true := by rfl

def kid22_part1402 : Audit := .cycle 1 11 true (1)
theorem kid22_part1402_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid22_part1402) = true := by rfl

def kid22_part1403 : Audit := .cycle 7 4 true (3)
theorem kid22_part1403_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid22_part1403) = true := by rfl

def kid22_part1404 : Audit := .cycle 2 10 true (1)
theorem kid22_part1404_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid22_part1404) = true := by rfl

def kid22_part1405 : Audit := .cycle 0 12 true (0)
theorem kid22_part1405_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid22_part1405) = true := by rfl

def kid22_part1406 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (4),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (4),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 11 2 true (4),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 15 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1406_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid22_part1406) = true := by rfl

def kid22_part1407 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 17 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 19 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1407_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid22_part1407) = true := by rfl

def kid22_part1383 : Audit := .split 10 (2,true) (byMove [(kid22_part1384),(kid22_part1385),(kid22_part1386),(kid22_part1387),(kid22_part1388),(kid22_part1389),(kid22_part1390),(kid22_part1391),(kid22_part1392),(kid22_part1393),(kid22_part1394),(kid22_part1395),(kid22_part1396),(kid22_part1397),(kid22_part1398),(kid22_part1399),(kid22_part1400),(kid22_part1401),(kid22_part1402),(kid22_part1403),(kid22_part1404),(kid22_part1405),(kid22_part1406),(kid22_part1407)])

theorem kid22_part1383_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid22_part1383) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid22_part1384),(kid22_part1385),(kid22_part1386),(kid22_part1387),(kid22_part1388),(kid22_part1389),(kid22_part1390),(kid22_part1391),(kid22_part1392),(kid22_part1393),(kid22_part1394),(kid22_part1395),(kid22_part1396),(kid22_part1397),(kid22_part1398),(kid22_part1399),(kid22_part1400),(kid22_part1401),(kid22_part1402),(kid22_part1403),(kid22_part1404),(kid22_part1405),(kid22_part1406),(kid22_part1407)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1384_checked

  · exact kid22_part1390_checked

  · exact kid22_part1396_checked

  · exact kid22_part1402_checked

  · exact kid22_part1385_checked

  · exact kid22_part1391_checked

  · exact kid22_part1397_checked

  · exact kid22_part1403_checked

  · exact kid22_part1386_checked

  · exact kid22_part1392_checked

  · exact kid22_part1398_checked

  · exact kid22_part1404_checked

  · exact kid22_part1387_checked

  · exact kid22_part1393_checked

  · exact kid22_part1399_checked

  · exact kid22_part1405_checked

  · exact kid22_part1388_checked

  · exact kid22_part1394_checked

  · exact kid22_part1400_checked

  · exact kid22_part1406_checked

  · exact kid22_part1389_checked

  · exact kid22_part1395_checked

  · exact kid22_part1401_checked

  · exact kid22_part1407_checked

def kid22_part1408 : Audit := .cycle 1 11 true (1)
theorem kid22_part1408_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid22_part1408) = true := by rfl

def kid22_part1410 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 29 1 false (3),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 22 true (1),
.cycle 3 11 true (1),
.cycle 12 6 true (4),
.last 16 (5,true),
.cycle 6 8 true (2),
.cycle 1 16 true (1),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.cycle 10 8 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1410_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid22_part1410) = true := by rfl

def kid22_part1411 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 8 true (3),
.cycle 19 4 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 15 true (3),
.cycle 3 11 true (1),
.cycle 0 20 true (0),
.cycle 12 3 true (4),
.cycle 6 8 true (2),
.cycle 7 9 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 19 4 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1411_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid22_part1411) = true := by rfl

def kid22_part1412 : Audit := .split 11 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 20 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 27 1 false (1),
.last 14 (5,true),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.last 13 (5,true),
.last 14 (5,true),
.last 15 (5,true),
.cycle 21 5 false (1),
.cycle 1 29 true (1),
.cycle 19 1 false (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.cycle 26 1 false (2)
])
theorem kid22_part1412_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid22_part1412) = true := by rfl

def kid22_part1413 : Audit := .cycle 7 6 true (3)
theorem kid22_part1413_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid22_part1413) = true := by rfl

def kid22_part1414 : Audit := .cycle 18 3 false (0)
theorem kid22_part1414_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid22_part1414) = true := by rfl

def kid22_part1415 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 20 true (1),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 16 4 false (0),
.cycle 15 4 false (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 15 3 true (5),
.cycle 6 10 true (2),
.last 13 (2,true),
.last 20 (2,true),
.cycle 19 1 false (1),
.cycle 16 4 false (0),
.cycle 15 4 false (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 6 true (3),
.cycle 19 8 false (2)
])
theorem kid22_part1415_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid22_part1415) = true := by rfl

def kid22_part1416 : Audit := .cycle 1 11 true (1)
theorem kid22_part1416_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid22_part1416) = true := by rfl

def kid22_part1417 : Audit := .cycle 7 4 true (3)
theorem kid22_part1417_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid22_part1417) = true := by rfl

def kid22_part1418 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.last 17 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 10 true (3),
.cycle 12 8 true (3),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 7 6 true (3),
.cycle 14 8 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.last 17 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1418_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid22_part1418) = true := by rfl

def kid22_part1419 : Audit := .cycle 0 12 true (0)
theorem kid22_part1419_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid22_part1419) = true := by rfl

def kid22_part1420 : Audit := .cycle 8 4 true (4)
theorem kid22_part1420_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid22_part1420) = true := by rfl

def kid22_part1421 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 21 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 10 true (3),
.cycle 3 19 true (1),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 10 4 true (4),
.cycle 21 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1421_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid22_part1421) = true := by rfl

def kid22_part1422 : Audit := .cycle 6 8 true (2)
theorem kid22_part1422_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid22_part1422) = true := by rfl

def kid22_part1423 : Audit := .cycle 10 2 true (3)
theorem kid22_part1423_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid22_part1423) = true := by rfl

def kid22_part1424 : Audit := .split 11 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 1 15 true (1),
.cycle 22 1 false (2),
.last 18 (5,true),
.cycle 5 20 true (1),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.cycle 33 1 false (9),
.cycle 1 13 true (1),
.cycle 1 15 true (1),
.last 12 (5,true),
.cycle 10 8 true (2),
.cycle 21 5 false (1),
.cycle 5 8 true (1),
.cycle 19 1 false (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (3),
.last 12 (5,true)
])
theorem kid22_part1424_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid22_part1424) = true := by rfl

def kid22_part1425 : Audit := .cycle 5 6 true (1)
theorem kid22_part1425_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid22_part1425) = true := by rfl

def kid22_part1426 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 32, 59, 64],[2, 16, 64, 1, 59, 40, 64],64⟩,
.last 14 (2,true),
.cycle 10 8 true (2),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 6 8 true (2),
.cycle 7 12 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 8 true (3),
.cycle 15 3 true (5),
.cycle 10 6 true (2),
.cycle 21 5 false (1),
.last 14 (2,true),
.cycle 5 16 true (1),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 6 8 true (2),
.cycle 23 7 false (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩
])
theorem kid22_part1426_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid22_part1426) = true := by rfl

def kid22_part1427 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 22 1 false (2),
.cycle 18 12 true (3),
.cycle 16 4 false (0),
.cycle 15 4 false (1),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 18 6 false (2),
.cycle 13 3 true (5),
.cycle 10 8 true (2),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 19 1 false (1),
.cycle 16 4 false (0),
.cycle 15 4 false (1),
.cycle 6 6 true (2),
.cycle 7 8 true (3),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1427_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid22_part1427) = true := by rfl

def kid22_part1428 : Audit := .cycle 1 11 true (1)
theorem kid22_part1428_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid22_part1428) = true := by rfl

def kid22_part1429 : Audit := .cycle 7 4 true (3)
theorem kid22_part1429_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid22_part1429) = true := by rfl

def kid22_part1430 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 20 true (0),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 5 10 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1430_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid22_part1430) = true := by rfl

def kid22_part1431 : Audit := .cycle 0 12 true (0)
theorem kid22_part1431_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid22_part1431) = true := by rfl

def kid22_part1432 : Audit := .cycle 8 4 true (4)
theorem kid22_part1432_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid22_part1432) = true := by rfl

def kid22_part1433 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (4),
.cycle 17 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (4),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.cycle 6 6 true (2),
.cycle 9 5 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.cycle 17 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1433_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid22_part1433) = true := by rfl

def kid22_part1409 : Audit := .split 10 (4,true) (byMove [(kid22_part1410),(kid22_part1411),(kid22_part1412),(kid22_part1413),(kid22_part1414),(kid22_part1415),(kid22_part1416),(kid22_part1417),(kid22_part1418),(kid22_part1419),(kid22_part1420),(kid22_part1421),(kid22_part1422),(kid22_part1423),(kid22_part1424),(kid22_part1425),(kid22_part1426),(kid22_part1427),(kid22_part1428),(kid22_part1429),(kid22_part1430),(kid22_part1431),(kid22_part1432),(kid22_part1433)])

theorem kid22_part1409_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid22_part1409) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid22_part1410),(kid22_part1411),(kid22_part1412),(kid22_part1413),(kid22_part1414),(kid22_part1415),(kid22_part1416),(kid22_part1417),(kid22_part1418),(kid22_part1419),(kid22_part1420),(kid22_part1421),(kid22_part1422),(kid22_part1423),(kid22_part1424),(kid22_part1425),(kid22_part1426),(kid22_part1427),(kid22_part1428),(kid22_part1429),(kid22_part1430),(kid22_part1431),(kid22_part1432),(kid22_part1433)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1410_checked

  · exact kid22_part1416_checked

  · exact kid22_part1422_checked

  · exact kid22_part1428_checked

  · exact kid22_part1411_checked

  · exact kid22_part1417_checked

  · exact kid22_part1423_checked

  · exact kid22_part1429_checked

  · exact kid22_part1412_checked

  · exact kid22_part1418_checked

  · exact kid22_part1424_checked

  · exact kid22_part1430_checked

  · exact kid22_part1413_checked

  · exact kid22_part1419_checked

  · exact kid22_part1425_checked

  · exact kid22_part1431_checked

  · exact kid22_part1414_checked

  · exact kid22_part1420_checked

  · exact kid22_part1426_checked

  · exact kid22_part1432_checked

  · exact kid22_part1415_checked

  · exact kid22_part1421_checked

  · exact kid22_part1427_checked

  · exact kid22_part1433_checked

def kid22_part1435 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 12 6 true (4),
.cycle 0 21 true (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 10 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1435_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid22_part1435) = true := by rfl

def kid22_part1436 : Audit := .cycle 7 7 true (3)
theorem kid22_part1436_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid22_part1436) = true := by rfl

def kid22_part1437 : Audit := .split 11 (2,true) (byMove [
.cycle 0 16 true (0),
.last 19 (4,true),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 21 (4,true),
.cycle 16 1 false (0),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 27 (4,true),
.cycle 18 1 false (0),
.cycle 6 11 true (2),
.last 15 (4,true),
.cycle 1 29 true (1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 16 1 false (0),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 7 true (3),
.last 21 (4,true)
])
theorem kid22_part1437_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid22_part1437) = true := by rfl

def kid22_part1438 : Audit := .cycle 7 6 true (3)
theorem kid22_part1438_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid22_part1438) = true := by rfl

def kid22_part1439 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 19 3 false (0),
.cycle 13 3 false (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 0 49 true (0),
.cycle 46 3 false (7),
.cycle 15 3 false (1),
.cycle 6 11 true (2),
.last 13 (2,true),
.last 20 (2,true),
.last 21 (2,true),
.cycle 18 3 false (0),
.cycle 13 3 false (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 7 true (3),
.cycle 21 3 false (1)
])
theorem kid22_part1439_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid22_part1439) = true := by rfl

def kid22_part1440 : Audit := .cycle 15 1 false (-1)
theorem kid22_part1440_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid22_part1440) = true := by rfl

def kid22_part1441 : Audit := .cycle 1 11 true (1)
theorem kid22_part1441_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid22_part1441) = true := by rfl

def kid22_part1442 : Audit := .cycle 7 4 true (3)
theorem kid22_part1442_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid22_part1442) = true := by rfl

def kid22_part1443 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 20 (4,true),
.last 18 (4,true),
.cycle 8 4 true (4),
.cycle 34 1 false (8),
.cycle 7 6 true (3),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 21 (4,true),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1443_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid22_part1443) = true := by rfl

def kid22_part1444 : Audit := .cycle 0 12 true (0)
theorem kid22_part1444_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid22_part1444) = true := by rfl

def kid22_part1445 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (2,true),
.cycle 3 16 true (1),
.cycle 8 4 true (4),
.cycle 34 1 false (8),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 6 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1445_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid22_part1445) = true := by rfl

def kid22_part1446 : Audit := .cycle 34 1 false (8)
theorem kid22_part1446_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid22_part1446) = true := by rfl

def kid22_part1447 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 28 8 false (2),
.cycle 7 9 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 8 true (3),
.cycle 3 11 true (1),
.cycle 12 6 true (4),
.cycle 7 15 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 6 true (3),
.cycle 10 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (3),
.cycle 9 5 true (3)
])
theorem kid22_part1447_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid22_part1447) = true := by rfl

def kid22_part1448 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 7 11 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.last 18 (2,true),
.last 15 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 18 (2,true),
.last 15 (2,true),
.cycle 6 10 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 23 5 false (1),
.last 15 (2,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 9 7 true (3)
])
theorem kid22_part1448_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid22_part1448) = true := by rfl

def kid22_part1449 : Audit := .split 11 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 1 15 true (1),
.last 19 (4,true),
.last 23 (4,true),
.last 19 (4,true),
.last 27 (4,true),
.cycle 6 6 true (2),
.last 13 (4,true),
.last 25 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 5 8 true (1),
.last 17 (4,true),
.last 18 (4,true),
.last 19 (4,true),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (3)
])
theorem kid22_part1449_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid22_part1449) = true := by rfl

def kid22_part1450 : Audit := .cycle 5 6 true (1)
theorem kid22_part1450_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid22_part1450) = true := by rfl

def kid22_part1451 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 1 15 true (1),
.last 20 (2,true),
.cycle 0 25 true (0),
.cycle 18 6 false (0),
.cycle 18 1 false (-2),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 8 true (3),
.cycle 10 4 true (3),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 35 1 false (7),
.cycle 18 3 false (0),
.cycle 18 1 false (-2),
.cycle 6 6 true (2),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 8 6 true (3),
.cycle 10 2 true (3)
])
theorem kid22_part1451_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid22_part1451) = true := by rfl

def kid22_part1452 : Audit := .cycle 15 1 false (-1)
theorem kid22_part1452_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid22_part1452) = true := by rfl

def kid22_part1453 : Audit := .cycle 1 11 true (1)
theorem kid22_part1453_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid22_part1453) = true := by rfl

def kid22_part1454 : Audit := .cycle 7 4 true (3)
theorem kid22_part1454_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid22_part1454) = true := by rfl

def kid22_part1455 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 2 15 true (1),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 5 10 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1455_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid22_part1455) = true := by rfl

def kid22_part1456 : Audit := .cycle 0 12 true (0)
theorem kid22_part1456_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid22_part1456) = true := by rfl

def kid22_part1457 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.cycle 8 5 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 8 true (4),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 8 9 true (4),
.cycle 6 6 true (2),
.cycle 11 2 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 22 5 false (2),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid22_part1457_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid22_part1457) = true := by rfl

def kid22_part1458 : Audit := .cycle 9 3 true (4)
theorem kid22_part1458_checked : zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid22_part1458) = true := by rfl

def kid22_part1434 : Audit := .split 10 (5,true) (byMove [(kid22_part1435),(kid22_part1436),(kid22_part1437),(kid22_part1438),(kid22_part1439),(kid22_part1440),(kid22_part1441),(kid22_part1442),(kid22_part1443),(kid22_part1444),(kid22_part1445),(kid22_part1446),(kid22_part1447),(kid22_part1448),(kid22_part1449),(kid22_part1450),(kid22_part1451),(kid22_part1452),(kid22_part1453),(kid22_part1454),(kid22_part1455),(kid22_part1456),(kid22_part1457),(kid22_part1458)])

theorem kid22_part1434_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid22_part1434) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid22_part1435),(kid22_part1436),(kid22_part1437),(kid22_part1438),(kid22_part1439),(kid22_part1440),(kid22_part1441),(kid22_part1442),(kid22_part1443),(kid22_part1444),(kid22_part1445),(kid22_part1446),(kid22_part1447),(kid22_part1448),(kid22_part1449),(kid22_part1450),(kid22_part1451),(kid22_part1452),(kid22_part1453),(kid22_part1454),(kid22_part1455),(kid22_part1456),(kid22_part1457),(kid22_part1458)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1435_checked

  · exact kid22_part1441_checked

  · exact kid22_part1447_checked

  · exact kid22_part1453_checked

  · exact kid22_part1436_checked

  · exact kid22_part1442_checked

  · exact kid22_part1448_checked

  · exact kid22_part1454_checked

  · exact kid22_part1437_checked

  · exact kid22_part1443_checked

  · exact kid22_part1449_checked

  · exact kid22_part1455_checked

  · exact kid22_part1438_checked

  · exact kid22_part1444_checked

  · exact kid22_part1450_checked

  · exact kid22_part1456_checked

  · exact kid22_part1439_checked

  · exact kid22_part1445_checked

  · exact kid22_part1451_checked

  · exact kid22_part1457_checked

  · exact kid22_part1440_checked

  · exact kid22_part1446_checked

  · exact kid22_part1452_checked

  · exact kid22_part1458_checked

def kid22_part1459 : Audit := .cycle 0 10 true (0)
theorem kid22_part1459_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid22_part1459) = true := by rfl

def kid22_part1460 : Audit := .cycle 1 9 true (1)
theorem kid22_part1460_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid22_part1460) = true := by rfl

def kid22_part1461 : Audit := .cycle 2 8 true (1)
theorem kid22_part1461_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid22_part1461) = true := by rfl

def kid22_part1462 : Audit := .cycle 1 12 true (1)
theorem kid22_part1462_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid22_part1462) = true := by rfl

def kid22_part1463 : Audit := .cycle 8 2 true (4)
theorem kid22_part1463_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid22_part1463) = true := by rfl

def kid22_part1464 : Audit := .cycle 9 1 true (5)
theorem kid22_part1464_checked : zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid22_part1464) = true := by rfl

def kid22_part1344 : Audit := .split 9 (5,false) (byMove [(kid22_part1345),(kid22_part1346),(kid22_part1347),(kid22_part1372),(kid22_part1373),(kid22_part1374),(kid22_part1375),(kid22_part1376),(kid22_part1377),(kid22_part1378),(kid22_part1379),(kid22_part1380),(kid22_part1381),(kid22_part1382),(kid22_part1383),(kid22_part1408),(kid22_part1409),(kid22_part1434),(kid22_part1459),(kid22_part1460),(kid22_part1461),(kid22_part1462),(kid22_part1463),(kid22_part1464)])

theorem kid22_part1344_checked : zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (kid22_part1344) = true := by

  change (zipQueryOK 1271 (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨true,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid22_part1345),(kid22_part1346),(kid22_part1347),(kid22_part1372),(kid22_part1373),(kid22_part1374),(kid22_part1375),(kid22_part1376),(kid22_part1377),(kid22_part1378),(kid22_part1379),(kid22_part1380),(kid22_part1381),(kid22_part1382),(kid22_part1383),(kid22_part1408),(kid22_part1409),(kid22_part1434),(kid22_part1459),(kid22_part1460),(kid22_part1461),(kid22_part1462),(kid22_part1463),(kid22_part1464)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1345_checked

  · exact kid22_part1375_checked

  · exact kid22_part1381_checked

  · exact kid22_part1459_checked

  · exact kid22_part1346_checked

  · exact kid22_part1376_checked

  · exact kid22_part1382_checked

  · exact kid22_part1460_checked

  · exact kid22_part1347_checked

  · exact kid22_part1377_checked

  · exact kid22_part1383_checked

  · exact kid22_part1461_checked

  · exact kid22_part1372_checked

  · exact kid22_part1378_checked

  · exact kid22_part1408_checked

  · exact kid22_part1462_checked

  · exact kid22_part1373_checked

  · exact kid22_part1379_checked

  · exact kid22_part1409_checked

  · exact kid22_part1463_checked

  · exact kid22_part1374_checked

  · exact kid22_part1380_checked

  · exact kid22_part1434_checked

  · exact kid22_part1464_checked

def kid22 : Audit := .split 8 (4,false) (byMove [(kid22_part1),(kid22_part2),(kid22_part3),(kid22_part124),(kid22_part125),(kid22_part222),(kid22_part463),(kid22_part464),(kid22_part465),(kid22_part538),(kid22_part539),(kid22_part540),(kid22_part637),(kid22_part638),(kid22_part711),(kid22_part832),(kid22_part833),(kid22_part954),(kid22_part1339),(kid22_part1340),(kid22_part1341),(kid22_part1342),(kid22_part1343),(kid22_part1344)])

theorem check22 : zipCheck 1271 (child ⟨true,true,4⟩) (kid22) = true := by

  change (zipQueryOK 1271 (child ⟨true,true,4⟩) 8 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (child ⟨true,true,4⟩) (4,false) (some mv)) (byMove [(kid22_part1),(kid22_part2),(kid22_part3),(kid22_part124),(kid22_part125),(kid22_part222),(kid22_part463),(kid22_part464),(kid22_part465),(kid22_part538),(kid22_part539),(kid22_part540),(kid22_part637),(kid22_part638),(kid22_part711),(kid22_part832),(kid22_part833),(kid22_part954),(kid22_part1339),(kid22_part1340),(kid22_part1341),(kid22_part1342),(kid22_part1343),(kid22_part1344)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid22_part1_checked

  · exact kid22_part463_checked

  · exact kid22_part637_checked

  · exact kid22_part1339_checked

  · exact kid22_part2_checked

  · exact kid22_part464_checked

  · exact kid22_part638_checked

  · exact kid22_part1340_checked

  · exact kid22_part3_checked

  · exact kid22_part465_checked

  · exact kid22_part711_checked

  · exact kid22_part1341_checked

  · exact kid22_part124_checked

  · exact kid22_part538_checked

  · exact kid22_part832_checked

  · exact kid22_part1342_checked

  · exact kid22_part125_checked

  · exact kid22_part539_checked

  · exact kid22_part833_checked

  · exact kid22_part1343_checked

  · exact kid22_part222_checked

  · exact kid22_part540_checked

  · exact kid22_part954_checked

  · exact kid22_part1344_checked

end BB6.Agent11Raw39B0RB
