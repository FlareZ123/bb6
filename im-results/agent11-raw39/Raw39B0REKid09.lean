import Raw39B0REBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid09_part1 : Audit := .cycle 0 18 true (0)
theorem kid09_part1_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,0⟩)) (kid09_part1) = true := by rfl

def kid09_part2 : Audit := .cycle 25 1 false (7)
theorem kid09_part2_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,1⟩)) (kid09_part2) = true := by rfl

def kid09_part3 : Audit := .cycle 19 1 false (5)
theorem kid09_part3_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,2⟩)) (kid09_part3) = true := by rfl

def kid09_part4 : Audit := .cycle 18 1 false (4)
theorem kid09_part4_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,3⟩)) (kid09_part4) = true := by rfl

def kid09_part5 : Audit := .cycle 17 1 false (5)
theorem kid09_part5_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,4⟩)) (kid09_part5) = true := by rfl

def kid09_part7 : Audit := .cycle 0 19 true (0)
theorem kid09_part7_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid09_part7) = true := by rfl

def kid09_part8 : Audit := .cycle 26 1 false (6)
theorem kid09_part8_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid09_part8) = true := by rfl

def kid09_part9 : Audit := .cycle 20 1 false (4)
theorem kid09_part9_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid09_part9) = true := by rfl

def kid09_part10 : Audit := .cycle 19 1 false (3)
theorem kid09_part10_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid09_part10) = true := by rfl

def kid09_part11 : Audit := .cycle 17 2 false (5)
theorem kid09_part11_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid09_part11) = true := by rfl

def kid09_part12 : Audit := .cycle 18 1 false (4)
theorem kid09_part12_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid09_part12) = true := by rfl

def kid09_part13 : Audit := .cycle 0 19 true (0)
theorem kid09_part13_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid09_part13) = true := by rfl

def kid09_part14 : Audit := .cycle 26 1 false (8)
theorem kid09_part14_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid09_part14) = true := by rfl

def kid09_part15 : Audit := .cycle 20 1 false (6)
theorem kid09_part15_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid09_part15) = true := by rfl

def kid09_part16 : Audit := .cycle 19 1 false (5)
theorem kid09_part16_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid09_part16) = true := by rfl

def kid09_part17 : Audit := .cycle 17 2 true (4)
theorem kid09_part17_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid09_part17) = true := by rfl

def kid09_part18 : Audit := .cycle 18 1 true (4)
theorem kid09_part18_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid09_part18) = true := by rfl

def kid09_part19 : Audit := .split 20 (1,true) (byMove [
.cycle 16 5 false (5),
.cycle 29 1 false (5),
.split 21 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.cycle 19 3 false (4),
.cycle 26 1 false (2),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 25 1 false (5)
]),
.cycle 0 22 true (0),
.cycle 22 1 false (4),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.cycle 19 3 false (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 21 2 true (3),
.cycle 25 1 false (5)
]),
.cycle 0 21 true (0),
.cycle 39 1 false (9),
.cycle 0 29 true (0),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 18 3 true (3),
.cycle 23 1 false (5),
.split 23 (2,true) (byMove [
.cycle 16 8 false (5),
.cycle 21 3 false (3),
.cycle 26 1 false (2),
.cycle 19 6 true (2),
.cycle 25 1 false (3),
.last 24 (5,true),
.cycle 6 27 true (0),
.cycle 12 43 true (0),
.cycle 8 18 true (0),
.cycle 0 25 true (0),
.cycle 0 32 true (0),
.last 24 (5,true),
.cycle 0 27 true (0),
.cycle 21 3 false (3),
.cycle 29 1 false (5),
.cycle 27 1 false (5),
.cycle 14 10 true (2),
.last 24 (5,true),
.cycle 0 36 true (0),
.cycle 20 5 false (4),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.cycle 3 22 true (0),
.last 24 (5,true)
]),
.split 21 (2,true) (byMove [
.cycle 30 1 false (4),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 16 6 true (3),
.cycle 0 25 true (0),
.cycle 24 1 false (6),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 19 3 false (4),
.cycle 29 1 false (5),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 27 1 false (5),
.cycle 20 2 true (3),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 22 (5,true)
]),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 16 6 true (3),
.cycle 18 5 false (4),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 18 5 true (3),
.cycle 19 3 false (4),
.last 23 (2,true),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 27 1 false (5),
.cycle 20 2 true (3),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.cycle 0 33 true (0)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.split 22 (5,true) (byMove [
.cycle 16 7 false (5),
.cycle 33 1 false (5),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 18 6 false (5),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.cycle 27 1 false (5),
.cycle 18 5 true (3),
.cycle 25 1 false (5),
.cycle 30 1 false (6),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 0 29 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 21 2 true (4),
.cycle 0 33 true (0)
]),
.cycle 0 31 true (0)
])
theorem kid09_part19_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid09_part19) = true := by rfl

def kid09_part21 : Audit := .cycle 16 5 false (5)
theorem kid09_part21_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid09_part21) = true := by rfl

def kid09_part22 : Audit := .split 21 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.cycle 26 1 false (4),
.cycle 19 3 false (4),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.last 23 (5,true),
.last 24 (5,true)
])
theorem kid09_part22_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid09_part22) = true := by rfl

def kid09_part23 : Audit := .cycle 23 1 false (3)
theorem kid09_part23_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid09_part23) = true := by rfl

def kid09_part24 : Audit := .cycle 0 22 true (0)
theorem kid09_part24_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid09_part24) = true := by rfl

def kid09_part25 : Audit := .cycle 22 1 false (4)
theorem kid09_part25_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid09_part25) = true := by rfl

def kid09_part26 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.last 23 (1,true),
.cycle 19 3 false (4),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 21 2 true (3),
.last 23 (1,true)
])
theorem kid09_part26_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid09_part26) = true := by rfl

def kid09_part27 : Audit := .cycle 0 21 true (0)
theorem kid09_part27_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid09_part27) = true := by rfl

def kid09_part28 : Audit := .cycle 39 1 false (9)
theorem kid09_part28_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid09_part28) = true := by rfl

def kid09_part29 : Audit := .cycle 0 29 true (0)
theorem kid09_part29_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid09_part29) = true := by rfl

def kid09_part30 : Audit := .cycle 26 1 false (6)
theorem kid09_part30_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid09_part30) = true := by rfl

def kid09_part31 : Audit := .split 23 (1,true) (byMove [
.cycle 16 14 false (5),
.cycle 0 27 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 17 7 false (5),
.cycle 18 6 false (5),
.cycle 16 8 true (3),
.cycle 32 1 false (8),
.cycle 17 8 true (3),
.cycle 0 25 true (0),
.cycle 25 1 false (5),
.last 24 (5,true),
.cycle 0 29 true (0),
.cycle 0 34 true (0),
.cycle 15 10 true (2),
.cycle 24 1 false (2),
.cycle 17 7 false (5),
.cycle 0 29 true (0),
.cycle 21 4 true (3),
.cycle 1 24 true (0),
.cycle 20 4 true (3),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.last 24 (5,true)
])
theorem kid09_part31_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid09_part31) = true := by rfl

def kid09_part32 : Audit := .cycle 18 3 true (3)
theorem kid09_part32_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid09_part32) = true := by rfl

def kid09_part33 : Audit := .cycle 23 1 false (5)
theorem kid09_part33_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid09_part33) = true := by rfl

def kid09_part34 : Audit := .split 21 (1,true) (byMove [
.cycle 16 10 false (5),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 16 6 true (3),
.cycle 30 1 false (8),
.cycle 19 4 true (3),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 27 true (0),
.cycle 19 3 false (4),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 21 4 true (3),
.cycle 1 22 true (0),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 22 (5,true)
])
theorem kid09_part34_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid09_part34) = true := by rfl

def kid09_part35 : Audit := .cycle 15 8 true (2)
theorem kid09_part35_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid09_part35) = true := by rfl

def kid09_part36 : Audit := .cycle 15 6 true (3)
theorem kid09_part36_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid09_part36) = true := by rfl

def kid09_part37 : Audit := .cycle 0 23 true (0)
theorem kid09_part37_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid09_part37) = true := by rfl

def kid09_part38 : Audit := .split 21 (5,true) (byMove [
.cycle 16 10 false (5),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 16 6 true (3),
.last 22 (1,true),
.cycle 18 5 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 18 5 true (3),
.last 23 (1,true),
.cycle 19 3 false (4),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.last 25 (1,true),
.last 22 (1,true),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 24 (1,true)
])
theorem kid09_part38_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid09_part38) = true := by rfl

def kid09_part39 : Audit := .cycle 0 21 true (0)
theorem kid09_part39_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid09_part39) = true := by rfl

def kid09_part40 : Audit := .cycle 1 20 true (0)
theorem kid09_part40_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid09_part40) = true := by rfl

def kid09_part41 : Audit := .cycle 2 19 true (0)
theorem kid09_part41_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid09_part41) = true := by rfl

def kid09_part42 : Audit := .cycle 15 7 true (3)
theorem kid09_part42_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid09_part42) = true := by rfl

def kid09_part43 : Audit := .split 22 (5,true) (byMove [
.cycle 16 7 false (5),
.last 23 (1,true),
.cycle 27 1 false (3),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 18 6 false (5),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.last 25 (1,true),
.cycle 18 5 true (3),
.cycle 25 1 false (5),
.last 23 (1,true),
.cycle 30 1 false (6),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 0 29 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 21 2 true (4),
.last 24 (1,true)
])
theorem kid09_part43_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid09_part43) = true := by rfl

def kid09_part44 : Audit := .split 22 (1,true) (byMove [
.cycle 16 7 false (5),
.cycle 0 32 true (0),
.cycle 27 1 false (3),
.cycle 0 27 true (0),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 16 7 true (3),
.cycle 0 44 true (0),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 0 26 true (0),
.last 26 (5,true),
.last 24 (5,true),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.last 23 (5,true),
.cycle 21 4 true (4),
.cycle 1 23 true (0),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.last 23 (5,true)
])
theorem kid09_part44_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid09_part44) = true := by rfl

def kid09_part20 : Audit := .split 20 (2,true) (byMove [(kid09_part21),(kid09_part22),(kid09_part23),(kid09_part24),(kid09_part25),(kid09_part26),(kid09_part27),(kid09_part28),(kid09_part29),(kid09_part30),(kid09_part31),(kid09_part32),(kid09_part33),(kid09_part34),(kid09_part35),(kid09_part36),(kid09_part37),(kid09_part38),(kid09_part39),(kid09_part40),(kid09_part41),(kid09_part42),(kid09_part43),(kid09_part44)])

theorem kid09_part20_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid09_part20) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 20 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid09_part21),(kid09_part22),(kid09_part23),(kid09_part24),(kid09_part25),(kid09_part26),(kid09_part27),(kid09_part28),(kid09_part29),(kid09_part30),(kid09_part31),(kid09_part32),(kid09_part33),(kid09_part34),(kid09_part35),(kid09_part36),(kid09_part37),(kid09_part38),(kid09_part39),(kid09_part40),(kid09_part41),(kid09_part42),(kid09_part43),(kid09_part44)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part21_checked

  · exact kid09_part27_checked

  · exact kid09_part33_checked

  · exact kid09_part39_checked

  · exact kid09_part22_checked

  · exact kid09_part28_checked

  · exact kid09_part34_checked

  · exact kid09_part40_checked

  · exact kid09_part23_checked

  · exact kid09_part29_checked

  · exact kid09_part35_checked

  · exact kid09_part41_checked

  · exact kid09_part24_checked

  · exact kid09_part30_checked

  · exact kid09_part36_checked

  · exact kid09_part42_checked

  · exact kid09_part25_checked

  · exact kid09_part31_checked

  · exact kid09_part37_checked

  · exact kid09_part43_checked

  · exact kid09_part26_checked

  · exact kid09_part32_checked

  · exact kid09_part38_checked

  · exact kid09_part44_checked

def kid09_part45 : Audit := .cycle 0 21 true (0)
theorem kid09_part45_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid09_part45) = true := by rfl

def kid09_part46 : Audit := .cycle 19 1 false (3)
theorem kid09_part46_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid09_part46) = true := by rfl

def kid09_part47 : Audit := .cycle 17 2 false (5)
theorem kid09_part47_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid09_part47) = true := by rfl

def kid09_part48 : Audit := .cycle 18 1 false (4)
theorem kid09_part48_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid09_part48) = true := by rfl

def kid09_part49 : Audit := .cycle 0 19 true (0)
theorem kid09_part49_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid09_part49) = true := by rfl

def kid09_part50 : Audit := .cycle 1 18 true (0)
theorem kid09_part50_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid09_part50) = true := by rfl

def kid09_part51 : Audit := .cycle 25 1 false (7)
theorem kid09_part51_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid09_part51) = true := by rfl

def kid09_part52 : Audit := .cycle 15 5 true (3)
theorem kid09_part52_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid09_part52) = true := by rfl

def kid09_part53 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 18 3 true (4),
.split 22 (1,true) (byMove [
.cycle 16 7 false (5),
.cycle 31 1 false (5),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.cycle 29 1 false (5),
.cycle 18 5 true (3),
.cycle 25 1 false (5),
.last 25 (2,true),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 27 1 false (5),
.cycle 0 35 true (0)
]),
.split 22 (2,true) (byMove [
.cycle 16 7 false (5),
.last 23 (1,true),
.cycle 25 1 false (3),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.last 27 (1,true),
.cycle 18 5 true (3),
.cycle 25 1 false (5),
.last 23 (1,true),
.cycle 15 10 true (2),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.last 25 (1,true),
.last 26 (1,true)
]),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 28 1 false (6),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 19 2 true (4),
.cycle 18 3 true (4)
])
theorem kid09_part53_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid09_part53) = true := by rfl

def kid09_part54 : Audit := .cycle 18 1 true (4)
theorem kid09_part54_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid09_part54) = true := by rfl

def kid09_part6 : Audit := .split 18 (5,false) (byMove [(kid09_part7),(kid09_part8),(kid09_part9),(kid09_part10),(kid09_part11),(kid09_part12),(kid09_part13),(kid09_part14),(kid09_part15),(kid09_part16),(kid09_part17),(kid09_part18),(kid09_part19),(kid09_part20),(kid09_part45),(kid09_part46),(kid09_part47),(kid09_part48),(kid09_part49),(kid09_part50),(kid09_part51),(kid09_part52),(kid09_part53),(kid09_part54)])

theorem kid09_part6_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (kid09_part6) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid09_part7),(kid09_part8),(kid09_part9),(kid09_part10),(kid09_part11),(kid09_part12),(kid09_part13),(kid09_part14),(kid09_part15),(kid09_part16),(kid09_part17),(kid09_part18),(kid09_part19),(kid09_part20),(kid09_part45),(kid09_part46),(kid09_part47),(kid09_part48),(kid09_part49),(kid09_part50),(kid09_part51),(kid09_part52),(kid09_part53),(kid09_part54)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part7_checked

  · exact kid09_part13_checked

  · exact kid09_part19_checked

  · exact kid09_part49_checked

  · exact kid09_part8_checked

  · exact kid09_part14_checked

  · exact kid09_part20_checked

  · exact kid09_part50_checked

  · exact kid09_part9_checked

  · exact kid09_part15_checked

  · exact kid09_part45_checked

  · exact kid09_part51_checked

  · exact kid09_part10_checked

  · exact kid09_part16_checked

  · exact kid09_part46_checked

  · exact kid09_part52_checked

  · exact kid09_part11_checked

  · exact kid09_part17_checked

  · exact kid09_part47_checked

  · exact kid09_part53_checked

  · exact kid09_part12_checked

  · exact kid09_part18_checked

  · exact kid09_part48_checked

  · exact kid09_part54_checked

def kid09_part55 : Audit := .cycle 0 18 true (0)
theorem kid09_part55_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,0⟩)) (kid09_part55) = true := by rfl

def kid09_part56 : Audit := .cycle 25 1 false (9)
theorem kid09_part56_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,1⟩)) (kid09_part56) = true := by rfl

def kid09_part57 : Audit := .cycle 19 1 false (7)
theorem kid09_part57_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,2⟩)) (kid09_part57) = true := by rfl

def kid09_part58 : Audit := .cycle 18 1 false (6)
theorem kid09_part58_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,3⟩)) (kid09_part58) = true := by rfl

def kid09_part59 : Audit := .cycle 17 1 true (5)
theorem kid09_part59_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,4⟩)) (kid09_part59) = true := by rfl

def kid09_part61 : Audit := .cycle 0 19 true (0)
theorem kid09_part61_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid09_part61) = true := by rfl

def kid09_part62 : Audit := .cycle 26 1 false (8)
theorem kid09_part62_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid09_part62) = true := by rfl

def kid09_part63 : Audit := .cycle 20 1 false (6)
theorem kid09_part63_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid09_part63) = true := by rfl

def kid09_part64 : Audit := .cycle 19 1 false (5)
theorem kid09_part64_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid09_part64) = true := by rfl

def kid09_part65 : Audit := .cycle 17 2 true (5)
theorem kid09_part65_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid09_part65) = true := by rfl

def kid09_part66 : Audit := .cycle 18 1 false (6)
theorem kid09_part66_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid09_part66) = true := by rfl

def kid09_part67 : Audit := .cycle 0 19 true (0)
theorem kid09_part67_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid09_part67) = true := by rfl

def kid09_part68 : Audit := .cycle 26 1 false (10)
theorem kid09_part68_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid09_part68) = true := by rfl

def kid09_part69 : Audit := .cycle 20 1 false (8)
theorem kid09_part69_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid09_part69) = true := by rfl

def kid09_part70 : Audit := .cycle 19 1 false (7)
theorem kid09_part70_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid09_part70) = true := by rfl

def kid09_part71 : Audit := .cycle 17 2 true (5)
theorem kid09_part71_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid09_part71) = true := by rfl

def kid09_part72 : Audit := .cycle 18 1 true (6)
theorem kid09_part72_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid09_part72) = true := by rfl

def kid09_part73 : Audit := .split 20 (1,true) (byMove [
.cycle 16 5 true (4),
.cycle 29 1 false (7),
.split 21 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (5),
.cycle 18 4 true (5),
.cycle 19 3 false (6),
.cycle 26 1 false (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (5,true),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 17 5 true (5),
.cycle 25 1 false (7)
]),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (5),
.cycle 18 4 true (5),
.cycle 19 3 false (6),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 2 true (4),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 17 5 true (5),
.cycle 25 1 false (7)
]),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 18 3 true (5),
.cycle 23 1 false (7),
.split 23 (2,true) (byMove [
.last 26 (5,true),
.cycle 21 3 false (5),
.cycle 26 1 false (4),
.cycle 19 6 true (4),
.cycle 25 1 false (5),
.last 24 (5,true),
.cycle 16 8 true (4),
.cycle 12 43 true (0),
.cycle 8 18 true (0),
.cycle 0 25 true (0),
.cycle 0 32 true (0),
.last 24 (5,true),
.cycle 0 27 true (0),
.cycle 21 3 false (5),
.cycle 29 1 false (7),
.cycle 27 1 false (7),
.cycle 14 10 true (2),
.last 24 (5,true),
.cycle 16 8 true (4),
.cycle 20 5 false (6),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.cycle 3 22 true (0),
.last 24 (5,true)
]),
.split 21 (2,true) (byMove [
.cycle 16 9 true (4),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.cycle 0 25 true (0),
.cycle 24 1 false (8),
.cycle 0 23 true (0),
.cycle 23 1 false (7),
.last 22 (5,true),
.cycle 19 3 false (6),
.cycle 29 1 false (7),
.cycle 15 8 true (3),
.cycle 22 1 false (4),
.last 23 (5,true),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.cycle 20 2 true (5),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 28 1 false (8),
.last 22 (5,true)
]),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.cycle 18 5 false (6),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (7),
.cycle 18 5 true (5),
.cycle 19 3 false (6),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 22 1 false (4),
.cycle 21 2 true (4),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.cycle 20 2 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 28 1 false (8),
.cycle 0 33 true (0)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 0 31 true (0)
])
theorem kid09_part73_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid09_part73) = true := by rfl

def kid09_part74 : Audit := .split 20 (2,true) (byMove [
.cycle 16 5 true (4),
.split 21 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (5),
.cycle 18 4 true (5),
.cycle 26 1 false (6),
.cycle 19 3 false (6),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.last 23 (5,true),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 17 5 true (5),
.last 24 (5,true)
]),
.cycle 23 1 false (5),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (5),
.cycle 18 4 true (5),
.last 23 (1,true),
.cycle 19 3 false (6),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 2 true (4),
.cycle 18 4 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 17 5 true (5),
.last 23 (1,true)
]),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 18 3 true (5),
.cycle 23 1 false (7),
.split 21 (1,true) (byMove [
.last 28 (5,true),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.cycle 30 1 false (10),
.cycle 19 4 true (5),
.cycle 0 23 true (0),
.cycle 23 1 false (7),
.last 22 (5,true),
.cycle 0 27 true (0),
.cycle 19 3 false (6),
.cycle 15 8 true (3),
.cycle 22 1 false (4),
.last 23 (5,true),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.cycle 1 22 true (0),
.cycle 20 2 true (5),
.cycle 0 23 true (0),
.cycle 28 1 false (8),
.last 22 (5,true)
]),
.cycle 15 8 true (3),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.split 21 (5,true) (byMove [
.cycle 0 29 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 18 5 false (6),
.cycle 0 23 true (0),
.cycle 23 1 false (7),
.cycle 18 5 true (5),
.last 23 (1,true),
.cycle 19 3 false (6),
.cycle 15 8 true (3),
.cycle 22 1 false (4),
.cycle 21 2 true (4),
.cycle 18 4 false (6),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 20 2 true (5),
.cycle 0 23 true (0),
.cycle 28 1 false (8),
.last 24 (1,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.split 22 (1,true) (byMove [
.last 25 (5,true),
.cycle 0 32 true (0),
.cycle 27 1 false (5),
.cycle 0 27 true (0),
.cycle 24 1 false (6),
.last 23 (5,true),
.cycle 16 7 true (4),
.cycle 0 44 true (0),
.cycle 20 3 true (6),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 0 26 true (0),
.last 26 (5,true),
.last 24 (5,true),
.cycle 26 1 false (8),
.cycle 14 9 true (2),
.last 23 (5,true),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 20 3 true (6),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.last 23 (5,true)
])
])
theorem kid09_part74_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid09_part74) = true := by rfl

def kid09_part75 : Audit := .cycle 0 21 true (0)
theorem kid09_part75_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid09_part75) = true := by rfl

def kid09_part76 : Audit := .cycle 19 1 false (5)
theorem kid09_part76_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid09_part76) = true := by rfl

def kid09_part77 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.cycle 18 3 false (6),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.cycle 18 3 true (5),
.split 22 (1,true) (byMove [
.cycle 16 7 true (4),
.cycle 31 1 false (7),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.cycle 20 3 false (6),
.cycle 0 23 true (0),
.cycle 41 1 false (11),
.cycle 0 31 true (0),
.cycle 28 1 false (8),
.cycle 17 6 true (5),
.cycle 18 5 true (5),
.cycle 25 1 false (7),
.last 25 (2,true),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 17 6 true (5),
.cycle 0 26 true (0)
]),
.split 22 (2,true) (byMove [
.cycle 16 7 true (4),
.last 23 (1,true),
.cycle 25 1 false (5),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.cycle 20 3 false (6),
.cycle 0 23 true (0),
.cycle 41 1 false (11),
.cycle 0 31 true (0),
.cycle 28 1 false (8),
.cycle 17 6 true (5),
.cycle 18 5 true (5),
.cycle 25 1 false (7),
.last 23 (1,true),
.cycle 15 10 true (3),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 17 6 true (5),
.cycle 0 26 true (0)
]),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 19 2 true (5),
.cycle 18 3 false (6),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 0 24 true (0)
])
theorem kid09_part77_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid09_part77) = true := by rfl

def kid09_part78 : Audit := .cycle 18 1 false (6)
theorem kid09_part78_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid09_part78) = true := by rfl

def kid09_part79 : Audit := .cycle 0 19 true (0)
theorem kid09_part79_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid09_part79) = true := by rfl

def kid09_part80 : Audit := .cycle 1 18 true (0)
theorem kid09_part80_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid09_part80) = true := by rfl

def kid09_part81 : Audit := .cycle 25 1 false (9)
theorem kid09_part81_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid09_part81) = true := by rfl

def kid09_part82 : Audit := .cycle 15 5 true (3)
theorem kid09_part82_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid09_part82) = true := by rfl

def kid09_part83 : Audit := .cycle 17 2 true (5)
theorem kid09_part83_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid09_part83) = true := by rfl

def kid09_part84 : Audit := .cycle 18 1 true (6)
theorem kid09_part84_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid09_part84) = true := by rfl

def kid09_part60 : Audit := .split 18 (5,false) (byMove [(kid09_part61),(kid09_part62),(kid09_part63),(kid09_part64),(kid09_part65),(kid09_part66),(kid09_part67),(kid09_part68),(kid09_part69),(kid09_part70),(kid09_part71),(kid09_part72),(kid09_part73),(kid09_part74),(kid09_part75),(kid09_part76),(kid09_part77),(kid09_part78),(kid09_part79),(kid09_part80),(kid09_part81),(kid09_part82),(kid09_part83),(kid09_part84)])

theorem kid09_part60_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (kid09_part60) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid09_part61),(kid09_part62),(kid09_part63),(kid09_part64),(kid09_part65),(kid09_part66),(kid09_part67),(kid09_part68),(kid09_part69),(kid09_part70),(kid09_part71),(kid09_part72),(kid09_part73),(kid09_part74),(kid09_part75),(kid09_part76),(kid09_part77),(kid09_part78),(kid09_part79),(kid09_part80),(kid09_part81),(kid09_part82),(kid09_part83),(kid09_part84)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part61_checked

  · exact kid09_part67_checked

  · exact kid09_part73_checked

  · exact kid09_part79_checked

  · exact kid09_part62_checked

  · exact kid09_part68_checked

  · exact kid09_part74_checked

  · exact kid09_part80_checked

  · exact kid09_part63_checked

  · exact kid09_part69_checked

  · exact kid09_part75_checked

  · exact kid09_part81_checked

  · exact kid09_part64_checked

  · exact kid09_part70_checked

  · exact kid09_part76_checked

  · exact kid09_part82_checked

  · exact kid09_part65_checked

  · exact kid09_part71_checked

  · exact kid09_part77_checked

  · exact kid09_part83_checked

  · exact kid09_part66_checked

  · exact kid09_part72_checked

  · exact kid09_part78_checked

  · exact kid09_part84_checked

def kid09_part86 : Audit := .cycle 16 4 true (4)
theorem kid09_part86_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid09_part86) = true := by rfl

def kid09_part87 : Audit := .cycle 28 1 false (6)
theorem kid09_part87_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid09_part87) = true := by rfl

def kid09_part88 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 true (3),
.cycle 18 4 false (5),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 25 1 false (5),
.cycle 21 1 true (3)
]),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 18 4 true (4),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 25 1 false (7),
.cycle 21 1 true (5)
]),
.cycle 18 3 false (5),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 16 6 true (3),
.cycle 24 1 false (4),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 18 4 false (5),
.last 24 (5,true),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 27 (5,true),
.cycle 19 3 false (5),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 24 1 false (6),
.split 21 (5,false) (byMove [
.cycle 16 6 true (4),
.cycle 24 1 false (4),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 24 1 false (6),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 32 true (0),
.cycle 21 1 true (5)
])
])
theorem kid09_part88_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid09_part88) = true := by rfl

def kid09_part89 : Audit := .cycle 0 21 true (0)
theorem kid09_part89_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid09_part89) = true := by rfl

def kid09_part90 : Audit := .cycle 21 1 false (5)
theorem kid09_part90_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid09_part90) = true := by rfl

def kid09_part91 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 true (3),
.cycle 18 4 false (5),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 25 1 false (5),
.cycle 21 1 true (3)
]),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 18 4 true (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 25 1 false (7),
.cycle 21 1 true (5)
]),
.cycle 18 3 false (5),
.split 22 (2,true) (byMove [
.cycle 16 7 false (5),
.last 24 (5,false),
.cycle 25 1 false (3),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.last 28 (5,false),
.last 23 (5,false),
.cycle 25 1 false (5),
.last 24 (5,false),
.cycle 15 10 true (2),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 0 33 true (0),
.last 23 (5,false)
]),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 16 6 true (3),
.cycle 31 1 false (7),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 20 2 true (3),
.cycle 18 4 false (5),
.last 23 (2,true),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 38 true (0),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.cycle 20 3 false (4)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 24 1 false (6),
.split 21 (5,false) (byMove [
.cycle 16 6 true (4),
.cycle 31 1 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 24 1 false (6),
.last 25 (2,true),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 3 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 32 true (0),
.cycle 21 1 true (5)
])
])
theorem kid09_part91_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid09_part91) = true := by rfl

def kid09_part92 : Audit := .cycle 0 20 true (0)
theorem kid09_part92_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid09_part92) = true := by rfl

def kid09_part93 : Audit := .cycle 38 1 false (10)
theorem kid09_part93_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid09_part93) = true := by rfl

def kid09_part94 : Audit := .cycle 0 28 true (0)
theorem kid09_part94_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid09_part94) = true := by rfl

def kid09_part95 : Audit := .cycle 25 1 false (7)
theorem kid09_part95_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid09_part95) = true := by rfl

def kid09_part96 : Audit := .cycle 17 3 true (4)
theorem kid09_part96_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid09_part96) = true := by rfl

def kid09_part97 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 24 1 false (6),
.split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 30 1 false (6),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.cycle 23 1 false (3),
.cycle 0 23 true (0),
.cycle 30 1 false (8),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 17 6 true (4),
.cycle 23 1 false (5),
.cycle 18 5 false (6),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 0 31 true (0),
.cycle 23 1 false (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 29 1 false (7),
.cycle 15 9 true (3),
.cycle 26 1 false (6),
.cycle 21 2 true (4)
]),
.cycle 0 21 true (0),
.cycle 0 41 true (0),
.cycle 8 14 true (0),
.cycle 0 28 true (0),
.cycle 17 4 true (4),
.cycle 20 1 true (6),
.cycle 18 3 true (4),
.split 22 (2,true) (byMove [
.cycle 16 7 true (4),
.cycle 19 4 true (5),
.cycle 26 1 false (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 20 3 true (5),
.cycle 0 32 true (0),
.last 24 (5,true),
.cycle 29 1 false (7),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 0 33 true (0),
.last 25 (5,true)
]),
.cycle 0 23 true (0),
.cycle 25 1 false (7),
.cycle 0 25 true (0),
.split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 15 10 true (3),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.cycle 23 1 false (3),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 25 1 false (7),
.cycle 13 21 true (1),
.last 24 (2,true),
.cycle 27 1 false (7),
.cycle 23 1 false (3),
.cycle 33 1 false (7),
.cycle 23 1 false (3),
.cycle 0 32 true (0),
.cycle 1 24 true (0),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 23 3 true (5)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 38 1 false (10),
.cycle 15 7 true (3),
.cycle 6 16 true (0),
.cycle 20 1 true (6)
])
theorem kid09_part97_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid09_part97) = true := by rfl

def kid09_part98 : Audit := .cycle 22 1 false (6)
theorem kid09_part98_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid09_part98) = true := by rfl

def kid09_part99 : Audit := .split 22 (2,true) (byMove [
.cycle 16 7 false (5),
.cycle 20 3 false (4),
.cycle 25 1 false (3),
.cycle 18 6 true (3),
.cycle 24 1 false (4),
.split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 17 7 false (5),
.last 24 (5,false),
.cycle 18 6 true (3),
.cycle 34 1 false (8),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 17 7 false (5),
.last 24 (5,false),
.cycle 18 6 false (5),
.cycle 21 3 false (4),
.cycle 18 8 true (2),
.cycle 24 1 false (2),
.cycle 17 7 false (5),
.last 24 (5,false),
.cycle 19 7 false (5),
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 28 1 false (6),
.cycle 0 28 true (0),
.last 24 (5,false)
]),
.cycle 16 7 true (3),
.cycle 12 42 true (0),
.cycle 8 17 true (0),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.split 23 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 30 1 false (6),
.cycle 15 10 true (3),
.cycle 27 1 false (5),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 0 44 true (0),
.cycle 8 17 true (0),
.cycle 0 31 true (0),
.cycle 17 7 true (3),
.last 24 (5,false),
.cycle 19 7 false (5),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 28 1 false (6),
.cycle 0 28 true (0),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 41 1 false (9),
.cycle 15 10 true (3),
.cycle 6 19 true (0),
.last 24 (5,false)
]),
.cycle 0 26 true (0),
.cycle 20 3 false (4),
.cycle 28 1 false (6),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.split 23 (5,true) (byMove [
.cycle 16 12 false (5),
.cycle 15 11 true (2),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 17 7 false (5),
.last 24 (5,false),
.cycle 26 1 false (6),
.cycle 20 4 true (3),
.last 25 (5,false),
.cycle 15 9 true (3),
.cycle 0 26 true (0),
.last 26 (5,false),
.cycle 18 6 false (5),
.cycle 21 3 false (4),
.cycle 28 1 false (6),
.cycle 24 1 false (2),
.cycle 17 7 false (5),
.last 24 (5,false),
.cycle 0 33 true (0),
.cycle 19 5 false (5),
.cycle 22 2 true (3),
.cycle 15 9 true (3),
.cycle 0 26 true (0),
.last 26 (5,false)
]),
.cycle 0 35 true (0),
.cycle 19 5 false (5),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.split 23 (5,true) (byMove [
.cycle 19 9 false (5),
.cycle 19 5 false (5),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.last 26 (5,false),
.cycle 0 24 true (0),
.cycle 12 40 true (0),
.cycle 0 32 true (0),
.cycle 3 21 true (0),
.cycle 0 35 true (0),
.last 24 (5,false),
.cycle 0 33 true (0),
.cycle 19 5 false (5),
.cycle 22 2 true (4),
.cycle 15 9 true (3),
.cycle 0 26 true (0),
.last 26 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 15 10 true (3),
.cycle 0 34 true (0),
.last 24 (5,false)
])
])
theorem kid09_part99_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid09_part99) = true := by rfl

def kid09_part100 : Audit := .split 20 (2,true) (byMove [
.cycle 16 13 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 18 4 true (3),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 23 (5,true),
.cycle 18 4 false (5),
.last 24 (5,true),
.cycle 18 6 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 25 (5,true),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 0 26 true (0),
.last 23 (5,true)
]),
.cycle 16 5 true (4),
.cycle 0 24 true (0),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 18 4 true (4),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 25 1 false (7),
.last 22 (5,false)
]),
.cycle 18 3 false (5),
.cycle 28 1 false (6),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.last 25 (5,true),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 24 1 false (6),
.cycle 15 9 true (3),
.cycle 20 2 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 18 4 false (5),
.last 24 (5,true),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 31 true (0),
.cycle 19 3 false (5),
.last 23 (5,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true)
]),
.cycle 16 5 true (4),
.cycle 19 2 true (4),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.split 21 (5,true) (byMove [
.cycle 16 6 true (4),
.cycle 0 25 true (0),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 24 1 false (6),
.cycle 15 9 true (3),
.cycle 20 2 true (4),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 32 true (0),
.last 22 (5,false)
])
])
theorem kid09_part100_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid09_part100) = true := by rfl

def kid09_part101 : Audit := .cycle 15 5 true (3)
theorem kid09_part101_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid09_part101) = true := by rfl

def kid09_part102 : Audit := .cycle 0 22 true (0)
theorem kid09_part102_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid09_part102) = true := by rfl

def kid09_part104 : Audit := .split 23 (2,true) (byMove [
.cycle 16 13 false (5),
.cycle 19 5 false (5),
.cycle 27 1 false (3),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 12 40 true (0),
.cycle 0 32 true (0),
.cycle 3 21 true (0),
.cycle 0 43 true (0),
.last 24 (5,false),
.cycle 0 33 true (0),
.cycle 19 5 false (5),
.cycle 30 1 false (6),
.cycle 15 9 true (3),
.cycle 0 26 true (0),
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 15 10 true (3),
.cycle 0 34 true (0),
.last 24 (5,false)
])
theorem kid09_part104_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid09_part104) = true := by rfl

def kid09_part105 : Audit := .cycle 0 24 true (0)
theorem kid09_part105_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid09_part105) = true := by rfl

def kid09_part106 : Audit := .cycle 22 1 false (4)
theorem kid09_part106_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid09_part106) = true := by rfl

def kid09_part107 : Audit := .cycle 21 1 false (3)
theorem kid09_part107_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid09_part107) = true := by rfl

def kid09_part108 : Audit := .cycle 17 4 false (5)
theorem kid09_part108_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid09_part108) = true := by rfl

def kid09_part109 : Audit := .split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 18 4 true (3),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 24 1 true (4),
.cycle 18 4 false (5),
.last 23 (2,true),
.cycle 18 6 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 29 (2,true),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 0 26 true (0),
.cycle 26 1 true (2)
])
theorem kid09_part109_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid09_part109) = true := by rfl

def kid09_part110 : Audit := .cycle 16 5 true (4)
theorem kid09_part110_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid09_part110) = true := by rfl

def kid09_part111 : Audit := .split 22 (5,false) (byMove [
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.cycle 22 1 false (4),
.cycle 16 7 true (4),
.cycle 21 2 true (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.cycle 31 1 false (9),
.cycle 18 5 false (5),
.last 24 (2,true),
.cycle 15 9 true (3),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.cycle 22 1 false (4),
.cycle 16 7 true (4),
.cycle 19 4 true (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 42 1 false (10)
])
theorem kid09_part111_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid09_part111) = true := by rfl

def kid09_part112 : Audit := .split 21 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 18 4 true (4),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 25 1 false (7),
.last 22 (5,false)
])
theorem kid09_part112_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid09_part112) = true := by rfl

def kid09_part113 : Audit := .cycle 0 22 true (0)
theorem kid09_part113_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid09_part113) = true := by rfl

def kid09_part114 : Audit := .cycle 22 1 false (6)
theorem kid09_part114_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid09_part114) = true := by rfl

def kid09_part115 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 30 1 false (8),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 17 6 true (4),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 30 1 false (10),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 17 6 true (4),
.cycle 22 1 true (6),
.cycle 18 5 true (4),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 20 7 true (4),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 29 1 false (9),
.cycle 15 9 true (3),
.cycle 26 1 false (8),
.cycle 22 1 true (6)
])
theorem kid09_part115_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid09_part115) = true := by rfl

def kid09_part116 : Audit := .cycle 18 3 false (5)
theorem kid09_part116_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid09_part116) = true := by rfl

def kid09_part117 : Audit := .split 22 (2,true) (byMove [
.cycle 16 7 false (5),
.last 24 (5,false),
.cycle 25 1 false (3),
.cycle 18 6 true (3),
.cycle 24 1 false (4),
.cycle 20 3 false (4),
.cycle 16 7 true (3),
.last 24 (5,false),
.cycle 8 17 true (0),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 26 (5,false),
.cycle 0 26 true (0),
.last 24 (5,false),
.cycle 28 1 false (6),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.cycle 20 3 false (4),
.cycle 0 35 true (0),
.last 26 (5,false),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.cycle 19 5 false (5)
])
theorem kid09_part117_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid09_part117) = true := by rfl

def kid09_part118 : Audit := .cycle 15 7 true (3)
theorem kid09_part118_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid09_part118) = true := by rfl

def kid09_part119 : Audit := .cycle 21 1 false (3)
theorem kid09_part119_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid09_part119) = true := by rfl

def kid09_part120 : Audit := .cycle 17 4 false (5)
theorem kid09_part120_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid09_part120) = true := by rfl

def kid09_part121 : Audit := .split 21 (5,false) (byMove [
.last 24 (2,true),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 24 1 false (6),
.cycle 21 2 true (3),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.cycle 18 4 false (5),
.last 23 (2,true),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 31 true (0),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 3 false (4)
])
theorem kid09_part121_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid09_part121) = true := by rfl

def kid09_part122 : Audit := .cycle 16 5 true (4)
theorem kid09_part122_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid09_part122) = true := by rfl

def kid09_part123 : Audit := .cycle 19 2 true (4)
theorem kid09_part123_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid09_part123) = true := by rfl

def kid09_part124 : Audit := .split 21 (2,true) (byMove [
.cycle 16 6 true (4),
.last 23 (5,false),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 29 1 false (7),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 24 1 false (6),
.last 23 (5,false),
.cycle 15 9 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 32 true (0),
.last 22 (5,false)
])
theorem kid09_part124_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid09_part124) = true := by rfl

def kid09_part125 : Audit := .cycle 0 22 true (0)
theorem kid09_part125_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid09_part125) = true := by rfl

def kid09_part126 : Audit := .cycle 27 1 false (7)
theorem kid09_part126_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid09_part126) = true := by rfl

def kid09_part127 : Audit := .split 22 (5,false) (byMove [
.cycle 16 7 true (4),
.cycle 19 4 true (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 22 1 true (6),
.cycle 0 32 true (0),
.cycle 20 5 true (4),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 0 33 true (0),
.cycle 22 1 true (6)
])
theorem kid09_part127_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid09_part127) = true := by rfl

def kid09_part103 : Audit := .split 20 (5,true) (byMove [(kid09_part104),(kid09_part105),(kid09_part106),(kid09_part107),(kid09_part108),(kid09_part109),(kid09_part110),(kid09_part111),(kid09_part112),(kid09_part113),(kid09_part114),(kid09_part115),(kid09_part116),(kid09_part117),(kid09_part118),(kid09_part119),(kid09_part120),(kid09_part121),(kid09_part122),(kid09_part123),(kid09_part124),(kid09_part125),(kid09_part126),(kid09_part127)])

theorem kid09_part103_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid09_part103) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 20 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid09_part104),(kid09_part105),(kid09_part106),(kid09_part107),(kid09_part108),(kid09_part109),(kid09_part110),(kid09_part111),(kid09_part112),(kid09_part113),(kid09_part114),(kid09_part115),(kid09_part116),(kid09_part117),(kid09_part118),(kid09_part119),(kid09_part120),(kid09_part121),(kid09_part122),(kid09_part123),(kid09_part124),(kid09_part125),(kid09_part126),(kid09_part127)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part104_checked

  · exact kid09_part110_checked

  · exact kid09_part116_checked

  · exact kid09_part122_checked

  · exact kid09_part105_checked

  · exact kid09_part111_checked

  · exact kid09_part117_checked

  · exact kid09_part123_checked

  · exact kid09_part106_checked

  · exact kid09_part112_checked

  · exact kid09_part118_checked

  · exact kid09_part124_checked

  · exact kid09_part107_checked

  · exact kid09_part113_checked

  · exact kid09_part119_checked

  · exact kid09_part125_checked

  · exact kid09_part108_checked

  · exact kid09_part114_checked

  · exact kid09_part120_checked

  · exact kid09_part126_checked

  · exact kid09_part109_checked

  · exact kid09_part115_checked

  · exact kid09_part121_checked

  · exact kid09_part127_checked

def kid09_part128 : Audit := .cycle 0 20 true (0)
theorem kid09_part128_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid09_part128) = true := by rfl

def kid09_part129 : Audit := .cycle 1 19 true (0)
theorem kid09_part129_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid09_part129) = true := by rfl

def kid09_part130 : Audit := .cycle 2 18 true (0)
theorem kid09_part130_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid09_part130) = true := by rfl

def kid09_part131 : Audit := .cycle 15 6 true (3)
theorem kid09_part131_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid09_part131) = true := by rfl

def kid09_part132 : Audit := .cycle 0 30 true (0)
theorem kid09_part132_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid09_part132) = true := by rfl

def kid09_part133 : Audit := .split 20 (5,false) (byMove [
.cycle 16 5 true (4),
.cycle 19 2 true (5),
.split 21 (2,true) (byMove [
.cycle 16 6 true (4),
.cycle 32 1 false (6),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 29 1 false (7),
.cycle 24 1 false (6),
.last 23 (5,true),
.cycle 15 9 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 32 true (0),
.cycle 20 2 true (5)
]),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.split 21 (5,true) (byMove [
.cycle 16 6 true (4),
.cycle 32 1 false (6),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 21 2 true (4),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 32 true (0),
.cycle 20 2 true (5)
]),
.cycle 0 21 true (0),
.cycle 12 37 true (0),
.cycle 0 29 true (0),
.cycle 3 18 true (0),
.cycle 17 4 true (4),
.cycle 20 1 true (6),
.cycle 0 30 true (0),
.split 22 (5,true) (byMove [
.cycle 16 7 true (4),
.cycle 19 4 true (5),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 27 (2,true),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.last 25 (2,true),
.cycle 0 32 true (0),
.cycle 21 2 true (5),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 27 (2,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 0 33 true (0),
.cycle 20 3 true (5)
]),
.split 21 (2,true) (byMove [
.last 26 (5,true),
.cycle 15 12 true (3),
.cycle 24 1 false (4),
.cycle 18 5 true (4),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.cycle 8 16 true (0),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.last 22 (5,true),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 27 1 false (7),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.last 22 (5,true)
]),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.split 21 (5,true) (byMove [
.cycle 16 11 true (4),
.cycle 15 12 true (3),
.last 22 (2,true),
.cycle 18 5 true (4),
.cycle 23 1 false (5),
.cycle 23 1 false (3),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.cycle 30 1 false (8),
.cycle 0 25 true (0),
.cycle 21 2 true (4),
.last 22 (2,true),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 23 1 false (3),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 20 3 true (5)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 0 31 true (0),
.cycle 20 1 true (6)
])
theorem kid09_part133_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid09_part133) = true := by rfl

def kid09_part85 : Audit := .split 19 (1,true) (byMove [(kid09_part86),(kid09_part87),(kid09_part88),(kid09_part89),(kid09_part90),(kid09_part91),(kid09_part92),(kid09_part93),(kid09_part94),(kid09_part95),(kid09_part96),(kid09_part97),(kid09_part98),(kid09_part99),(kid09_part100),(kid09_part101),(kid09_part102),(kid09_part103),(kid09_part128),(kid09_part129),(kid09_part130),(kid09_part131),(kid09_part132),(kid09_part133)])

theorem kid09_part85_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (kid09_part85) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) 19 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid09_part86),(kid09_part87),(kid09_part88),(kid09_part89),(kid09_part90),(kid09_part91),(kid09_part92),(kid09_part93),(kid09_part94),(kid09_part95),(kid09_part96),(kid09_part97),(kid09_part98),(kid09_part99),(kid09_part100),(kid09_part101),(kid09_part102),(kid09_part103),(kid09_part128),(kid09_part129),(kid09_part130),(kid09_part131),(kid09_part132),(kid09_part133)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part86_checked

  · exact kid09_part92_checked

  · exact kid09_part98_checked

  · exact kid09_part128_checked

  · exact kid09_part87_checked

  · exact kid09_part93_checked

  · exact kid09_part99_checked

  · exact kid09_part129_checked

  · exact kid09_part88_checked

  · exact kid09_part94_checked

  · exact kid09_part100_checked

  · exact kid09_part130_checked

  · exact kid09_part89_checked

  · exact kid09_part95_checked

  · exact kid09_part101_checked

  · exact kid09_part131_checked

  · exact kid09_part90_checked

  · exact kid09_part96_checked

  · exact kid09_part102_checked

  · exact kid09_part132_checked

  · exact kid09_part91_checked

  · exact kid09_part97_checked

  · exact kid09_part103_checked

  · exact kid09_part133_checked

def kid09_part135 : Audit := .cycle 16 4 true (4)
theorem kid09_part135_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid09_part135) = true := by rfl

def kid09_part136 : Audit := .split 20 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 true (3),
.last 24 (5,true),
.cycle 18 4 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 20 3 false (4),
.cycle 21 1 true (3)
]),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 20 3 true (4),
.cycle 18 4 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.last 24 (5,true),
.cycle 21 1 true (5)
]),
.cycle 25 1 false (5),
.cycle 18 3 false (5),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.last 26 (5,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 16 6 true (3),
.cycle 20 2 true (3),
.cycle 30 1 false (6),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.last 24 (5,true),
.cycle 18 4 false (5),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 27 (5,true),
.last 23 (5,true),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 29 1 false (7),
.split 21 (5,false) (byMove [
.cycle 16 6 true (4),
.cycle 20 2 true (4),
.cycle 30 1 false (6),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 24 1 false (6),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 24 (5,true),
.cycle 21 1 true (5)
])
])
theorem kid09_part136_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid09_part136) = true := by rfl

def kid09_part137 : Audit := .cycle 22 1 false (4)
theorem kid09_part137_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid09_part137) = true := by rfl

def kid09_part138 : Audit := .cycle 0 21 true (0)
theorem kid09_part138_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid09_part138) = true := by rfl

def kid09_part139 : Audit := .cycle 21 1 false (5)
theorem kid09_part139_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid09_part139) = true := by rfl

def kid09_part140 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 true (3),
.last 23 (1,true),
.cycle 18 4 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.last 23 (1,true),
.cycle 21 1 true (3)
]),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.last 23 (1,true),
.cycle 18 4 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 21 1 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.last 23 (1,true),
.cycle 21 1 true (5)
]),
.split 22 (1,true) (byMove [
.cycle 16 7 false (5),
.cycle 31 1 false (5),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.cycle 29 1 false (5),
.last 23 (5,false),
.cycle 25 1 false (5),
.cycle 18 6 false (5),
.last 24 (5,false),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 false (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 3 23 true (0),
.last 23 (5,false)
]),
.cycle 18 3 false (5),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 20 6 false (4),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 16 6 true (3),
.last 22 (1,true),
.cycle 25 1 false (5),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 20 2 true (3),
.last 23 (1,true),
.cycle 18 4 false (5),
.cycle 15 8 true (2),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 38 true (0),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.cycle 20 3 false (4)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.split 22 (1,true) (byMove [
.cycle 16 13 false (5),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.last 23 (5,false),
.cycle 16 7 true (4),
.cycle 31 1 false (9),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.cycle 20 3 true (4),
.cycle 0 28 true (0),
.cycle 18 5 false (5),
.cycle 15 9 true (3),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.last 23 (5,false),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 20 3 true (4)
]),
.split 21 (5,false) (byMove [
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 21 1 true (5),
.cycle 24 1 false (6),
.last 22 (1,true),
.last 27 (1,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 3 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 23 (1,true),
.cycle 21 1 true (5)
])
])
theorem kid09_part140_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid09_part140) = true := by rfl

def kid09_part141 : Audit := .cycle 0 20 true (0)
theorem kid09_part141_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid09_part141) = true := by rfl

def kid09_part142 : Audit := .cycle 38 1 false (10)
theorem kid09_part142_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid09_part142) = true := by rfl

def kid09_part143 : Audit := .cycle 0 28 true (0)
theorem kid09_part143_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid09_part143) = true := by rfl

def kid09_part144 : Audit := .cycle 25 1 false (7)
theorem kid09_part144_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid09_part144) = true := by rfl

def kid09_part145 : Audit := .cycle 17 3 true (4)
theorem kid09_part145_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid09_part145) = true := by rfl

def kid09_part146 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.split 22 (1,true) (byMove [
.last 33 (5,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.cycle 17 7 false (6),
.cycle 16 7 true (4),
.cycle 31 1 false (9),
.cycle 17 8 true (4),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.last 23 (5,true),
.cycle 0 28 true (0),
.last 25 (5,true),
.cycle 15 9 true (3),
.cycle 23 1 false (3),
.last 26 (5,true),
.cycle 17 7 false (6),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 23 (5,true)
]),
.split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 30 1 false (6),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.cycle 23 1 false (3),
.cycle 0 23 true (0),
.cycle 30 1 false (8),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 17 6 true (4),
.cycle 23 1 false (5),
.last 24 (1,true),
.cycle 18 5 false (6),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.last 28 (1,true),
.cycle 23 1 false (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 29 1 false (7),
.cycle 15 9 true (3),
.last 24 (1,true),
.cycle 21 2 true (4)
]),
.cycle 0 21 true (0),
.cycle 0 41 true (0),
.cycle 8 14 true (0),
.cycle 0 28 true (0),
.cycle 17 4 true (4),
.cycle 20 1 true (6),
.split 22 (1,true) (byMove [
.cycle 16 7 true (4),
.cycle 32 1 false (6),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 20 3 true (5),
.cycle 0 32 true (0),
.last 27 (5,true),
.last 24 (5,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 3 23 true (0),
.cycle 0 33 true (0)
]),
.cycle 18 3 true (4),
.cycle 0 23 true (0),
.cycle 25 1 false (7),
.split 22 (1,true) (byMove [
.last 26 (5,true),
.cycle 15 10 true (3),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.last 27 (5,true),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.last 24 (5,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 13 12 true (1),
.last 25 (5,true),
.cycle 27 1 false (7),
.cycle 23 1 false (3),
.last 26 (5,true),
.last 27 (5,true),
.cycle 0 32 true (0),
.cycle 1 24 true (0),
.last 24 (5,true),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true)
]),
.split 22 (5,true) (byMove [
.cycle 0 27 true (0),
.cycle 15 10 true (3),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.cycle 23 1 false (3),
.cycle 25 1 false (7),
.last 23 (1,true),
.cycle 26 1 false (8),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 25 1 false (7),
.last 24 (1,true),
.last 34 (1,true),
.cycle 27 1 false (7),
.cycle 23 1 false (3),
.last 28 (1,true),
.cycle 23 1 false (3),
.cycle 0 32 true (0),
.last 23 (1,true),
.cycle 42 1 false (10),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 23 3 true (5)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 38 1 false (10),
.cycle 15 7 true (3),
.split 22 (1,true) (byMove [
.cycle 18 6 true (4),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.last 29 (5,true),
.cycle 0 36 true (0),
.last 26 (5,true),
.cycle 16 7 true (4),
.cycle 12 29 true (0),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 7 16 true (0),
.last 23 (5,true),
.cycle 0 28 true (0),
.last 25 (5,true),
.cycle 15 9 true (3),
.cycle 0 28 true (0),
.last 28 (5,true),
.cycle 0 26 true (0),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 40 1 false (10),
.last 23 (5,true)
]),
.cycle 20 1 true (6)
])
theorem kid09_part146_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid09_part146) = true := by rfl

def kid09_part147 : Audit := .cycle 22 1 false (6)
theorem kid09_part147_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid09_part147) = true := by rfl

def kid09_part148 : Audit := .split 20 (1,true) (byMove [
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 24 (5,true),
.cycle 18 4 true (3),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 23 (5,true),
.last 24 (5,true),
.cycle 18 4 false (5),
.last 26 (5,true),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 24 (5,true),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 20 3 false (4),
.last 23 (5,true)
]),
.cycle 16 5 true (4),
.cycle 29 1 false (9),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.last 22 (5,false),
.last 24 (5,false),
.cycle 18 4 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 20 3 true (4),
.last 22 (5,false)
]),
.cycle 0 26 true (0),
.cycle 18 3 false (5),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.split 21 (5,false) (byMove [
.last 26 (5,true),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 24 1 false (6),
.cycle 20 2 true (3),
.cycle 18 5 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.last 24 (5,true),
.cycle 18 4 false (5),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true)
]),
.cycle 16 5 true (4),
.cycle 1 21 true (0),
.cycle 19 2 true (4),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.split 21 (5,true) (byMove [
.cycle 16 6 true (4),
.last 23 (5,false),
.cycle 18 5 false (5),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 24 1 false (6),
.cycle 20 2 true (4),
.cycle 18 5 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 20 3 true (4),
.last 22 (5,false)
])
])
theorem kid09_part148_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid09_part148) = true := by rfl

def kid09_part149 : Audit := .cycle 15 7 true (3)
theorem kid09_part149_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid09_part149) = true := by rfl

def kid09_part150 : Audit := .cycle 15 5 true (3)
theorem kid09_part150_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid09_part150) = true := by rfl

def kid09_part151 : Audit := .cycle 0 22 true (0)
theorem kid09_part151_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid09_part151) = true := by rfl

def kid09_part153 : Audit := .cycle 16 9 false (5)
theorem kid09_part153_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid09_part153) = true := by rfl

def kid09_part154 : Audit := .cycle 0 24 true (0)
theorem kid09_part154_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid09_part154) = true := by rfl

def kid09_part155 : Audit := .cycle 22 1 false (4)
theorem kid09_part155_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid09_part155) = true := by rfl

def kid09_part156 : Audit := .cycle 21 1 false (3)
theorem kid09_part156_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid09_part156) = true := by rfl

def kid09_part157 : Audit := .cycle 17 4 false (5)
theorem kid09_part157_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid09_part157) = true := by rfl

def kid09_part158 : Audit := .split 21 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 23 (1,true),
.cycle 18 4 true (3),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 24 1 true (4),
.last 23 (1,true),
.cycle 18 4 false (5),
.last 25 (1,true),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.last 23 (1,true),
.cycle 0 30 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.last 23 (1,true),
.cycle 26 1 true (2)
])
theorem kid09_part158_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid09_part158) = true := by rfl

def kid09_part159 : Audit := .cycle 16 5 true (4)
theorem kid09_part159_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid09_part159) = true := by rfl

def kid09_part160 : Audit := .split 21 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 22 1 false (6),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 26 1 false (6),
.cycle 18 4 true (4),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (8),
.cycle 15 8 true (3),
.cycle 30 1 false (8),
.last 22 (5,false)
])
theorem kid09_part160_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid09_part160) = true := by rfl

def kid09_part161 : Audit := .split 22 (5,false) (byMove [
.cycle 16 13 false (5),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.cycle 22 1 false (4),
.cycle 16 7 true (4),
.last 23 (1,true),
.cycle 21 2 true (4),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.cycle 25 1 false (7),
.last 24 (1,true),
.cycle 18 5 false (5),
.cycle 15 9 true (3),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.cycle 22 1 false (4),
.cycle 16 7 true (4),
.last 23 (1,true),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 0 32 true (0)
])
theorem kid09_part161_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid09_part161) = true := by rfl

def kid09_part162 : Audit := .cycle 0 22 true (0)
theorem kid09_part162_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid09_part162) = true := by rfl

def kid09_part163 : Audit := .cycle 22 1 false (6)
theorem kid09_part163_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid09_part163) = true := by rfl

def kid09_part164 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 30 1 false (8),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 17 6 true (4),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 30 1 false (10),
.cycle 24 1 false (8),
.cycle 23 1 false (7),
.cycle 17 6 true (4),
.cycle 22 1 true (6),
.last 24 (1,true),
.cycle 18 5 true (4),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 20 7 true (4),
.cycle 22 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 29 1 false (9),
.cycle 15 9 true (3),
.last 24 (1,true),
.cycle 22 1 true (6)
])
theorem kid09_part164_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid09_part164) = true := by rfl

def kid09_part165 : Audit := .split 22 (1,true) (byMove [
.cycle 16 7 false (5),
.cycle 0 32 true (0),
.last 24 (5,false),
.cycle 0 27 true (0),
.cycle 24 1 false (4),
.cycle 20 3 false (4),
.cycle 16 7 true (3),
.cycle 0 44 true (0),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 18 6 false (5),
.last 24 (5,false),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.cycle 20 3 false (4),
.cycle 0 31 true (0),
.cycle 1 23 true (0),
.cycle 0 28 true (0),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.cycle 0 33 true (0)
])
theorem kid09_part165_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid09_part165) = true := by rfl

def kid09_part166 : Audit := .cycle 18 3 false (5)
theorem kid09_part166_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid09_part166) = true := by rfl

def kid09_part167 : Audit := .cycle 15 7 true (3)
theorem kid09_part167_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid09_part167) = true := by rfl

def kid09_part168 : Audit := .cycle 21 1 false (3)
theorem kid09_part168_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid09_part168) = true := by rfl

def kid09_part169 : Audit := .cycle 17 4 false (5)
theorem kid09_part169_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid09_part169) = true := by rfl

def kid09_part170 : Audit := .split 21 (5,false) (byMove [
.cycle 20 6 false (4),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 24 1 false (6),
.last 22 (1,true),
.cycle 21 2 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.last 23 (1,true),
.cycle 18 4 false (5),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 21 1 false (3),
.cycle 0 31 true (0),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 3 false (4)
])
theorem kid09_part170_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid09_part170) = true := by rfl

def kid09_part171 : Audit := .cycle 16 5 true (4)
theorem kid09_part171_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid09_part171) = true := by rfl

def kid09_part172 : Audit := .split 21 (1,true) (byMove [
.cycle 16 6 true (4),
.cycle 30 1 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 1 22 true (0),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.last 22 (5,false),
.cycle 24 1 false (6),
.cycle 18 5 false (5),
.last 23 (5,false),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 3 22 true (0),
.last 22 (5,false)
])
theorem kid09_part172_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid09_part172) = true := by rfl

def kid09_part173 : Audit := .cycle 19 2 true (4)
theorem kid09_part173_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid09_part173) = true := by rfl

def kid09_part174 : Audit := .cycle 0 22 true (0)
theorem kid09_part174_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid09_part174) = true := by rfl

def kid09_part175 : Audit := .cycle 27 1 false (7)
theorem kid09_part175_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid09_part175) = true := by rfl

def kid09_part176 : Audit := .split 22 (5,false) (byMove [
.cycle 16 7 true (4),
.last 23 (1,true),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 22 1 true (6),
.cycle 0 32 true (0),
.last 23 (1,true),
.cycle 20 5 true (4),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 20 3 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.last 24 (1,true),
.cycle 22 1 true (6)
])
theorem kid09_part176_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid09_part176) = true := by rfl

def kid09_part152 : Audit := .split 20 (5,true) (byMove [(kid09_part153),(kid09_part154),(kid09_part155),(kid09_part156),(kid09_part157),(kid09_part158),(kid09_part159),(kid09_part160),(kid09_part161),(kid09_part162),(kid09_part163),(kid09_part164),(kid09_part165),(kid09_part166),(kid09_part167),(kid09_part168),(kid09_part169),(kid09_part170),(kid09_part171),(kid09_part172),(kid09_part173),(kid09_part174),(kid09_part175),(kid09_part176)])

theorem kid09_part152_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid09_part152) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 20 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid09_part153),(kid09_part154),(kid09_part155),(kid09_part156),(kid09_part157),(kid09_part158),(kid09_part159),(kid09_part160),(kid09_part161),(kid09_part162),(kid09_part163),(kid09_part164),(kid09_part165),(kid09_part166),(kid09_part167),(kid09_part168),(kid09_part169),(kid09_part170),(kid09_part171),(kid09_part172),(kid09_part173),(kid09_part174),(kid09_part175),(kid09_part176)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part153_checked

  · exact kid09_part159_checked

  · exact kid09_part165_checked

  · exact kid09_part171_checked

  · exact kid09_part154_checked

  · exact kid09_part160_checked

  · exact kid09_part166_checked

  · exact kid09_part172_checked

  · exact kid09_part155_checked

  · exact kid09_part161_checked

  · exact kid09_part167_checked

  · exact kid09_part173_checked

  · exact kid09_part156_checked

  · exact kid09_part162_checked

  · exact kid09_part168_checked

  · exact kid09_part174_checked

  · exact kid09_part157_checked

  · exact kid09_part163_checked

  · exact kid09_part169_checked

  · exact kid09_part175_checked

  · exact kid09_part158_checked

  · exact kid09_part164_checked

  · exact kid09_part170_checked

  · exact kid09_part176_checked

def kid09_part177 : Audit := .cycle 0 20 true (0)
theorem kid09_part177_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid09_part177) = true := by rfl

def kid09_part178 : Audit := .cycle 1 19 true (0)
theorem kid09_part178_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid09_part178) = true := by rfl

def kid09_part179 : Audit := .cycle 2 18 true (0)
theorem kid09_part179_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid09_part179) = true := by rfl

def kid09_part180 : Audit := .cycle 15 6 true (3)
theorem kid09_part180_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid09_part180) = true := by rfl

def kid09_part181 : Audit := .split 21 (1,true) (byMove [
.cycle 3 24 true (0),
.cycle 0 31 true (0),
.cycle 26 1 false (4),
.cycle 0 26 true (0),
.cycle 23 1 false (5),
.split 22 (5,true) (byMove [
.cycle 0 27 true (0),
.cycle 0 31 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.last 23 (5,false),
.cycle 0 26 true (0),
.cycle 18 5 true (4),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 3 24 true (0),
.last 23 (5,false),
.cycle 21 3 false (5),
.cycle 18 5 false (6),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 0 33 true (0),
.last 23 (5,false),
.cycle 0 26 true (0),
.cycle 18 5 true (4),
.cycle 0 25 true (0),
.cycle 27 1 false (7),
.last 25 (5,false),
.last 23 (5,false)
]),
.cycle 16 6 true (4),
.cycle 0 43 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 29 1 false (7),
.cycle 15 9 true (3),
.cycle 17 9 false (6),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 0 43 true (0),
.cycle 8 16 true (0),
.cycle 0 30 true (0),
.cycle 17 6 true (4),
.last 23 (5,false),
.last 25 (5,false),
.cycle 18 5 true (4),
.cycle 0 25 true (0),
.cycle 27 1 false (7),
.cycle 0 31 true (0),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 40 1 false (10),
.cycle 15 9 true (3),
.cycle 20 3 true (5),
.last 23 (5,false)
]),
.cycle 0 25 true (0),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.split 22 (5,true) (byMove [
.cycle 3 24 true (0),
.cycle 15 10 true (3),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.last 23 (5,false),
.cycle 25 1 false (7),
.last 24 (5,false),
.cycle 30 1 false (8),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 25 (5,false),
.cycle 21 3 false (5),
.cycle 0 27 true (0),
.cycle 27 1 false (7),
.cycle 23 1 false (3),
.cycle 14 12 true (2),
.last 23 (5,false),
.cycle 0 32 true (0),
.cycle 21 2 true (4),
.cycle 3 22 true (0),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 25 (5,false)
]),
.cycle 16 6 true (4),
.cycle 1 22 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.split 22 (5,true) (byMove [
.cycle 16 7 true (4),
.last 24 (5,false),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 25 (5,false),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.last 23 (5,false),
.cycle 0 32 true (0),
.cycle 21 2 true (5),
.cycle 3 22 true (0),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 25 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 20 3 true (5),
.last 23 (5,false)
])
])
theorem kid09_part181_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid09_part181) = true := by rfl

def kid09_part182 : Audit := .split 20 (5,false) (byMove [
.cycle 16 5 true (4),
.split 21 (1,true) (byMove [
.cycle 16 6 true (4),
.cycle 30 1 false (6),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 1 22 true (0),
.cycle 24 1 false (6),
.last 25 (5,true),
.last 23 (5,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 3 22 true (0),
.cycle 20 2 true (5)
]),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.split 21 (5,true) (byMove [
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.last 22 (1,true),
.cycle 21 2 true (4),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 23 (1,true),
.cycle 20 2 true (5)
]),
.cycle 0 21 true (0),
.cycle 12 37 true (0),
.cycle 0 29 true (0),
.cycle 3 18 true (0),
.cycle 17 4 true (4),
.cycle 20 1 true (6),
.cycle 0 30 true (0),
.split 21 (1,true) (byMove [
.last 26 (5,true),
.cycle 0 31 true (0),
.cycle 26 1 false (4),
.cycle 0 26 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 0 43 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.last 22 (5,true),
.cycle 0 25 true (0),
.last 25 (5,true),
.last 23 (5,true),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 1 22 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.last 22 (5,true)
]),
.split 22 (5,true) (byMove [
.cycle 16 7 true (4),
.last 23 (1,true),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 0 26 true (0),
.cycle 0 32 true (0),
.last 23 (1,true),
.cycle 21 2 true (5),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.last 24 (1,true),
.cycle 20 3 true (5)
]),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.split 21 (5,true) (byMove [
.cycle 16 11 true (4),
.last 22 (1,true),
.cycle 26 1 false (4),
.last 24 (1,true),
.cycle 23 1 false (5),
.cycle 23 1 false (3),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.cycle 30 1 false (8),
.cycle 0 25 true (0),
.last 22 (1,true),
.cycle 21 2 true (4),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 23 1 false (3),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 20 3 true (5)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.split 22 (1,true) (byMove [
.last 27 (5,true),
.cycle 32 1 false (6),
.cycle 3 23 true (0),
.cycle 0 27 true (0),
.cycle 0 30 true (0),
.last 23 (5,true),
.cycle 16 7 true (4),
.cycle 0 44 true (0),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 0 26 true (0),
.last 27 (5,true),
.last 24 (5,true),
.cycle 5 18 true (0),
.cycle 14 9 true (2),
.last 23 (5,true),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.last 23 (5,true)
]),
.cycle 20 1 true (6)
])
theorem kid09_part182_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid09_part182) = true := by rfl

def kid09_part134 : Audit := .split 19 (2,true) (byMove [(kid09_part135),(kid09_part136),(kid09_part137),(kid09_part138),(kid09_part139),(kid09_part140),(kid09_part141),(kid09_part142),(kid09_part143),(kid09_part144),(kid09_part145),(kid09_part146),(kid09_part147),(kid09_part148),(kid09_part149),(kid09_part150),(kid09_part151),(kid09_part152),(kid09_part177),(kid09_part178),(kid09_part179),(kid09_part180),(kid09_part181),(kid09_part182)])

theorem kid09_part134_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (kid09_part134) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) 19 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid09_part135),(kid09_part136),(kid09_part137),(kid09_part138),(kid09_part139),(kid09_part140),(kid09_part141),(kid09_part142),(kid09_part143),(kid09_part144),(kid09_part145),(kid09_part146),(kid09_part147),(kid09_part148),(kid09_part149),(kid09_part150),(kid09_part151),(kid09_part152),(kid09_part177),(kid09_part178),(kid09_part179),(kid09_part180),(kid09_part181),(kid09_part182)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part135_checked

  · exact kid09_part141_checked

  · exact kid09_part147_checked

  · exact kid09_part177_checked

  · exact kid09_part136_checked

  · exact kid09_part142_checked

  · exact kid09_part148_checked

  · exact kid09_part178_checked

  · exact kid09_part137_checked

  · exact kid09_part143_checked

  · exact kid09_part149_checked

  · exact kid09_part179_checked

  · exact kid09_part138_checked

  · exact kid09_part144_checked

  · exact kid09_part150_checked

  · exact kid09_part180_checked

  · exact kid09_part139_checked

  · exact kid09_part145_checked

  · exact kid09_part151_checked

  · exact kid09_part181_checked

  · exact kid09_part140_checked

  · exact kid09_part146_checked

  · exact kid09_part152_checked

  · exact kid09_part182_checked

def kid09_part183 : Audit := .cycle 0 20 true (0)
theorem kid09_part183_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,2⟩)) (kid09_part183) = true := by rfl

def kid09_part184 : Audit := .cycle 18 1 false (4)
theorem kid09_part184_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,3⟩)) (kid09_part184) = true := by rfl

def kid09_part185 : Audit := .cycle 17 1 false (5)
theorem kid09_part185_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,4⟩)) (kid09_part185) = true := by rfl

def kid09_part187 : Audit := .split 21 (2,true) (byMove [
.cycle 16 9 false (5),
.split 22 (1,true) (byMove [
.cycle 16 7 false (5),
.cycle 31 1 false (5),
.cycle 31 1 false (5),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 25 1 false (5),
.cycle 23 3 false (3),
.cycle 0 27 true (0),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.last 24 (5,true),
.cycle 16 11 false (5)
]),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.split 22 (5,true) (byMove [
.cycle 16 7 false (5),
.last 23 (1,true),
.cycle 0 25 true (0),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 41 1 false (9),
.cycle 0 31 true (0),
.cycle 28 1 false (6),
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 25 1 false (5),
.last 23 (1,true),
.cycle 0 29 true (0),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 18 6 false (5),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 3 23 true (0),
.cycle 16 11 false (5)
]),
.cycle 0 22 true (0),
.cycle 12 38 true (0),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.cycle 0 35 true (0),
.cycle 0 23 true (0),
.cycle 0 31 true (0),
.split 22 (1,true) (byMove [
.cycle 16 7 false (5),
.cycle 0 32 true (0),
.cycle 28 1 false (2),
.cycle 0 27 true (0),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 16 7 true (3),
.cycle 0 44 true (0),
.cycle 20 4 true (4),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 23 3 false (3),
.cycle 0 32 true (0),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.last 23 (5,true),
.cycle 0 39 true (0),
.cycle 1 23 true (0),
.cycle 21 2 true (4),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.last 23 (5,true)
]),
.cycle 28 1 false (6),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.split 22 (5,true) (byMove [
.cycle 16 7 false (5),
.last 23 (1,true),
.cycle 18 6 false (5),
.last 25 (1,true),
.cycle 24 1 false (4),
.cycle 0 34 true (0),
.cycle 16 7 true (3),
.last 23 (1,true),
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.cycle 0 25 true (0),
.cycle 0 26 true (0),
.last 23 (1,true),
.cycle 18 6 false (5),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.cycle 18 6 false (5),
.cycle 0 39 true (0),
.last 23 (1,true),
.cycle 21 2 true (4),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 32, 36, 64],[16, 64, 32, 1, 8, 32, 64],64⟩
]),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.split 23 (5,true) (byMove [
.cycle 0 35 true (0),
.last 24 (1,true),
.cycle 31 1 false (3),
.last 26 (1,true),
.cycle 0 31 true (0),
.cycle 45 1 false (7),
.cycle 16 8 true (3),
.last 24 (1,true),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 0 32 true (0),
.cycle 0 26 true (0),
.cycle 0 27 true (0),
.last 24 (1,true),
.cycle 0 27 true (0),
.cycle 5 19 true (0),
.cycle 14 10 true (2),
.cycle 12 44 true (0),
.cycle 14 25 true (2),
.last 24 (1,true),
.cycle 21 3 true (5),
.cycle 0 25 true (0),
.cycle 3 22 true (0),
.cycle 14 27 true (2)
]),
.split 35 (5,true) (byMove [
.cycle 23 13 false (6),
.last 36 (1,true),
.cycle 21 15 false (6),
.last 38 (1,true),
.cycle 0 43 true (0),
.cycle 0 67 true (0),
.cycle 13 52 true (1),
.last 36 (1,true),
.cycle 0 79 true (0),
.cycle 0 37 true (0),
.cycle 0 44 true (0),
.cycle 0 38 true (0),
.cycle 0 39 true (0),
.last 36 (1,true),
.cycle 34 2 true (4),
.cycle 5 31 true (0),
.cycle 14 22 true (2),
.cycle 31 8 false (5),
.cycle 0 58 true (0),
.last 36 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 36, 36, 64],[16, 64, 32, 1, 8, 4, 64],64⟩,
.cycle 0 37 true (0),
.cycle 3 34 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 32, 36, 64],[16, 64, 32, 1, 8, 32, 64],64⟩
])
])
theorem kid09_part187_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid09_part187) = true := by rfl

def kid09_part188 : Audit := .cycle 0 22 true (0)
theorem kid09_part188_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid09_part188) = true := by rfl

def kid09_part189 : Audit := .cycle 20 1 false (4)
theorem kid09_part189_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid09_part189) = true := by rfl

def kid09_part190 : Audit := .cycle 19 1 false (3)
theorem kid09_part190_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid09_part190) = true := by rfl

def kid09_part191 : Audit := .cycle 17 2 false (5)
theorem kid09_part191_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid09_part191) = true := by rfl

def kid09_part192 : Audit := .cycle 18 1 false (4)
theorem kid09_part192_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid09_part192) = true := by rfl

def kid09_part193 : Audit := .cycle 16 3 true (4)
theorem kid09_part193_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid09_part193) = true := by rfl

def kid09_part194 : Audit := .split 19 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 17 3 false (5),
.cycle 28 1 false (8),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 17 3 true (4),
.cycle 28 1 false (10),
.cycle 24 1 false (6),
.split 21 (2,true) (byMove [
.cycle 16 6 true (4),
.cycle 19 3 false (5),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 0 43 true (0),
.cycle 24 1 false (6),
.cycle 19 3 false (5),
.cycle 15 9 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 12 39 true (0)
]),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 17 3 false (5),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 15 6 true (3),
.split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.last 24 (2,true),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (7),
.cycle 31 1 false (11),
.cycle 3 22 true (0),
.last 23 (2,true),
.cycle 15 8 true (3),
.cycle 22 1 false (4),
.cycle 0 27 true (0),
.cycle 30 1 false (8),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 28 1 false (8),
.cycle 12 40 true (0)
]),
.cycle 39 1 false (11)
])
theorem kid09_part194_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid09_part194) = true := by rfl

def kid09_part195 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 17 3 false (5),
.cycle 22 1 false (6),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 17 3 true (4),
.cycle 22 1 false (8),
.split 21 (1,true) (byMove [
.cycle 16 6 true (4),
.cycle 30 1 false (6),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 8 16 true (0),
.cycle 24 1 false (6),
.cycle 0 28 true (0),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 0 31 true (0)
]),
.split 22 (1,true) (byMove [
.cycle 16 11 false (5),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.cycle 0 26 true (0),
.cycle 16 7 true (4),
.cycle 31 1 false (9),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.last 23 (5,true),
.cycle 0 28 true (0),
.cycle 20 3 false (5),
.cycle 15 9 true (3),
.cycle 23 1 false (3),
.cycle 17 6 false (5),
.cycle 18 5 false (5),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 21 2 true (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 23 (5,true)
]),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 17 3 false (5),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 15 6 true (3),
.split 21 (5,true) (byMove [
.cycle 48 1 false (10),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.cycle 17 5 false (6),
.cycle 0 25 true (0),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 23 1 false (7),
.cycle 25 1 false (9),
.last 23 (1,true),
.cycle 3 22 true (0),
.cycle 15 8 true (3),
.cycle 22 1 false (4),
.cycle 0 27 true (0),
.cycle 30 1 false (8),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 28 1 false (8),
.cycle 0 32 true (0)
]),
.cycle 0 29 true (0)
])
theorem kid09_part195_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid09_part195) = true := by rfl

def kid09_part196 : Audit := .cycle 0 20 true (0)
theorem kid09_part196_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid09_part196) = true := by rfl

def kid09_part197 : Audit := .cycle 20 1 false (6)
theorem kid09_part197_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid09_part197) = true := by rfl

def kid09_part198 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 17 3 false (5),
.cycle 20 1 true (4),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 17 3 true (4),
.cycle 20 1 true (6),
.split 21 (1,true) (byMove [
.cycle 16 6 true (4),
.cycle 30 1 false (6),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 22 1 true (6),
.cycle 24 1 false (6),
.last 24 (2,true),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 27 true (0),
.cycle 22 1 true (6)
]),
.split 21 (2,true) (byMove [
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 22 1 true (6),
.cycle 24 1 false (6),
.last 22 (1,true),
.cycle 15 9 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 24 (1,true),
.cycle 22 1 true (6)
]),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 17 3 false (5),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 15 6 true (3),
.cycle 28 1 false (8),
.cycle 20 1 true (6)
])
theorem kid09_part198_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid09_part198) = true := by rfl

def kid09_part200 : Audit := .cycle 16 5 false (5)
theorem kid09_part200_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid09_part200) = true := by rfl

def kid09_part201 : Audit := .cycle 0 30 true (0)
theorem kid09_part201_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid09_part201) = true := by rfl

def kid09_part202 : Audit := .split 21 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 25 true (0),
.cycle 42 1 false (10),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.cycle 19 3 false (4),
.cycle 26 1 false (2),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 25 true (0),
.cycle 1 23 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.last 23 (5,true),
.cycle 0 26 true (0)
])
theorem kid09_part202_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid09_part202) = true := by rfl

def kid09_part203 : Audit := .cycle 0 25 true (0)
theorem kid09_part203_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid09_part203) = true := by rfl

def kid09_part204 : Audit := .cycle 22 1 false (4)
theorem kid09_part204_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid09_part204) = true := by rfl

def kid09_part205 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 25 true (0),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.cycle 19 3 false (4),
.last 23 (2,true),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 25 true (0),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 0 26 true (0),
.cycle 0 26 true (0)
])
theorem kid09_part205_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid09_part205) = true := by rfl

def kid09_part206 : Audit := .cycle 16 5 true (3)
theorem kid09_part206_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid09_part206) = true := by rfl

def kid09_part207 : Audit := .cycle 0 42 true (0)
theorem kid09_part207_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid09_part207) = true := by rfl

def kid09_part208 : Audit := .split 21 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 25 1 false (5),
.cycle 0 22 true (0),
.cycle 0 42 true (0),
.cycle 8 15 true (0),
.cycle 0 29 true (0),
.cycle 17 5 true (3),
.cycle 0 33 true (0),
.cycle 0 32 true (0),
.cycle 20 4 true (4),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 39 1 false (9),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 6 17 true (0)
])
theorem kid09_part208_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid09_part208) = true := by rfl

def kid09_part209 : Audit := .cycle 0 22 true (0)
theorem kid09_part209_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid09_part209) = true := by rfl

def kid09_part210 : Audit := .cycle 0 29 true (0)
theorem kid09_part210_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid09_part210) = true := by rfl

def kid09_part211 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 17 7 false (5),
.cycle 25 1 false (5),
.cycle 0 22 true (0),
.cycle 0 42 true (0),
.cycle 8 15 true (0),
.cycle 0 29 true (0),
.cycle 17 5 true (3),
.cycle 22 3 true (5),
.cycle 22 3 true (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 17 7 false (5),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 39 1 false (9),
.cycle 15 8 true (3),
.cycle 41 1 false (9),
.cycle 6 17 true (0)
])
theorem kid09_part211_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid09_part211) = true := by rfl

def kid09_part212 : Audit := .cycle 0 24 true (0)
theorem kid09_part212_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid09_part212) = true := by rfl

def kid09_part213 : Audit := .split 23 (2,true) (byMove [
.cycle 16 8 false (5),
.cycle 21 3 false (3),
.cycle 26 1 false (2),
.cycle 19 6 true (2),
.cycle 25 1 false (3),
.last 24 (5,true),
.cycle 6 18 true (0),
.cycle 12 46 true (0),
.cycle 38 1 false (8),
.cycle 15 9 true (2),
.cycle 0 26 true (0),
.last 24 (5,true),
.cycle 13 11 true (1),
.cycle 21 3 false (3),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.cycle 28 1 false (6),
.last 24 (5,true),
.cycle 0 33 true (0),
.cycle 20 5 false (4),
.cycle 2 24 true (0),
.cycle 0 39 true (0),
.cycle 0 26 true (0),
.last 24 (5,true)
])
theorem kid09_part213_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid09_part213) = true := by rfl

def kid09_part214 : Audit := .split 21 (2,true) (byMove [
.cycle 13 15 true (1),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 24 1 false (6),
.cycle 15 9 true (3),
.cycle 25 1 false (7),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 19 3 false (4),
.cycle 0 30 true (0),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 31 true (0),
.cycle 20 2 true (3),
.cycle 2 22 true (0),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true)
])
theorem kid09_part214_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid09_part214) = true := by rfl

def kid09_part215 : Audit := .cycle 24 1 false (6)
theorem kid09_part215_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid09_part215) = true := by rfl

def kid09_part216 : Audit := .cycle 14 7 true (2)
theorem kid09_part216_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid09_part216) = true := by rfl

def kid09_part217 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 24 1 false (6),
.cycle 18 5 false (4),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 22 5 true (4),
.cycle 19 3 false (4),
.last 23 (2,true),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 31 true (0),
.cycle 20 2 true (3),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 0 34 true (0)
])
theorem kid09_part217_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid09_part217) = true := by rfl

def kid09_part218 : Audit := .cycle 0 27 true (0)
theorem kid09_part218_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid09_part218) = true := by rfl

def kid09_part219 : Audit := .cycle 1 21 true (0)
theorem kid09_part219_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid09_part219) = true := by rfl

def kid09_part220 : Audit := .split 21 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 2 21 true (0),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 12 38 true (0),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.cycle 0 27 true (0),
.cycle 2 23 true (0),
.cycle 0 31 true (0),
.cycle 20 2 true (4),
.cycle 28 1 false (6),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 0 32 true (0)
])
theorem kid09_part220_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid09_part220) = true := by rfl

def kid09_part221 : Audit := .cycle 0 22 true (0)
theorem kid09_part221_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid09_part221) = true := by rfl

def kid09_part222 : Audit := .cycle 3 19 true (0)
theorem kid09_part222_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid09_part222) = true := by rfl

def kid09_part223 : Audit := .split 21 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 33 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.cycle 0 37 true (0),
.cycle 0 22 true (0),
.cycle 12 38 true (0),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.cycle 0 27 true (0),
.cycle 0 35 true (0),
.cycle 0 31 true (0),
.cycle 20 2 true (4),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 18 6 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 3 22 true (0),
.cycle 0 32 true (0)
])
theorem kid09_part223_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid09_part223) = true := by rfl

def kid09_part199 : Audit := .split 20 (1,true) (byMove [(kid09_part200),(kid09_part201),(kid09_part202),(kid09_part203),(kid09_part204),(kid09_part205),(kid09_part206),(kid09_part207),(kid09_part208),(kid09_part209),(kid09_part210),(kid09_part211),(kid09_part212),(kid09_part213),(kid09_part214),(kid09_part215),(kid09_part216),(kid09_part217),(kid09_part218),(kid09_part219),(kid09_part220),(kid09_part221),(kid09_part222),(kid09_part223)])

theorem kid09_part199_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid09_part199) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 20 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid09_part200),(kid09_part201),(kid09_part202),(kid09_part203),(kid09_part204),(kid09_part205),(kid09_part206),(kid09_part207),(kid09_part208),(kid09_part209),(kid09_part210),(kid09_part211),(kid09_part212),(kid09_part213),(kid09_part214),(kid09_part215),(kid09_part216),(kid09_part217),(kid09_part218),(kid09_part219),(kid09_part220),(kid09_part221),(kid09_part222),(kid09_part223)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part200_checked

  · exact kid09_part206_checked

  · exact kid09_part212_checked

  · exact kid09_part218_checked

  · exact kid09_part201_checked

  · exact kid09_part207_checked

  · exact kid09_part213_checked

  · exact kid09_part219_checked

  · exact kid09_part202_checked

  · exact kid09_part208_checked

  · exact kid09_part214_checked

  · exact kid09_part220_checked

  · exact kid09_part203_checked

  · exact kid09_part209_checked

  · exact kid09_part215_checked

  · exact kid09_part221_checked

  · exact kid09_part204_checked

  · exact kid09_part210_checked

  · exact kid09_part216_checked

  · exact kid09_part222_checked

  · exact kid09_part205_checked

  · exact kid09_part211_checked

  · exact kid09_part217_checked

  · exact kid09_part223_checked

def kid09_part225 : Audit := .cycle 16 5 false (5)
theorem kid09_part225_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid09_part225) = true := by rfl

def kid09_part226 : Audit := .split 21 (1,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 24 true (0),
.cycle 32 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.cycle 26 1 false (4),
.cycle 19 3 false (4),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 24 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.last 23 (5,true),
.last 24 (5,true)
])
theorem kid09_part226_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid09_part226) = true := by rfl

def kid09_part227 : Audit := .cycle 23 1 false (3)
theorem kid09_part227_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid09_part227) = true := by rfl

def kid09_part228 : Audit := .split 23 (1,true) (byMove [
.cycle 16 8 true (3),
.cycle 32 1 false (6),
.cycle 25 1 false (3),
.cycle 0 25 true (0),
.cycle 25 1 false (5),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 42 1 false (10),
.cycle 0 32 true (0),
.cycle 29 1 false (7),
.cycle 0 29 true (0),
.cycle 0 28 true (0),
.cycle 26 1 false (6),
.cycle 19 6 true (3),
.cycle 25 1 false (3),
.cycle 15 9 true (3),
.cycle 0 26 true (0),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 15 10 true (3),
.last 25 (5,true),
.last 26 (5,true)
])
theorem kid09_part228_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid09_part228) = true := by rfl

def kid09_part229 : Audit := .cycle 22 1 false (4)
theorem kid09_part229_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid09_part229) = true := by rfl

def kid09_part230 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.last 23 (1,true),
.cycle 32 1 false (8),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 17 5 false (5),
.cycle 18 4 true (3),
.last 23 (1,true),
.cycle 19 3 false (4),
.last 25 (1,true),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.last 23 (1,true),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 0 26 true (0),
.last 23 (1,true)
])
theorem kid09_part230_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid09_part230) = true := by rfl

def kid09_part231 : Audit := .cycle 16 5 true (3)
theorem kid09_part231_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid09_part231) = true := by rfl

def kid09_part232 : Audit := .split 21 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.last 23 (5,true),
.cycle 64 1 false (10),
.cycle 0 22 true (0),
.cycle 0 42 true (0),
.cycle 8 15 true (0),
.cycle 0 29 true (0),
.cycle 17 5 true (3),
.cycle 60 1 false (12),
.cycle 0 33 true (0),
.cycle 12 40 true (0),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.last 23 (5,true),
.cycle 18 6 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 39 1 false (9),
.cycle 15 8 true (3),
.last 23 (5,true),
.last 24 (5,true)
])
theorem kid09_part232_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid09_part232) = true := by rfl

def kid09_part233 : Audit := .cycle 8 15 true (0)
theorem kid09_part233_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid09_part233) = true := by rfl

def kid09_part234 : Audit := .cycle 0 22 true (0)
theorem kid09_part234_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid09_part234) = true := by rfl

def kid09_part235 : Audit := .cycle 0 29 true (0)
theorem kid09_part235_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid09_part235) = true := by rfl

def kid09_part236 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 28 1 false (6),
.cycle 15 8 true (3),
.cycle 17 7 false (5),
.last 23 (1,true),
.cycle 0 22 true (0),
.cycle 0 42 true (0),
.cycle 8 15 true (0),
.cycle 0 29 true (0),
.cycle 17 5 true (3),
.cycle 22 3 true (5),
.last 23 (1,true),
.cycle 22 3 true (4),
.cycle 0 24 true (0),
.cycle 26 1 false (6),
.cycle 17 7 false (5),
.last 23 (1,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 39 1 false (9),
.cycle 15 8 true (3),
.cycle 41 1 false (9),
.last 23 (1,true)
])
theorem kid09_part236_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid09_part236) = true := by rfl

def kid09_part237 : Audit := .cycle 0 24 true (0)
theorem kid09_part237_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid09_part237) = true := by rfl

def kid09_part238 : Audit := .split 21 (1,true) (byMove [
.cycle 16 10 false (5),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 24 1 false (6),
.cycle 31 1 false (9),
.cycle 19 4 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 13 11 true (1),
.cycle 19 3 false (4),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 31 true (0),
.cycle 1 23 true (0),
.cycle 20 2 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true)
])
theorem kid09_part238_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid09_part238) = true := by rfl

def kid09_part239 : Audit := .cycle 26 1 false (6)
theorem kid09_part239_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid09_part239) = true := by rfl

def kid09_part240 : Audit := .cycle 24 1 false (6)
theorem kid09_part240_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid09_part240) = true := by rfl

def kid09_part241 : Audit := .cycle 14 7 true (2)
theorem kid09_part241_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid09_part241) = true := by rfl

def kid09_part242 : Audit := .split 21 (5,true) (byMove [
.cycle 16 10 false (5),
.cycle 15 9 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 24 1 false (6),
.last 22 (1,true),
.cycle 18 5 false (4),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 22 5 true (4),
.last 23 (1,true),
.cycle 19 3 false (4),
.cycle 26 1 false (6),
.cycle 22 1 false (2),
.cycle 17 5 false (5),
.cycle 18 4 false (4),
.cycle 0 31 true (0),
.last 22 (1,true),
.cycle 20 2 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 25 (1,true)
])
theorem kid09_part242_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid09_part242) = true := by rfl

def kid09_part243 : Audit := .split 24 (1,true) (byMove [
.cycle 0 33 true (0),
.cycle 10 18 true (0),
.cycle 0 32 true (0),
.cycle 0 32 true (0),
.cycle 26 1 false (4),
.last 25 (5,true),
.cycle 6 19 true (0),
.cycle 12 32 true (0),
.cycle 20 5 true (4),
.cycle 15 10 true (3),
.cycle 0 27 true (0),
.last 25 (5,true),
.cycle 13 12 true (1),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.cycle 0 29 true (0),
.cycle 29 1 false (7),
.last 25 (5,true),
.cycle 0 34 true (0),
.cycle 1 26 true (0),
.cycle 20 5 true (4),
.cycle 15 10 true (3),
.cycle 0 27 true (0),
.last 25 (5,true)
])
theorem kid09_part243_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid09_part243) = true := by rfl

def kid09_part244 : Audit := .split 21 (1,true) (byMove [
.cycle 16 18 false (5),
.cycle 31 1 false (5),
.cycle 1 22 true (0),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 12 38 true (0),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.cycle 0 27 true (0),
.cycle 1 24 true (0),
.cycle 0 31 true (0),
.cycle 19 5 false (5),
.cycle 20 2 true (4),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 23 (5,true),
.last 24 (5,true)
])
theorem kid09_part244_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid09_part244) = true := by rfl

def kid09_part245 : Audit := .cycle 2 20 true (0)
theorem kid09_part245_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid09_part245) = true := by rfl

def kid09_part246 : Audit := .cycle 0 22 true (0)
theorem kid09_part246_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid09_part246) = true := by rfl

def kid09_part247 : Audit := .cycle 3 19 true (0)
theorem kid09_part247_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid09_part247) = true := by rfl

def kid09_part248 : Audit := .split 21 (5,true) (byMove [
.last 25 (1,true),
.last 22 (1,true),
.last 24 (1,true),
.cycle 0 23 true (0),
.cycle 28 1 false (6),
.last 28 (1,true),
.cycle 0 22 true (0),
.cycle 12 38 true (0),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.last 24 (1,true),
.last 26 (1,true),
.cycle 0 31 true (0),
.last 22 (1,true),
.cycle 20 2 true (4),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 18 6 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 3 22 true (0),
.last 23 (1,true)
])
theorem kid09_part248_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid09_part248) = true := by rfl

def kid09_part224 : Audit := .split 20 (2,true) (byMove [(kid09_part225),(kid09_part226),(kid09_part227),(kid09_part228),(kid09_part229),(kid09_part230),(kid09_part231),(kid09_part232),(kid09_part233),(kid09_part234),(kid09_part235),(kid09_part236),(kid09_part237),(kid09_part238),(kid09_part239),(kid09_part240),(kid09_part241),(kid09_part242),(kid09_part243),(kid09_part244),(kid09_part245),(kid09_part246),(kid09_part247),(kid09_part248)])

theorem kid09_part224_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid09_part224) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 20 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid09_part225),(kid09_part226),(kid09_part227),(kid09_part228),(kid09_part229),(kid09_part230),(kid09_part231),(kid09_part232),(kid09_part233),(kid09_part234),(kid09_part235),(kid09_part236),(kid09_part237),(kid09_part238),(kid09_part239),(kid09_part240),(kid09_part241),(kid09_part242),(kid09_part243),(kid09_part244),(kid09_part245),(kid09_part246),(kid09_part247),(kid09_part248)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part225_checked

  · exact kid09_part231_checked

  · exact kid09_part237_checked

  · exact kid09_part243_checked

  · exact kid09_part226_checked

  · exact kid09_part232_checked

  · exact kid09_part238_checked

  · exact kid09_part244_checked

  · exact kid09_part227_checked

  · exact kid09_part233_checked

  · exact kid09_part239_checked

  · exact kid09_part245_checked

  · exact kid09_part228_checked

  · exact kid09_part234_checked

  · exact kid09_part240_checked

  · exact kid09_part246_checked

  · exact kid09_part229_checked

  · exact kid09_part235_checked

  · exact kid09_part241_checked

  · exact kid09_part247_checked

  · exact kid09_part230_checked

  · exact kid09_part236_checked

  · exact kid09_part242_checked

  · exact kid09_part248_checked

def kid09_part249 : Audit := .cycle 15 5 true (3)
theorem kid09_part249_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid09_part249) = true := by rfl

def kid09_part250 : Audit := .cycle 19 1 false (3)
theorem kid09_part250_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid09_part250) = true := by rfl

def kid09_part251 : Audit := .cycle 17 2 false (5)
theorem kid09_part251_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid09_part251) = true := by rfl

def kid09_part252 : Audit := .cycle 18 1 false (4)
theorem kid09_part252_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid09_part252) = true := by rfl

def kid09_part253 : Audit := .cycle 16 3 true (4)
theorem kid09_part253_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid09_part253) = true := by rfl

def kid09_part254 : Audit := .split 19 (1,true) (byMove [
.cycle 16 4 true (4),
.cycle 28 1 false (6),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 1 21 true (0),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 1 21 true (0),
.cycle 19 3 false (5),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.last 22 (5,true),
.cycle 1 21 true (0)
]),
.cycle 0 21 true (0),
.cycle 21 1 false (5),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 1 21 true (0),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 1 21 true (0),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 29 1 false (7),
.cycle 1 21 true (0)
]),
.cycle 0 20 true (0),
.cycle 38 1 false (10),
.cycle 0 28 true (0),
.cycle 25 1 false (7),
.cycle 17 3 true (4),
.cycle 1 20 true (0),
.cycle 22 1 false (6),
.split 22 (2,true) (byMove [
.cycle 16 7 false (5),
.cycle 20 3 false (4),
.cycle 25 1 false (3),
.cycle 19 6 true (3),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 16 7 true (3),
.cycle 12 42 true (0),
.cycle 8 17 true (0),
.cycle 0 24 true (0),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 20 3 false (4),
.cycle 28 1 false (6),
.cycle 26 1 false (6),
.cycle 14 9 true (2),
.last 23 (5,true),
.cycle 0 35 true (0),
.cycle 19 5 false (5),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.cycle 3 21 true (0),
.last 23 (5,true)
]),
.split 20 (2,true) (byMove [
.cycle 16 13 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.last 24 (5,true),
.cycle 16 5 true (4),
.cycle 0 24 true (0),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.last 21 (5,true),
.cycle 19 3 false (5),
.cycle 28 1 false (6),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 16 5 true (4),
.cycle 19 2 true (4),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.last 21 (5,true)
]),
.cycle 15 5 true (3),
.cycle 0 22 true (0),
.split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.last 23 (2,true),
.cycle 16 5 true (4),
.cycle 18 4 true (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.cycle 1 22 true (0),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 16 5 true (4),
.cycle 19 2 true (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.cycle 1 22 true (0)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 15 6 true (3),
.split 21 (5,true) (byMove [
.cycle 3 24 true (0),
.cycle 15 12 true (3),
.last 22 (2,true),
.cycle 19 5 true (4),
.cycle 23 1 false (5),
.cycle 0 27 true (0),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.cycle 1 23 true (0),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 22 (2,true),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 0 27 true (0),
.cycle 16 6 true (4),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 1 23 true (0)
]),
.cycle 1 20 true (0)
])
theorem kid09_part254_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid09_part254) = true := by rfl

def kid09_part255 : Audit := .split 19 (2,true) (byMove [
.cycle 16 4 true (4),
.split 20 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 28 1 false (6),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 28 1 false (8),
.cycle 25 1 false (5),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.last 22 (5,true),
.cycle 2 20 true (0)
]),
.cycle 22 1 false (4),
.cycle 0 21 true (0),
.cycle 21 1 false (5),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 28 1 false (6),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 28 1 false (8),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 29 1 false (7),
.cycle 2 20 true (0)
]),
.cycle 0 20 true (0),
.cycle 38 1 false (10),
.cycle 0 28 true (0),
.cycle 25 1 false (7),
.cycle 17 3 true (4),
.cycle 38 1 false (10),
.cycle 22 1 false (6),
.split 20 (1,true) (byMove [
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 0 24 true (0),
.cycle 16 5 true (4),
.cycle 29 1 false (9),
.cycle 19 4 true (4),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.last 21 (5,true),
.cycle 0 26 true (0),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 16 5 true (4),
.cycle 1 21 true (0),
.cycle 19 2 true (4),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.last 21 (5,true)
]),
.cycle 15 7 true (3),
.cycle 15 5 true (3),
.cycle 0 22 true (0),
.split 20 (5,true) (byMove [
.cycle 16 9 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 0 24 true (0),
.cycle 16 5 true (4),
.last 21 (1,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.cycle 29 1 false (9),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 16 5 true (4),
.last 21 (1,true),
.cycle 19 2 true (4),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.cycle 2 21 true (0)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 15 6 true (3),
.split 21 (5,true) (byMove [
.cycle 3 24 true (0),
.last 22 (1,true),
.cycle 26 1 false (4),
.last 24 (1,true),
.cycle 23 1 false (5),
.cycle 0 31 true (0),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.cycle 0 43 true (0),
.cycle 0 25 true (0),
.last 22 (1,true),
.cycle 0 25 true (0),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 0 27 true (0),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 2 22 true (0)
]),
.cycle 2 19 true (0)
])
theorem kid09_part255_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid09_part255) = true := by rfl

def kid09_part256 : Audit := .cycle 0 20 true (0)
theorem kid09_part256_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid09_part256) = true := by rfl

def kid09_part257 : Audit := .cycle 25 1 false (7)
theorem kid09_part257_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid09_part257) = true := by rfl

def kid09_part258 : Audit := .split 19 (5,true) (byMove [
.cycle 16 4 true (4),
.split 20 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 21 1 true (3),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 21 1 true (5),
.cycle 25 1 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 0 26 true (0),
.cycle 21 1 true (5)
]),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 21 1 true (3),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (4),
.cycle 21 1 true (5),
.last 22 (1,true),
.last 23 (1,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (7),
.cycle 15 7 true (3),
.cycle 24 1 false (4),
.cycle 21 1 true (5)
]),
.cycle 0 21 true (0),
.cycle 21 1 false (5),
.cycle 21 1 true (3),
.cycle 0 20 true (0),
.cycle 38 1 false (10),
.cycle 0 28 true (0),
.cycle 25 1 false (7),
.cycle 17 3 true (4),
.cycle 20 1 true (6),
.cycle 22 1 false (6),
.split 20 (1,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.last 27 (2,true),
.cycle 16 5 true (4),
.cycle 29 1 false (9),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.last 23 (2,true),
.cycle 0 26 true (0),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 16 5 true (4),
.cycle 1 21 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.cycle 19 2 true (4)
]),
.split 20 (2,true) (byMove [
.cycle 16 13 false (5),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.last 29 (1,true),
.cycle 16 5 true (4),
.last 21 (1,true),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.cycle 0 24 true (0),
.last 22 (1,true),
.last 23 (1,true),
.cycle 15 7 true (3),
.cycle 21 1 false (3),
.cycle 17 4 false (5),
.cycle 18 3 false (5),
.cycle 16 5 true (4),
.last 21 (1,true),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 27 1 false (7),
.cycle 19 2 true (4)
]),
.cycle 15 5 true (3),
.cycle 0 22 true (0),
.cycle 18 3 false (5),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 15 6 true (3),
.cycle 3 20 true (0),
.cycle 20 1 true (6)
])
theorem kid09_part258_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid09_part258) = true := by rfl

def kid09_part186 : Audit := .split 18 (5,false) (byMove [(kid09_part187),(kid09_part188),(kid09_part189),(kid09_part190),(kid09_part191),(kid09_part192),(kid09_part193),(kid09_part194),(kid09_part195),(kid09_part196),(kid09_part197),(kid09_part198),(kid09_part199),(kid09_part224),(kid09_part249),(kid09_part250),(kid09_part251),(kid09_part252),(kid09_part253),(kid09_part254),(kid09_part255),(kid09_part256),(kid09_part257),(kid09_part258)])

theorem kid09_part186_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (kid09_part186) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid09_part187),(kid09_part188),(kid09_part189),(kid09_part190),(kid09_part191),(kid09_part192),(kid09_part193),(kid09_part194),(kid09_part195),(kid09_part196),(kid09_part197),(kid09_part198),(kid09_part199),(kid09_part224),(kid09_part249),(kid09_part250),(kid09_part251),(kid09_part252),(kid09_part253),(kid09_part254),(kid09_part255),(kid09_part256),(kid09_part257),(kid09_part258)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part187_checked

  · exact kid09_part193_checked

  · exact kid09_part199_checked

  · exact kid09_part253_checked

  · exact kid09_part188_checked

  · exact kid09_part194_checked

  · exact kid09_part224_checked

  · exact kid09_part254_checked

  · exact kid09_part189_checked

  · exact kid09_part195_checked

  · exact kid09_part249_checked

  · exact kid09_part255_checked

  · exact kid09_part190_checked

  · exact kid09_part196_checked

  · exact kid09_part250_checked

  · exact kid09_part256_checked

  · exact kid09_part191_checked

  · exact kid09_part197_checked

  · exact kid09_part251_checked

  · exact kid09_part257_checked

  · exact kid09_part192_checked

  · exact kid09_part198_checked

  · exact kid09_part252_checked

  · exact kid09_part258_checked

def kid09_part259 : Audit := .cycle 0 18 true (0)
theorem kid09_part259_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,0⟩)) (kid09_part259) = true := by rfl

def kid09_part260 : Audit := .cycle 1 17 true (0)
theorem kid09_part260_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,1⟩)) (kid09_part260) = true := by rfl

def kid09_part261 : Audit := .cycle 24 1 false (8)
theorem kid09_part261_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,2⟩)) (kid09_part261) = true := by rfl

def kid09_part262 : Audit := .cycle 15 4 true (3)
theorem kid09_part262_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,3⟩)) (kid09_part262) = true := by rfl

def kid09_part263 : Audit := .cycle 17 1 true (5)
theorem kid09_part263_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,4⟩)) (kid09_part263) = true := by rfl

def kid09_part265 : Audit := .cycle 16 3 true (4)
theorem kid09_part265_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid09_part265) = true := by rfl

def kid09_part266 : Audit := .split 19 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 17 3 false (6),
.cycle 28 1 false (6),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 17 3 true (5),
.cycle 28 1 false (8),
.cycle 24 1 false (6),
.split 21 (2,true) (byMove [
.cycle 16 6 true (4),
.cycle 19 3 false (5),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 1 22 true (0),
.cycle 24 1 false (6),
.cycle 19 3 false (5),
.cycle 15 9 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 31 true (0),
.last 27 (5,true)
]),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.split 21 (5,true) (byMove [
.cycle 16 6 true (4),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 31 1 false (5),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 1 22 true (0),
.cycle 24 1 false (6),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 15 11 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 27 true (0),
.cycle 0 26 true (0)
]),
.cycle 0 24 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 15 6 true (3),
.cycle 17 3 true (5),
.cycle 18 2 true (5)
])
theorem kid09_part266_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid09_part266) = true := by rfl

def kid09_part267 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 17 3 false (6),
.cycle 22 1 false (4),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 17 3 true (5),
.cycle 22 1 false (6),
.split 21 (1,true) (byMove [
.cycle 16 6 true (4),
.cycle 30 1 false (6),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 29 1 false (7),
.cycle 24 1 false (6),
.cycle 0 28 true (0),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 34 true (0),
.cycle 26 1 false (6)
]),
.split 22 (1,true) (byMove [
.last 29 (5,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.cycle 25 1 false (3),
.cycle 16 7 true (4),
.cycle 31 1 false (9),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 24 1 false (6),
.last 23 (5,true),
.cycle 0 28 true (0),
.cycle 20 3 false (5),
.cycle 15 9 true (3),
.cycle 23 1 false (3),
.last 24 (5,true),
.cycle 25 1 false (3),
.cycle 16 7 true (4),
.cycle 1 23 true (0),
.cycle 21 2 true (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 23 (5,true)
]),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.split 21 (5,true) (byMove [
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 25 1 false (3),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 29 1 false (7),
.cycle 24 1 false (6),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 25 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 27 true (0),
.cycle 0 26 true (0)
]),
.cycle 22 1 false (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 15 6 true (3),
.cycle 17 3 true (5),
.cycle 18 2 true (5)
])
theorem kid09_part267_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid09_part267) = true := by rfl

def kid09_part268 : Audit := .cycle 0 20 true (0)
theorem kid09_part268_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid09_part268) = true := by rfl

def kid09_part269 : Audit := .cycle 20 1 false (6)
theorem kid09_part269_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid09_part269) = true := by rfl

def kid09_part270 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 17 3 false (6),
.cycle 20 1 false (4),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 17 3 true (5),
.cycle 20 1 false (6),
.split 21 (1,true) (byMove [
.cycle 16 6 true (4),
.cycle 30 1 false (6),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 18 5 false (6),
.cycle 24 1 false (6),
.last 24 (2,true),
.last 22 (2,true),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.cycle 0 34 true (0),
.cycle 26 1 false (6)
]),
.split 21 (2,true) (byMove [
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 23 1 false (5),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 40 1 false (10),
.cycle 0 30 true (0),
.cycle 27 1 false (7),
.cycle 17 5 true (4),
.cycle 18 5 false (6),
.cycle 24 1 false (6),
.last 22 (1,true),
.cycle 15 9 true (3),
.cycle 15 7 true (3),
.cycle 0 24 true (0),
.cycle 19 3 false (5),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 15 8 true (3),
.last 25 (1,true),
.last 24 (1,true)
]),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 0 24 true (0),
.cycle 20 1 false (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 15 6 true (3),
.cycle 17 3 true (5),
.cycle 18 2 true (5)
])
theorem kid09_part270_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid09_part270) = true := by rfl

def kid09_part271 : Audit := .cycle 0 19 true (0)
theorem kid09_part271_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid09_part271) = true := by rfl

def kid09_part272 : Audit := .cycle 37 1 false (11)
theorem kid09_part272_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid09_part272) = true := by rfl

def kid09_part273 : Audit := .cycle 0 27 true (0)
theorem kid09_part273_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid09_part273) = true := by rfl

def kid09_part274 : Audit := .cycle 24 1 false (8)
theorem kid09_part274_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid09_part274) = true := by rfl

def kid09_part275 : Audit := .cycle 17 2 true (5)
theorem kid09_part275_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid09_part275) = true := by rfl

def kid09_part276 : Audit := .cycle 18 1 true (6)
theorem kid09_part276_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid09_part276) = true := by rfl

def kid09_part277 : Audit := .cycle 21 1 false (7)
theorem kid09_part277_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid09_part277) = true := by rfl

def kid09_part279 : Audit := .split 22 (2,true) (byMove [
.cycle 16 7 true (4),
.cycle 16 8 true (4),
.cycle 26 1 false (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 21 3 true (5),
.cycle 0 32 true (0),
.last 26 (5,true),
.cycle 29 1 false (7),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.last 28 (5,true),
.last 27 (5,true)
])
theorem kid09_part279_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid09_part279) = true := by rfl

def kid09_part280 : Audit := .cycle 0 23 true (0)
theorem kid09_part280_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid09_part280) = true := by rfl

def kid09_part281 : Audit := .cycle 21 1 false (5)
theorem kid09_part281_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid09_part281) = true := by rfl

def kid09_part282 : Audit := .cycle 20 1 false (4)
theorem kid09_part282_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid09_part282) = true := by rfl

def kid09_part283 : Audit := .cycle 17 3 false (6)
theorem kid09_part283_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid09_part283) = true := by rfl

def kid09_part284 : Audit := .split 22 (2,true) (byMove [
.cycle 16 7 false (6),
.cycle 19 4 false (5),
.cycle 25 1 false (3),
.cycle 0 28 true (0),
.cycle 24 1 false (4),
.last 23 (5,true),
.last 25 (5,true),
.cycle 60 1 false (12),
.cycle 0 25 true (0),
.cycle 0 29 true (0),
.last 24 (5,true),
.last 26 (5,true),
.cycle 25 1 false (5),
.cycle 19 4 false (5),
.last 28 (5,true),
.last 26 (5,true),
.last 27 (5,true),
.last 23 (5,true),
.last 25 (5,true),
.cycle 1 24 true (0),
.cycle 0 25 true (0),
.cycle 4 19 true (0),
.last 24 (5,true),
.last 25 (5,true)
])
theorem kid09_part284_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid09_part284) = true := by rfl

def kid09_part285 : Audit := .cycle 16 4 true (4)
theorem kid09_part285_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid09_part285) = true := by rfl

def kid09_part286 : Audit := .cycle 28 1 false (10)
theorem kid09_part286_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid09_part286) = true := by rfl

def kid09_part287 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.last 24 (5,true),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.cycle 20 3 true (6),
.cycle 0 31 true (0),
.cycle 19 4 true (5),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.last 22 (5,true),
.last 24 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part287_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid09_part287) = true := by rfl

def kid09_part288 : Audit := .cycle 0 21 true (0)
theorem kid09_part288_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid09_part288) = true := by rfl

def kid09_part289 : Audit := .cycle 21 1 false (7)
theorem kid09_part289_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid09_part289) = true := by rfl

def kid09_part290 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.last 23 (2,true),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.last 23 (2,true),
.last 25 (2,true),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 0 25 true (0),
.last 23 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part290_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid09_part290) = true := by rfl

def kid09_part291 : Audit := .cycle 0 25 true (0)
theorem kid09_part291_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid09_part291) = true := by rfl

def kid09_part292 : Audit := .split 21 (2,true) (byMove [
.last 24 (5,true),
.cycle 19 3 false (5),
.cycle 24 1 false (4),
.cycle 19 6 true (4),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 12 41 true (0),
.cycle 8 16 true (0),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.last 22 (5,true),
.cycle 0 25 true (0),
.cycle 19 3 false (5),
.cycle 27 1 false (7),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 19 5 false (6),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.last 22 (5,true)
])
theorem kid09_part292_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid09_part292) = true := by rfl

def kid09_part293 : Audit := .cycle 15 6 true (3)
theorem kid09_part293_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid09_part293) = true := by rfl

def kid09_part294 : Audit := .cycle 20 1 false (4)
theorem kid09_part294_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid09_part294) = true := by rfl

def kid09_part295 : Audit := .split 21 (5,true) (byMove [
.cycle 16 9 true (4),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 0 27 true (0),
.cycle 23 1 false (5),
.last 25 (2,true),
.cycle 16 6 true (4),
.cycle 12 41 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.last 25 (2,true),
.cycle 0 25 true (0),
.cycle 19 3 false (5),
.last 22 (2,true),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.last 25 (2,true),
.cycle 16 6 true (4),
.cycle 0 25 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 14 11 true (2)
])
theorem kid09_part295_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid09_part295) = true := by rfl

def kid09_part296 : Audit := .split 22 (2,true) (byMove [
.last 25 (5,true),
.cycle 19 4 false (5),
.cycle 25 1 false (3),
.last 26 (5,true),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 6 17 true (0),
.cycle 18 6 false (6),
.cycle 37 1 false (9),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 13 10 true (1),
.cycle 19 4 false (5),
.cycle 0 29 true (0),
.cycle 0 27 true (0),
.cycle 27 1 false (7),
.last 23 (5,true),
.cycle 0 32 true (0),
.last 24 (5,true),
.cycle 2 23 true (0),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true)
])
theorem kid09_part296_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid09_part296) = true := by rfl

def kid09_part297 : Audit := .cycle 16 4 true (4)
theorem kid09_part297_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid09_part297) = true := by rfl

def kid09_part298 : Audit := .cycle 1 20 true (0)
theorem kid09_part298_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid09_part298) = true := by rfl

def kid09_part299 : Audit := .split 20 (2,true) (byMove [
.cycle 16 5 true (4),
.cycle 28 1 false (8),
.cycle 23 1 false (5),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 20 3 true (6),
.cycle 23 1 false (7),
.cycle 19 2 true (5),
.cycle 15 8 true (3),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part299_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid09_part299) = true := by rfl

def kid09_part300 : Audit := .cycle 0 21 true (0)
theorem kid09_part300_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid09_part300) = true := by rfl

def kid09_part301 : Audit := .cycle 26 1 false (8)
theorem kid09_part301_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid09_part301) = true := by rfl

def kid09_part302 : Audit := .split 20 (5,true) (byMove [
.cycle 16 5 true (4),
.cycle 18 4 true (5),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.last 24 (2,true),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.last 23 (2,true),
.cycle 23 1 false (7),
.cycle 19 2 true (5),
.last 21 (2,true),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.last 24 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part302_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid09_part302) = true := by rfl

def kid09_part278 : Audit := .split 19 (1,true) (byMove [(kid09_part279),(kid09_part280),(kid09_part281),(kid09_part282),(kid09_part283),(kid09_part284),(kid09_part285),(kid09_part286),(kid09_part287),(kid09_part288),(kid09_part289),(kid09_part290),(kid09_part291),(kid09_part292),(kid09_part293),(kid09_part294),(kid09_part295),(kid09_part296),(kid09_part297),(kid09_part298),(kid09_part299),(kid09_part300),(kid09_part301),(kid09_part302)])

theorem kid09_part278_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid09_part278) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 19 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid09_part279),(kid09_part280),(kid09_part281),(kid09_part282),(kid09_part283),(kid09_part284),(kid09_part285),(kid09_part286),(kid09_part287),(kid09_part288),(kid09_part289),(kid09_part290),(kid09_part291),(kid09_part292),(kid09_part293),(kid09_part294),(kid09_part295),(kid09_part296),(kid09_part297),(kid09_part298),(kid09_part299),(kid09_part300),(kid09_part301),(kid09_part302)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part279_checked

  · exact kid09_part285_checked

  · exact kid09_part291_checked

  · exact kid09_part297_checked

  · exact kid09_part280_checked

  · exact kid09_part286_checked

  · exact kid09_part292_checked

  · exact kid09_part298_checked

  · exact kid09_part281_checked

  · exact kid09_part287_checked

  · exact kid09_part293_checked

  · exact kid09_part299_checked

  · exact kid09_part282_checked

  · exact kid09_part288_checked

  · exact kid09_part294_checked

  · exact kid09_part300_checked

  · exact kid09_part283_checked

  · exact kid09_part289_checked

  · exact kid09_part295_checked

  · exact kid09_part301_checked

  · exact kid09_part284_checked

  · exact kid09_part290_checked

  · exact kid09_part296_checked

  · exact kid09_part302_checked

def kid09_part304 : Audit := .cycle 16 7 true (4)
theorem kid09_part304_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid09_part304) = true := by rfl

def kid09_part305 : Audit := .cycle 0 23 true (0)
theorem kid09_part305_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid09_part305) = true := by rfl

def kid09_part306 : Audit := .cycle 21 1 false (5)
theorem kid09_part306_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid09_part306) = true := by rfl

def kid09_part307 : Audit := .cycle 20 1 false (4)
theorem kid09_part307_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid09_part307) = true := by rfl

def kid09_part308 : Audit := .cycle 17 3 false (6)
theorem kid09_part308_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid09_part308) = true := by rfl

def kid09_part309 : Audit := .split 24 (1,true) (byMove [
.cycle 16 9 true (3),
.cycle 33 1 false (7),
.cycle 0 29 true (0),
.cycle 0 26 true (0),
.cycle 26 1 false (6),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 43 1 false (11),
.cycle 0 33 true (0),
.cycle 30 1 false (8),
.last 36 (5,true),
.cycle 0 28 true (0),
.cycle 27 1 false (7),
.last 28 (5,true),
.cycle 19 6 true (3),
.cycle 15 10 true (3),
.cycle 0 27 true (0),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 15 11 true (3),
.last 28 (5,true),
.last 27 (5,true)
])
theorem kid09_part309_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid09_part309) = true := by rfl

def kid09_part310 : Audit := .cycle 16 4 true (4)
theorem kid09_part310_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid09_part310) = true := by rfl

def kid09_part311 : Audit := .split 20 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.cycle 0 24 true (0),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.cycle 0 24 true (0),
.cycle 25 1 false (7),
.cycle 41 1 false (11),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.last 22 (5,true),
.cycle 15 8 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part311_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid09_part311) = true := by rfl

def kid09_part312 : Audit := .cycle 22 1 false (8)
theorem kid09_part312_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid09_part312) = true := by rfl

def kid09_part313 : Audit := .cycle 0 21 true (0)
theorem kid09_part313_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid09_part313) = true := by rfl

def kid09_part314 : Audit := .cycle 21 1 false (7)
theorem kid09_part314_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid09_part314) = true := by rfl

def kid09_part315 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.cycle 0 24 true (0),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.cycle 0 24 true (0),
.last 22 (1,true),
.cycle 0 26 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 0 25 true (0),
.cycle 15 8 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part315_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid09_part315) = true := by rfl

def kid09_part316 : Audit := .split 21 (1,true) (byMove [
.last 24 (5,true),
.cycle 0 31 true (0),
.cycle 19 3 false (5),
.cycle 0 26 true (0),
.cycle 23 1 false (5),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 0 43 true (0),
.cycle 0 33 true (0),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.last 22 (5,true),
.cycle 0 25 true (0),
.cycle 13 12 true (1),
.cycle 19 3 false (5),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.last 22 (5,true),
.cycle 16 6 true (4),
.cycle 1 22 true (0),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.last 22 (5,true)
])
theorem kid09_part316_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid09_part316) = true := by rfl

def kid09_part317 : Audit := .split 22 (1,true) (byMove [
.last 29 (5,true),
.cycle 15 10 true (3),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 17 6 false (6),
.last 28 (5,true),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.cycle 19 4 true (4),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 13 12 true (1),
.cycle 20 3 false (5),
.cycle 27 1 false (7),
.cycle 23 1 false (3),
.last 24 (5,true),
.cycle 0 29 true (0),
.cycle 0 32 true (0),
.cycle 1 24 true (0),
.cycle 21 2 true (4),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.last 23 (5,true)
])
theorem kid09_part317_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid09_part317) = true := by rfl

def kid09_part318 : Audit := .cycle 15 6 true (3)
theorem kid09_part318_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid09_part318) = true := by rfl

def kid09_part319 : Audit := .cycle 20 1 false (4)
theorem kid09_part319_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid09_part319) = true := by rfl

def kid09_part320 : Audit := .split 21 (5,true) (byMove [
.cycle 16 9 true (4),
.last 22 (1,true),
.cycle 19 3 false (5),
.last 24 (1,true),
.cycle 23 1 false (5),
.cycle 0 31 true (0),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 0 33 true (0),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.cycle 0 26 true (0),
.cycle 0 25 true (0),
.last 22 (1,true),
.cycle 19 3 false (5),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 0 29 true (0),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 14 11 true (2)
])
theorem kid09_part320_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid09_part320) = true := by rfl

def kid09_part321 : Audit := .cycle 25 1 false (7)
theorem kid09_part321_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid09_part321) = true := by rfl

def kid09_part322 : Audit := .cycle 16 4 true (4)
theorem kid09_part322_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid09_part322) = true := by rfl

def kid09_part323 : Audit := .split 20 (1,true) (byMove [
.cycle 16 5 true (4),
.cycle 29 1 false (7),
.cycle 1 21 true (0),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 0 24 true (0),
.cycle 23 1 false (7),
.cycle 20 5 false (6),
.cycle 19 2 true (5),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part323_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid09_part323) = true := by rfl

def kid09_part324 : Audit := .cycle 2 19 true (0)
theorem kid09_part324_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid09_part324) = true := by rfl

def kid09_part325 : Audit := .cycle 0 21 true (0)
theorem kid09_part325_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid09_part325) = true := by rfl

def kid09_part326 : Audit := .cycle 26 1 false (8)
theorem kid09_part326_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid09_part326) = true := by rfl

def kid09_part327 : Audit := .split 20 (5,true) (byMove [
.cycle 16 5 true (4),
.last 21 (1,true),
.cycle 18 4 true (5),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.cycle 0 25 true (0),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 0 24 true (0),
.cycle 23 1 false (7),
.last 21 (1,true),
.cycle 19 2 true (5),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.cycle 27 1 false (7),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part327_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid09_part327) = true := by rfl

def kid09_part303 : Audit := .split 19 (2,true) (byMove [(kid09_part304),(kid09_part305),(kid09_part306),(kid09_part307),(kid09_part308),(kid09_part309),(kid09_part310),(kid09_part311),(kid09_part312),(kid09_part313),(kid09_part314),(kid09_part315),(kid09_part316),(kid09_part317),(kid09_part318),(kid09_part319),(kid09_part320),(kid09_part321),(kid09_part322),(kid09_part323),(kid09_part324),(kid09_part325),(kid09_part326),(kid09_part327)])

theorem kid09_part303_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid09_part303) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 19 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid09_part304),(kid09_part305),(kid09_part306),(kid09_part307),(kid09_part308),(kid09_part309),(kid09_part310),(kid09_part311),(kid09_part312),(kid09_part313),(kid09_part314),(kid09_part315),(kid09_part316),(kid09_part317),(kid09_part318),(kid09_part319),(kid09_part320),(kid09_part321),(kid09_part322),(kid09_part323),(kid09_part324),(kid09_part325),(kid09_part326),(kid09_part327)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part304_checked

  · exact kid09_part310_checked

  · exact kid09_part316_checked

  · exact kid09_part322_checked

  · exact kid09_part305_checked

  · exact kid09_part311_checked

  · exact kid09_part317_checked

  · exact kid09_part323_checked

  · exact kid09_part306_checked

  · exact kid09_part312_checked

  · exact kid09_part318_checked

  · exact kid09_part324_checked

  · exact kid09_part307_checked

  · exact kid09_part313_checked

  · exact kid09_part319_checked

  · exact kid09_part325_checked

  · exact kid09_part308_checked

  · exact kid09_part314_checked

  · exact kid09_part320_checked

  · exact kid09_part326_checked

  · exact kid09_part309_checked

  · exact kid09_part315_checked

  · exact kid09_part321_checked

  · exact kid09_part327_checked

def kid09_part328 : Audit := .cycle 15 4 true (3)
theorem kid09_part328_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid09_part328) = true := by rfl

def kid09_part329 : Audit := .cycle 0 21 true (0)
theorem kid09_part329_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid09_part329) = true := by rfl

def kid09_part331 : Audit := .split 22 (2,true) (byMove [
.cycle 16 7 true (4),
.last 23 (1,true),
.cycle 26 1 false (4),
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 16 8 true (4),
.cycle 0 23 true (0),
.cycle 12 39 true (0),
.cycle 0 31 true (0),
.cycle 3 20 true (0),
.cycle 17 6 true (4),
.cycle 16 16 true (4),
.cycle 0 32 true (0),
.last 23 (1,true),
.cycle 29 1 false (7),
.cycle 15 8 true (3),
.cycle 0 25 true (0),
.cycle 16 11 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 9 true (3),
.cycle 16 13 true (4),
.cycle 16 12 true (4)
])
theorem kid09_part331_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid09_part331) = true := by rfl

def kid09_part332 : Audit := .cycle 0 23 true (0)
theorem kid09_part332_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid09_part332) = true := by rfl

def kid09_part333 : Audit := .cycle 21 1 false (5)
theorem kid09_part333_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid09_part333) = true := by rfl

def kid09_part334 : Audit := .cycle 20 1 false (4)
theorem kid09_part334_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid09_part334) = true := by rfl

def kid09_part335 : Audit := .cycle 17 3 false (6)
theorem kid09_part335_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid09_part335) = true := by rfl

def kid09_part336 : Audit := .cycle 20 1 false (4)
theorem kid09_part336_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid09_part336) = true := by rfl

def kid09_part337 : Audit := .cycle 16 4 true (4)
theorem kid09_part337_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid09_part337) = true := by rfl

def kid09_part338 : Audit := .split 20 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.cycle 21 1 false (5),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.cycle 21 1 false (7),
.cycle 25 1 false (7),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 41 1 false (11),
.cycle 21 1 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part338_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid09_part338) = true := by rfl

def kid09_part339 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 17 4 true (5),
.cycle 21 1 false (5),
.cycle 0 21 true (0),
.cycle 28 1 false (10),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 17 4 true (5),
.cycle 21 1 false (7),
.last 22 (1,true),
.last 23 (1,true),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 0 31 true (0),
.cycle 21 1 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 1 false (9),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part339_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid09_part339) = true := by rfl

def kid09_part340 : Audit := .cycle 0 21 true (0)
theorem kid09_part340_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid09_part340) = true := by rfl

def kid09_part341 : Audit := .cycle 21 1 false (7)
theorem kid09_part341_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid09_part341) = true := by rfl

def kid09_part342 : Audit := .cycle 21 1 false (7)
theorem kid09_part342_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid09_part342) = true := by rfl

def kid09_part343 : Audit := .split 21 (1,true) (byMove [
.cycle 27 1 false (7),
.cycle 0 31 true (0),
.last 22 (2,true),
.cycle 0 26 true (0),
.cycle 23 1 false (5),
.cycle 19 3 false (5),
.cycle 16 6 true (4),
.cycle 0 43 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.cycle 13 15 true (1),
.cycle 0 25 true (0),
.last 24 (2,true),
.last 22 (2,true),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 19 3 false (5),
.cycle 16 6 true (4),
.cycle 1 22 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.cycle 0 32 true (0)
])
theorem kid09_part343_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid09_part343) = true := by rfl

def kid09_part344 : Audit := .split 21 (2,true) (byMove [
.last 25 (1,true),
.last 22 (1,true),
.cycle 24 1 false (4),
.last 24 (1,true),
.cycle 23 1 false (5),
.cycle 19 3 false (5),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 8 16 true (0),
.cycle 0 23 true (0),
.cycle 0 30 true (0),
.last 28 (1,true),
.cycle 0 25 true (0),
.last 22 (1,true),
.cycle 27 1 false (7),
.cycle 25 1 false (7),
.cycle 14 8 true (2),
.cycle 19 3 false (5),
.cycle 16 6 true (4),
.last 22 (1,true),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 3 20 true (0),
.last 23 (1,true)
])
theorem kid09_part344_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid09_part344) = true := by rfl

def kid09_part345 : Audit := .cycle 15 6 true (3)
theorem kid09_part345_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid09_part345) = true := by rfl

def kid09_part346 : Audit := .cycle 20 1 false (4)
theorem kid09_part346_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid09_part346) = true := by rfl

def kid09_part347 : Audit := .cycle 14 8 true (2)
theorem kid09_part347_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid09_part347) = true := by rfl

def kid09_part348 : Audit := .cycle 20 1 false (4)
theorem kid09_part348_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid09_part348) = true := by rfl

def kid09_part349 : Audit := .cycle 16 4 true (4)
theorem kid09_part349_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid09_part349) = true := by rfl

def kid09_part350 : Audit := .split 20 (1,true) (byMove [
.cycle 16 5 true (4),
.cycle 29 1 false (7),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.cycle 1 21 true (0),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 1 25 true (0),
.cycle 23 1 false (7),
.last 23 (2,true),
.last 21 (2,true),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part350_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid09_part350) = true := by rfl

def kid09_part351 : Audit := .split 20 (2,true) (byMove [
.cycle 16 5 true (4),
.last 21 (1,true),
.cycle 23 1 false (5),
.cycle 0 22 true (0),
.cycle 22 1 false (6),
.cycle 28 1 false (8),
.cycle 0 21 true (0),
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 26 1 false (8),
.cycle 17 4 true (5),
.cycle 43 1 false (11),
.cycle 23 1 false (7),
.last 21 (1,true),
.cycle 15 8 true (3),
.cycle 15 6 true (3),
.cycle 0 23 true (0),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 15 7 true (3),
.cycle 17 4 true (5),
.cycle 18 3 true (5)
])
theorem kid09_part351_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid09_part351) = true := by rfl

def kid09_part352 : Audit := .cycle 0 21 true (0)
theorem kid09_part352_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid09_part352) = true := by rfl

def kid09_part353 : Audit := .cycle 26 1 false (8)
theorem kid09_part353_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid09_part353) = true := by rfl

def kid09_part354 : Audit := .cycle 18 3 true (5)
theorem kid09_part354_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid09_part354) = true := by rfl

def kid09_part330 : Audit := .split 19 (5,true) (byMove [(kid09_part331),(kid09_part332),(kid09_part333),(kid09_part334),(kid09_part335),(kid09_part336),(kid09_part337),(kid09_part338),(kid09_part339),(kid09_part340),(kid09_part341),(kid09_part342),(kid09_part343),(kid09_part344),(kid09_part345),(kid09_part346),(kid09_part347),(kid09_part348),(kid09_part349),(kid09_part350),(kid09_part351),(kid09_part352),(kid09_part353),(kid09_part354)])

theorem kid09_part330_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid09_part330) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid09_part331),(kid09_part332),(kid09_part333),(kid09_part334),(kid09_part335),(kid09_part336),(kid09_part337),(kid09_part338),(kid09_part339),(kid09_part340),(kid09_part341),(kid09_part342),(kid09_part343),(kid09_part344),(kid09_part345),(kid09_part346),(kid09_part347),(kid09_part348),(kid09_part349),(kid09_part350),(kid09_part351),(kid09_part352),(kid09_part353),(kid09_part354)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part331_checked

  · exact kid09_part337_checked

  · exact kid09_part343_checked

  · exact kid09_part349_checked

  · exact kid09_part332_checked

  · exact kid09_part338_checked

  · exact kid09_part344_checked

  · exact kid09_part350_checked

  · exact kid09_part333_checked

  · exact kid09_part339_checked

  · exact kid09_part345_checked

  · exact kid09_part351_checked

  · exact kid09_part334_checked

  · exact kid09_part340_checked

  · exact kid09_part346_checked

  · exact kid09_part352_checked

  · exact kid09_part335_checked

  · exact kid09_part341_checked

  · exact kid09_part347_checked

  · exact kid09_part353_checked

  · exact kid09_part336_checked

  · exact kid09_part342_checked

  · exact kid09_part348_checked

  · exact kid09_part354_checked

def kid09_part355 : Audit := .cycle 0 19 true (0)
theorem kid09_part355_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid09_part355) = true := by rfl

def kid09_part356 : Audit := .cycle 1 18 true (0)
theorem kid09_part356_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid09_part356) = true := by rfl

def kid09_part357 : Audit := .cycle 2 17 true (0)
theorem kid09_part357_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid09_part357) = true := by rfl

def kid09_part358 : Audit := .cycle 15 5 true (3)
theorem kid09_part358_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid09_part358) = true := by rfl

def kid09_part359 : Audit := .cycle 17 2 true (5)
theorem kid09_part359_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid09_part359) = true := by rfl

def kid09_part360 : Audit := .cycle 18 1 true (6)
theorem kid09_part360_checked : zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid09_part360) = true := by rfl

def kid09_part264 : Audit := .split 18 (5,false) (byMove [(kid09_part265),(kid09_part266),(kid09_part267),(kid09_part268),(kid09_part269),(kid09_part270),(kid09_part271),(kid09_part272),(kid09_part273),(kid09_part274),(kid09_part275),(kid09_part276),(kid09_part277),(kid09_part278),(kid09_part303),(kid09_part328),(kid09_part329),(kid09_part330),(kid09_part355),(kid09_part356),(kid09_part357),(kid09_part358),(kid09_part359),(kid09_part360)])

theorem kid09_part264_checked : zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (kid09_part264) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid09_part265),(kid09_part266),(kid09_part267),(kid09_part268),(kid09_part269),(kid09_part270),(kid09_part271),(kid09_part272),(kid09_part273),(kid09_part274),(kid09_part275),(kid09_part276),(kid09_part277),(kid09_part278),(kid09_part303),(kid09_part328),(kid09_part329),(kid09_part330),(kid09_part355),(kid09_part356),(kid09_part357),(kid09_part358),(kid09_part359),(kid09_part360)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part265_checked

  · exact kid09_part271_checked

  · exact kid09_part277_checked

  · exact kid09_part355_checked

  · exact kid09_part266_checked

  · exact kid09_part272_checked

  · exact kid09_part278_checked

  · exact kid09_part356_checked

  · exact kid09_part267_checked

  · exact kid09_part273_checked

  · exact kid09_part303_checked

  · exact kid09_part357_checked

  · exact kid09_part268_checked

  · exact kid09_part274_checked

  · exact kid09_part328_checked

  · exact kid09_part358_checked

  · exact kid09_part269_checked

  · exact kid09_part275_checked

  · exact kid09_part329_checked

  · exact kid09_part359_checked

  · exact kid09_part270_checked

  · exact kid09_part276_checked

  · exact kid09_part330_checked

  · exact kid09_part360_checked

def kid09 : Audit := .split 17 (4,false) (byMove [(kid09_part1),(kid09_part2),(kid09_part3),(kid09_part4),(kid09_part5),(kid09_part6),(kid09_part55),(kid09_part56),(kid09_part57),(kid09_part58),(kid09_part59),(kid09_part60),(kid09_part85),(kid09_part134),(kid09_part183),(kid09_part184),(kid09_part185),(kid09_part186),(kid09_part259),(kid09_part260),(kid09_part261),(kid09_part262),(kid09_part263),(kid09_part264)])

theorem check09 : zipCheck 944 (child ⟨false,true,3⟩) (kid09) = true := by

  change (zipQueryOK 944 (child ⟨false,true,3⟩) 17 (4,false) && allMoves (fun mv => zipCheck 944 (refine (child ⟨false,true,3⟩) (4,false) (some mv)) (byMove [(kid09_part1),(kid09_part2),(kid09_part3),(kid09_part4),(kid09_part5),(kid09_part6),(kid09_part55),(kid09_part56),(kid09_part57),(kid09_part58),(kid09_part59),(kid09_part60),(kid09_part85),(kid09_part134),(kid09_part183),(kid09_part184),(kid09_part185),(kid09_part186),(kid09_part259),(kid09_part260),(kid09_part261),(kid09_part262),(kid09_part263),(kid09_part264)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid09_part1_checked

  · exact kid09_part55_checked

  · exact kid09_part85_checked

  · exact kid09_part259_checked

  · exact kid09_part2_checked

  · exact kid09_part56_checked

  · exact kid09_part134_checked

  · exact kid09_part260_checked

  · exact kid09_part3_checked

  · exact kid09_part57_checked

  · exact kid09_part183_checked

  · exact kid09_part261_checked

  · exact kid09_part4_checked

  · exact kid09_part58_checked

  · exact kid09_part184_checked

  · exact kid09_part262_checked

  · exact kid09_part5_checked

  · exact kid09_part59_checked

  · exact kid09_part185_checked

  · exact kid09_part263_checked

  · exact kid09_part6_checked

  · exact kid09_part60_checked

  · exact kid09_part186_checked

  · exact kid09_part264_checked

end BB6.Agent11Raw39B0RE
