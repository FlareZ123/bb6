import Raw39B0REBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid21_part1 : Audit := .cycle 0 12 true (0)
theorem kid21_part1_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,0⟩)) (kid21_part1) = true := by rfl

def kid21_part2 : Audit := .cycle 1 11 true (1)
theorem kid21_part2_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,1⟩)) (kid21_part2) = true := by rfl

def kid21_part3 : Audit := .cycle 5 16 true (0)
theorem kid21_part3_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,2⟩)) (kid21_part3) = true := by rfl

def kid21_part4 : Audit := .cycle 31 1 false (5)
theorem kid21_part4_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,3⟩)) (kid21_part4) = true := by rfl

def kid21_part5 : Audit := .cycle 20 1 false (2)
theorem kid21_part5_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,4⟩)) (kid21_part5) = true := by rfl

def kid21_part7 : Audit := .cycle 0 13 true (0)
theorem kid21_part7_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid21_part7) = true := by rfl

def kid21_part8 : Audit := .cycle 1 12 true (1)
theorem kid21_part8_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid21_part8) = true := by rfl

def kid21_part9 : Audit := .cycle 37 1 false (5)
theorem kid21_part9_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid21_part9) = true := by rfl

def kid21_part10 : Audit := .cycle 0 20 true (0)
theorem kid21_part10_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid21_part10) = true := by rfl

def kid21_part11 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (5),
.cycle 27 2 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 17 true (0),
.cycle 27 2 false (5),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 2 false (1),
.cycle 17 2 false (1),
.split 18 (1,true) (byMove [
.cycle 20 2 false (0),
.cycle 30 2 false (2),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 23 2 false (1),
.cycle 16 3 false (0),
.cycle 0 19 true (-1),
.cycle 39 2 false (1),
.cycle 0 27 true (-1),
.cycle 27 2 false (3),
.cycle 25 2 false (1),
.cycle 14 5 false (2),
.cycle 24 2 false (2),
.last 21 (2,true),
.last 19 (2,true),
.cycle 21 2 false (1),
.cycle 0 21 true (-1),
.cycle 16 3 false (0),
.cycle 49 2 false (1),
.cycle 40 2 false (2),
.cycle 2 17 false (5),
.cycle 13 9 false (3),
.cycle 26 2 false (2),
.cycle 13 11 false (3)
]),
.split 18 (2,true) (byMove [
.cycle 20 2 false (0),
.last 19 (1,true),
.cycle 21 1 false (-1),
.cycle 0 20 true (-1),
.cycle 23 2 false (1),
.cycle 16 3 false (0),
.cycle 0 19 true (-1),
.cycle 39 2 false (1),
.cycle 0 27 true (-1),
.cycle 27 2 false (3),
.cycle 25 2 false (1),
.cycle 14 5 false (2),
.cycle 24 2 false (2),
.last 19 (1,true),
.cycle 23 2 false (1),
.cycle 21 2 false (1),
.cycle 0 21 true (-1),
.cycle 16 3 false (0),
.last 36 (1,true),
.last 35 (1,true),
.cycle 2 17 false (5),
.cycle 13 9 false (3),
.last 21 (1,true),
.cycle 13 11 false (3)
]),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 26 2 false (4),
.cycle 20 2 false (2),
.cycle 15 2 true (0),
.cycle 22 2 false (2)
])
theorem kid21_part11_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid21_part11) = true := by rfl

def kid21_part12 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (5),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 17 true (0),
.cycle 28 1 false (4),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.split 18 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 31 1 false (1),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 24 1 false (0),
.cycle 16 3 false (0),
.cycle 0 19 true (-1),
.cycle 12 19 false (5),
.cycle 0 27 true (-1),
.cycle 28 1 false (2),
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.cycle 25 1 false (1),
.last 21 (2,true),
.last 19 (2,true),
.cycle 22 1 false (0),
.cycle 0 21 true (-1),
.cycle 16 3 false (0),
.cycle 13 29 false (6),
.cycle 41 1 false (1),
.cycle 2 17 false (5),
.cycle 14 9 false (2),
.cycle 27 1 false (1),
.cycle 27 1 false (1)
]),
.split 18 (2,true) (byMove [
.cycle 21 1 false (-1),
.last 19 (1,true),
.cycle 21 1 false (-1),
.cycle 0 20 true (-1),
.cycle 24 1 false (0),
.cycle 16 3 false (0),
.cycle 0 19 true (-1),
.cycle 12 19 false (5),
.cycle 0 27 true (-1),
.cycle 28 1 false (2),
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.cycle 25 1 false (1),
.last 19 (1,true),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 0 21 true (-1),
.cycle 16 3 false (0),
.last 36 (1,true),
.last 35 (1,true),
.cycle 2 17 false (5),
.cycle 14 9 false (2),
.last 21 (1,true),
.last 21 (1,true)
]),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 27 1 false (3),
.cycle 21 1 false (1),
.cycle 16 2 true (0),
.cycle 15 2 true (0)
])
theorem kid21_part12_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid21_part12) = true := by rfl

def kid21_part13 : Audit := .cycle 0 13 true (0)
theorem kid21_part13_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid21_part13) = true := by rfl

def kid21_part14 : Audit := .cycle 1 12 true (1)
theorem kid21_part14_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid21_part14) = true := by rfl

def kid21_part15 : Audit := .cycle 0 27 true (0)
theorem kid21_part15_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid21_part15) = true := by rfl

def kid21_part16 : Audit := .cycle 5 16 true (0)
theorem kid21_part16_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid21_part16) = true := by rfl

def kid21_part17 : Audit := .cycle 11 2 true (4)
theorem kid21_part17_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid21_part17) = true := by rfl

def kid21_part18 : Audit := .cycle 12 1 true (4)
theorem kid21_part18_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid21_part18) = true := by rfl

def kid21_part19 : Audit := .split 14 (1,true) (byMove [
.cycle 32 5 false (3),
.cycle 1 15 true (1),
.split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.cycle 23 5 false (3),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 33 5 false (3),
.cycle 12 4 true (3),
.cycle 29 3 false (2),
.cycle 0 26 true (0),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 27 5 false (5),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 6 11 true (2)
]),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.cycle 23 5 false (3),
.cycle 20 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 33 5 false (3),
.cycle 12 4 true (3),
.cycle 29 3 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 27 5 false (5),
.cycle 20 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 15 2 true (3),
.cycle 6 11 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 6 11 true (2),
.cycle 12 3 true (3),
.cycle 6 9 true (2),
.split 17 (2,true) (byMove [
.cycle 23 8 false (1),
.cycle 22 3 false (0),
.cycle 41 1 false (3),
.cycle 13 6 true (2),
.cycle 4 15 true (1),
.last 18 (5,true),
.cycle 6 21 true (1),
.cycle 1 20 true (1),
.cycle 5 43 true (1),
.cycle 0 19 true (0),
.cycle 7 11 true (2),
.last 18 (5,true),
.cycle 0 21 true (0),
.cycle 22 3 false (0),
.cycle 5 15 true (1),
.cycle 5 13 true (1),
.cycle 5 25 true (1),
.last 18 (5,true),
.cycle 6 15 true (2),
.cycle 24 5 false (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.cycle 0 50 true (-1),
.last 18 (5,true)
]),
.split 15 (2,true) (byMove [
.cycle 6 16 true (2),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.cycle 33 1 false (3),
.cycle 23 5 false (3),
.last 20 (5,true),
.cycle 10 6 true (3),
.cycle 0 19 true (0),
.cycle 0 31 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 5 19 true (0),
.cycle 5 15 true (1),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.cycle 0 25 true (0),
.last 20 (5,true),
.cycle 6 13 true (2),
.cycle 14 2 true (3),
.cycle 2 15 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.last 30 (2,true),
.cycle 33 1 false (3),
.cycle 23 5 false (3),
.cycle 20 4 false (0),
.cycle 10 6 true (3),
.cycle 5 25 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 12 5 true (3),
.cycle 5 19 true (0),
.last 17 (2,true),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.cycle 0 25 true (0),
.cycle 20 4 false (0),
.cycle 6 13 true (2),
.cycle 14 2 true (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 6 12 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.split 16 (5,true) (byMove [
.cycle 38 7 false (3),
.cycle 1 19 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 23 6 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 6 13 true (2),
.cycle 12 5 true (3),
.cycle 6 11 true (2),
.cycle 7 11 true (3),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 0 23 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 15 2 true (4),
.cycle 6 12 true (2)
]),
.cycle 6 10 true (2)
])
theorem kid21_part19_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid21_part19) = true := by rfl

def kid21_part21 : Audit := .split 28 (1,true) (byMove [
.cycle 23 7 false (2),
.cycle 0 32 true (-1),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 29 5 false (-1),
.cycle 29 5 false (-1),
.cycle 29 5 false (2),
.cycle 39 5 false (6),
.cycle 0 30 true (0),
.cycle 0 30 true (0),
.cycle 32 5 false (3),
.last 29 (5,true),
.cycle 0 34 true (-1),
.cycle 29 5 false (0),
.cycle 31 5 false (2),
.cycle 29 1 false (-1),
.cycle 29 5 false (-1),
.cycle 29 5 false (-1),
.cycle 25 4 true (0),
.cycle 1 29 true (0),
.cycle 29 5 false (1),
.cycle 0 30 true (0),
.cycle 20 12 true (0),
.last 29 (5,true)
])
theorem kid21_part21_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid21_part21) = true := by rfl

def kid21_part22 : Audit := .split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 33 5 false (3),
.cycle 12 4 true (3),
.cycle 6 12 true (2),
.cycle 22 3 false (0),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.last 18 (5,true)
])
theorem kid21_part22_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid21_part22) = true := by rfl

def kid21_part23 : Audit := .cycle 0 24 true (0)
theorem kid21_part23_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid21_part23) = true := by rfl

def kid21_part24 : Audit := .cycle 0 16 true (0)
theorem kid21_part24_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid21_part24) = true := by rfl

def kid21_part25 : Audit := .cycle 7 8 true (3)
theorem kid21_part25_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid21_part25) = true := by rfl

def kid21_part26 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.last 18 (1,true),
.cycle 20 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.last 28 (1,true),
.cycle 12 4 true (3),
.last 17 (1,true),
.last 22 (1,true),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.last 18 (1,true),
.cycle 20 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 15 2 true (3),
.last 17 (1,true)
])
theorem kid21_part26_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid21_part26) = true := by rfl

def kid21_part27 : Audit := .cycle 0 15 true (0)
theorem kid21_part27_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid21_part27) = true := by rfl

def kid21_part28 : Audit := .cycle 1 14 true (1)
theorem kid21_part28_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid21_part28) = true := by rfl

def kid21_part29 : Audit := .cycle 0 23 true (0)
theorem kid21_part29_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid21_part29) = true := by rfl

def kid21_part30 : Audit := .cycle 3 12 true (1)
theorem kid21_part30_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid21_part30) = true := by rfl

def kid21_part31 : Audit := .split 17 (1,true) (byMove [
.cycle 27 14 false (3),
.cycle 0 21 true (0),
.cycle 43 1 false (1),
.cycle 37 1 false (3),
.cycle 18 7 false (2),
.last 24 (5,true),
.cycle 10 8 true (3),
.cycle 1 18 true (1),
.cycle 11 8 true (3),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.last 18 (5,true),
.cycle 0 23 true (0),
.cycle 7 13 true (2),
.cycle 9 10 true (2),
.cycle 45 1 false (3),
.cycle 18 7 false (2),
.cycle 0 23 true (0),
.cycle 15 4 true (3),
.cycle 1 18 true (1),
.cycle 14 4 true (3),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.last 18 (5,true)
])
theorem kid21_part31_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid21_part31) = true := by rfl

def kid21_part32 : Audit := .cycle 12 3 true (3)
theorem kid21_part32_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid21_part32) = true := by rfl

def kid21_part33 : Audit := .cycle 6 9 true (2)
theorem kid21_part33_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid21_part33) = true := by rfl

def kid21_part34 : Audit := .split 15 (1,true) (byMove [
.cycle 23 10 false (2),
.cycle 0 19 true (0),
.cycle 35 1 false (1),
.cycle 33 1 false (3),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 10 6 true (3),
.cycle 1 16 true (1),
.cycle 13 4 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 21 true (0),
.cycle 22 3 false (0),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 15 4 true (3),
.cycle 1 16 true (1),
.cycle 14 2 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
])
theorem kid21_part34_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid21_part34) = true := by rfl

def kid21_part35 : Audit := .cycle 9 8 true (2)
theorem kid21_part35_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid21_part35) = true := by rfl

def kid21_part36 : Audit := .cycle 9 6 true (3)
theorem kid21_part36_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid21_part36) = true := by rfl

def kid21_part37 : Audit := .cycle 0 17 true (0)
theorem kid21_part37_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid21_part37) = true := by rfl

def kid21_part38 : Audit := .split 15 (5,true) (byMove [
.cycle 23 10 false (2),
.cycle 0 19 true (0),
.cycle 36 1 false (0),
.cycle 33 1 false (3),
.last 18 (1,true),
.cycle 20 4 false (0),
.cycle 10 6 true (3),
.last 16 (1,true),
.last 28 (1,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 12 5 true (3),
.last 17 (1,true),
.last 22 (1,true),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.last 18 (1,true),
.cycle 20 4 false (0),
.last 19 (1,true),
.last 16 (1,true),
.cycle 14 2 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 18 (1,true)
])
theorem kid21_part38_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid21_part38) = true := by rfl

def kid21_part39 : Audit := .cycle 0 15 true (0)
theorem kid21_part39_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid21_part39) = true := by rfl

def kid21_part40 : Audit := .cycle 1 14 true (1)
theorem kid21_part40_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid21_part40) = true := by rfl

def kid21_part41 : Audit := .cycle 2 13 true (1)
theorem kid21_part41_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid21_part41) = true := by rfl

def kid21_part42 : Audit := .cycle 8 7 true (3)
theorem kid21_part42_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid21_part42) = true := by rfl

def kid21_part43 : Audit := .split 16 (5,true) (byMove [
.last 34 (1,true),
.last 17 (1,true),
.cycle 0 28 true (0),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 23 6 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.last 19 (1,true),
.cycle 12 5 true (3),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 7 11 true (3),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 0 23 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 15 2 true (4),
.last 18 (1,true)
])
theorem kid21_part43_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid21_part43) = true := by rfl

def kid21_part44 : Audit := .split 16 (1,true) (byMove [
.cycle 27 9 false (3),
.cycle 0 26 true (0),
.cycle 5 22 true (0),
.cycle 0 21 true (0),
.cycle 4 14 true (1),
.last 17 (5,true),
.cycle 10 7 true (3),
.cycle 1 17 true (1),
.cycle 14 3 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 20 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.last 17 (5,true),
.cycle 15 4 true (4),
.cycle 1 17 true (1),
.cycle 14 3 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
])
theorem kid21_part44_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid21_part44) = true := by rfl

def kid21_part20 : Audit := .split 14 (2,true) (byMove [(kid21_part21),(kid21_part22),(kid21_part23),(kid21_part24),(kid21_part25),(kid21_part26),(kid21_part27),(kid21_part28),(kid21_part29),(kid21_part30),(kid21_part31),(kid21_part32),(kid21_part33),(kid21_part34),(kid21_part35),(kid21_part36),(kid21_part37),(kid21_part38),(kid21_part39),(kid21_part40),(kid21_part41),(kid21_part42),(kid21_part43),(kid21_part44)])

theorem kid21_part20_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid21_part20) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid21_part21),(kid21_part22),(kid21_part23),(kid21_part24),(kid21_part25),(kid21_part26),(kid21_part27),(kid21_part28),(kid21_part29),(kid21_part30),(kid21_part31),(kid21_part32),(kid21_part33),(kid21_part34),(kid21_part35),(kid21_part36),(kid21_part37),(kid21_part38),(kid21_part39),(kid21_part40),(kid21_part41),(kid21_part42),(kid21_part43),(kid21_part44)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part21_checked

  · exact kid21_part27_checked

  · exact kid21_part33_checked

  · exact kid21_part39_checked

  · exact kid21_part22_checked

  · exact kid21_part28_checked

  · exact kid21_part34_checked

  · exact kid21_part40_checked

  · exact kid21_part23_checked

  · exact kid21_part29_checked

  · exact kid21_part35_checked

  · exact kid21_part41_checked

  · exact kid21_part24_checked

  · exact kid21_part30_checked

  · exact kid21_part36_checked

  · exact kid21_part42_checked

  · exact kid21_part25_checked

  · exact kid21_part31_checked

  · exact kid21_part37_checked

  · exact kid21_part43_checked

  · exact kid21_part26_checked

  · exact kid21_part32_checked

  · exact kid21_part38_checked

  · exact kid21_part44_checked

def kid21_part45 : Audit := .cycle 0 15 true (0)
theorem kid21_part45_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid21_part45) = true := by rfl

def kid21_part46 : Audit := .cycle 32 1 false (4)
theorem kid21_part46_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid21_part46) = true := by rfl

def kid21_part48 : Audit := .split 22 (1,true) (byMove [
.cycle 38 2 false (0),
.cycle 68 2 false (0),
.last 23 (2,true),
.cycle 0 24 true (-1),
.cycle 34 2 false (0),
.cycle 0 24 true (-1),
.cycle 0 23 true (-1),
.last 44 (2,true),
.cycle 0 31 true (-1),
.cycle 40 2 false (0),
.cycle 0 27 true (-1),
.cycle 0 30 true (-1),
.cycle 56 2 false (0),
.last 25 (2,true),
.last 23 (2,true),
.cycle 32 2 false (0),
.cycle 0 25 true (-1),
.last 26 (2,true),
.last 47 (2,true),
.cycle 18 30 true (0),
.cycle 2 21 true (-1),
.cycle 0 34 true (-1),
.cycle 42 2 false (0),
.cycle 0 26 true (-1)
])
theorem kid21_part48_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part48) = true := by rfl

def kid21_part49 : Audit := .split 26 (1,true) (byMove [
.cycle 0 40 true (-1),
.cycle 1 27 true (-1),
.last 27 (2,true),
.cycle 0 28 true (-1),
.cycle 23 12 true (1),
.cycle 1 27 true (-1),
.cycle 0 27 true (-1),
.last 48 (2,true),
.cycle 0 35 true (-1),
.cycle 0 51 true (-1),
.cycle 0 31 true (-1),
.cycle 0 38 true (-1),
.cycle 6 21 true (-1),
.last 29 (2,true),
.last 27 (2,true),
.cycle 23 10 true (1),
.cycle 0 29 true (-1),
.cycle 0 31 true (-1),
.last 47 (2,true),
.cycle 24 22 true (2),
.cycle 2 25 true (-1),
.cycle 0 42 true (-1),
.cycle 1 31 true (-1),
.cycle 0 30 true (-1)
])
theorem kid21_part49_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part49) = true := by rfl

def kid21_part50 : Audit := .cycle 18 1 false (0)
theorem kid21_part50_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part50) = true := by rfl

def kid21_part51 : Audit := .cycle 17 1 false (-1)
theorem kid21_part51_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part51) = true := by rfl

def kid21_part52 : Audit := .cycle 17 2 false (-1)
theorem kid21_part52_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part52) = true := by rfl

def kid21_part53 : Audit := .cycle 17 2 false (-1)
theorem kid21_part53_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part53) = true := by rfl

def kid21_part54 : Audit := .split 18 (1,true) (byMove [
.cycle 20 2 false (2),
.cycle 34 2 false (6),
.last 19 (2,true),
.last 22 (2,true),
.cycle 23 2 false (3),
.last 22 (2,true),
.cycle 0 21 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.cycle 0 29 true (0),
.cycle 0 25 true (0),
.cycle 28 2 false (6),
.last 21 (2,true),
.last 19 (2,true),
.cycle 21 2 false (3),
.cycle 0 25 true (0),
.cycle 21 2 false (3),
.cycle 0 21 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (0),
.cycle 0 25 true (0),
.cycle 0 32 true (0)
])
theorem kid21_part54_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part54) = true := by rfl

def kid21_part55 : Audit := .split 18 (2,true) (byMove [
.cycle 20 2 false (2),
.last 19 (1,true),
.cycle 21 1 false (1),
.cycle 0 24 true (0),
.cycle 23 2 false (3),
.cycle 0 23 true (0),
.last 20 (1,true),
.last 40 (1,true),
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.last 24 (1,true),
.cycle 50 5 true (6),
.cycle 28 2 false (6),
.last 19 (1,true),
.cycle 23 2 false (3),
.cycle 21 2 false (3),
.last 22 (1,true),
.last 20 (1,true),
.last 20 (1,true),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 4 15 true (0),
.last 44 (1,true),
.cycle 0 32 true (0)
])
theorem kid21_part55_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part55) = true := by rfl

def kid21_part56 : Audit := .split 20 (1,true) (byMove [
.cycle 22 2 false (4),
.cycle 32 2 false (6),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 25 2 false (5),
.cycle 23 1 false (5),
.cycle 0 21 true (0),
.last 42 (2,true),
.cycle 0 29 true (0),
.cycle 29 2 false (7),
.cycle 0 25 true (0),
.cycle 0 26 true (0),
.cycle 26 2 false (6),
.last 23 (2,true),
.last 21 (2,true),
.cycle 23 2 false (5),
.cycle 0 23 true (0),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 0 30 true (0),
.cycle 0 31 true (0),
.cycle 0 24 true (0)
])
theorem kid21_part56_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part56) = true := by rfl

def kid21_part57 : Audit := .cycle 17 1 false (1)
theorem kid21_part57_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part57) = true := by rfl

def kid21_part58 : Audit := .cycle 17 2 false (1)
theorem kid21_part58_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part58) = true := by rfl

def kid21_part59 : Audit := .cycle 17 2 false (1)
theorem kid21_part59_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part59) = true := by rfl

def kid21_part60 : Audit := .split 18 (1,true) (byMove [
.cycle 20 2 false (0),
.cycle 38 2 false (6),
.last 19 (2,true),
.last 22 (2,true),
.cycle 23 2 false (1),
.cycle 16 3 false (0),
.cycle 0 23 true (-1),
.last 20 (2,true),
.cycle 0 31 true (-1),
.cycle 0 51 true (-1),
.cycle 0 35 true (-1),
.cycle 14 5 false (2),
.cycle 32 2 false (6),
.last 21 (2,true),
.last 19 (2,true),
.cycle 21 2 false (1),
.cycle 0 29 true (-1),
.cycle 16 3 false (0),
.cycle 17 46 true (-1),
.last 20 (2,true),
.cycle 2 21 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 27, 25, 64],[16, 8, 64, 1, 8, 8, 64],64⟩,
.cycle 34 2 false (6),
.cycle 40 2 false (6)
])
theorem kid21_part60_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part60) = true := by rfl

def kid21_part61 : Audit := .split 18 (2,true) (byMove [
.cycle 20 2 false (0),
.last 19 (1,true),
.cycle 21 1 false (-1),
.cycle 0 28 true (-1),
.cycle 23 2 false (1),
.cycle 16 3 false (0),
.last 20 (1,true),
.last 42 (1,true),
.last 22 (1,true),
.last 26 (1,true),
.last 24 (1,true),
.cycle 14 5 false (2),
.cycle 32 2 false (6),
.last 19 (1,true),
.cycle 23 2 false (1),
.cycle 21 2 false (1),
.last 22 (1,true),
.cycle 16 3 false (0),
.last 20 (1,true),
.last 39 (1,true),
.last 22 (1,true),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 1, 4, 4, 4, 4],[128, 131072, 2097152, 512, 32, 1024, 1073741824, 128, 1912602752, 2097152, 131072, 4194304, 1912602752, 1912733824, 136314880, 512, 131072, 1024, 1073741824, 1912602752, 1024, 134217728, 536870912, 268435456, 1912602752, 1912602752, 2046821504, 134217728, 536870912, 268435456, 1073741824],[1024, 1073741824, 131072, 128, 131072, 128, 1024, 1073741824, 1912602752, 131072, 1912602752, 524288, 1024, 1073741824, 131072, 1912602752, 131072, 128, 1912602752, 1073741824, 128, 131072, 128, 33554432, 1912602752, 1073741824, 1912602752, 1912602752, 1912602752, 33554432, 1073741824],1191981376⟩,
.last 21 (1,true),
.last 27 (1,true)
])
theorem kid21_part61_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part61) = true := by rfl

def kid21_part62 : Audit := .split 20 (1,true) (byMove [
.cycle 22 2 false (2),
.cycle 36 2 false (6),
.last 21 (2,true),
.last 24 (2,true),
.cycle 25 2 false (3),
.last 26 (2,true),
.cycle 0 23 true (-1),
.last 22 (2,true),
.cycle 0 23 true (-1),
.cycle 0 27 true (-1),
.cycle 0 31 true (-1),
.cycle 0 31 true (-1),
.cycle 30 2 false (6),
.last 23 (2,true),
.last 21 (2,true),
.cycle 23 2 false (3),
.cycle 0 27 true (-1),
.cycle 25 2 false (3),
.last 40 (2,true),
.last 22 (2,true),
.cycle 0 23 true (-1),
.cycle 4 17 true (-1),
.last 23 (2,true),
.last 29 (2,true)
])
theorem kid21_part62_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part62) = true := by rfl

def kid21_part63 : Audit := .cycle 17 1 false (-1)
theorem kid21_part63_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part63) = true := by rfl

def kid21_part64 : Audit := .cycle 17 2 false (-1)
theorem kid21_part64_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part64) = true := by rfl

def kid21_part65 : Audit := .cycle 17 2 false (-1)
theorem kid21_part65_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part65) = true := by rfl

def kid21_part66 : Audit := .split 18 (1,true) (byMove [
.last 26 (2,true),
.cycle 31 2 false (3),
.last 19 (2,true),
.last 22 (2,true),
.cycle 13 10 true (0),
.last 22 (2,true),
.cycle 0 21 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.cycle 0 29 true (0),
.cycle 0 25 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 27, 25, 64],[16, 8, 64, 1, 8, 1, 64],64⟩,
.last 22 (2,true),
.last 19 (2,true),
.cycle 13 8 true (0),
.cycle 0 25 true (0),
.cycle 0 33 true (0),
.cycle 0 21 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (0),
.cycle 0 25 true (0),
.cycle 0 32 true (0)
])
theorem kid21_part66_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part66) = true := by rfl

def kid21_part67 : Audit := .split 18 (2,true) (byMove [
.cycle 0 32 true (0),
.last 19 (1,true),
.cycle 22 1 false (0),
.cycle 0 24 true (0),
.cycle 13 10 true (0),
.cycle 0 23 true (0),
.last 20 (1,true),
.last 40 (1,true),
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.last 24 (1,true),
.cycle 1 24 true (0),
.last 37 (1,true),
.last 19 (1,true),
.cycle 32 2 false (6),
.cycle 13 8 true (0),
.last 22 (1,true),
.last 20 (1,true),
.last 20 (1,true),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 4 15 true (0),
.cycle 1 24 true (0),
.cycle 0 32 true (0)
])
theorem kid21_part67_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part67) = true := by rfl

def kid21_part68 : Audit := .split 20 (1,true) (byMove [
.cycle 0 37 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 529, 144, 529, 8192, 16384, 8, 16, 8, 1, 8192, 16384, 8, 16, 8, 1, 262144],[16, 8, 262144, 1, 512, 256, 16, 529, 262144, 1, 32768, 16384, 16, 17049, 262144, 1, 32768, 16384, 262144],262144⟩,
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 7 14 true (0),
.cycle 0 51 true (0),
.cycle 0 21 true (0),
.last 42 (2,true),
.cycle 0 29 true (0),
.cycle 0 47 true (0),
.cycle 0 25 true (0),
.cycle 0 26 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 27, 25, 64],[16, 8, 64, 1, 8, 4, 64],64⟩,
.last 23 (2,true),
.last 21 (2,true),
.cycle 9 12 true (0),
.cycle 0 23 true (0),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 0 30 true (0),
.cycle 2 21 true (0),
.cycle 0 24 true (0)
])
theorem kid21_part68_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part68) = true := by rfl

def kid21_part69 : Audit := .cycle 28 2 false (6)
theorem kid21_part69_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part69) = true := by rfl

def kid21_part70 : Audit := .cycle 15 2 true (0)
theorem kid21_part70_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part70) = true := by rfl

def kid21_part71 : Audit := .cycle 13 8 true (0)
theorem kid21_part71_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part71) = true := by rfl

def kid21_part47 : Audit := .split 16 (5,true) (byMove [(kid21_part48),(kid21_part49),(kid21_part50),(kid21_part51),(kid21_part52),(kid21_part53),(kid21_part54),(kid21_part55),(kid21_part56),(kid21_part57),(kid21_part58),(kid21_part59),(kid21_part60),(kid21_part61),(kid21_part62),(kid21_part63),(kid21_part64),(kid21_part65),(kid21_part66),(kid21_part67),(kid21_part68),(kid21_part69),(kid21_part70),(kid21_part71)])

theorem kid21_part47_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid21_part47) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 16 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid21_part48),(kid21_part49),(kid21_part50),(kid21_part51),(kid21_part52),(kid21_part53),(kid21_part54),(kid21_part55),(kid21_part56),(kid21_part57),(kid21_part58),(kid21_part59),(kid21_part60),(kid21_part61),(kid21_part62),(kid21_part63),(kid21_part64),(kid21_part65),(kid21_part66),(kid21_part67),(kid21_part68),(kid21_part69),(kid21_part70),(kid21_part71)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part48_checked

  · exact kid21_part54_checked

  · exact kid21_part60_checked

  · exact kid21_part66_checked

  · exact kid21_part49_checked

  · exact kid21_part55_checked

  · exact kid21_part61_checked

  · exact kid21_part67_checked

  · exact kid21_part50_checked

  · exact kid21_part56_checked

  · exact kid21_part62_checked

  · exact kid21_part68_checked

  · exact kid21_part51_checked

  · exact kid21_part57_checked

  · exact kid21_part63_checked

  · exact kid21_part69_checked

  · exact kid21_part52_checked

  · exact kid21_part58_checked

  · exact kid21_part64_checked

  · exact kid21_part70_checked

  · exact kid21_part53_checked

  · exact kid21_part59_checked

  · exact kid21_part65_checked

  · exact kid21_part71_checked

def kid21_part73 : Audit := .split 19 (2,true) (byMove [
.cycle 15 7 false (1),
.last 20 (1,true),
.cycle 23 1 false (-1),
.last 22 (1,true),
.cycle 4 31 true (-1),
.cycle 23 1 false (-1),
.cycle 0 23 true (-1),
.last 20 (1,true),
.cycle 0 37 true (-1),
.cycle 35 1 false (-1),
.cycle 45 1 false (-1),
.cycle 58 1 false (-2),
.cycle 5 17 true (-1),
.last 20 (1,true),
.cycle 5 21 true (-2),
.cycle 5 27 true (-1),
.cycle 0 25 true (-1),
.cycle 23 1 false (-1),
.cycle 0 23 true (-1),
.last 20 (1,true),
.last 52 (1,true),
.cycle 5 38 true (-2),
.cycle 33 1 false (-1),
.cycle 27 1 false (-1)
])
theorem kid21_part73_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part73) = true := by rfl

def kid21_part74 : Audit := .cycle 0 23 true (-1)
theorem kid21_part74_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part74) = true := by rfl

def kid21_part75 : Audit := .cycle 18 1 false (0)
theorem kid21_part75_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part75) = true := by rfl

def kid21_part76 : Audit := .cycle 17 1 false (-1)
theorem kid21_part76_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part76) = true := by rfl

def kid21_part77 : Audit := .cycle 18 1 false (-2)
theorem kid21_part77_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part77) = true := by rfl

def kid21_part78 : Audit := .cycle 17 1 false (-1)
theorem kid21_part78_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part78) = true := by rfl

def kid21_part79 : Audit := .cycle 31 1 false (5)
theorem kid21_part79_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part79) = true := by rfl

def kid21_part80 : Audit := .split 17 (1,true) (byMove [
.last 20 (2,true),
.cycle 0 40 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 21 true (0),
.cycle 32 1 false (8),
.last 18 (2,true),
.cycle 25 1 false (5),
.cycle 31 1 false (5),
.cycle 32 1 false (8),
.cycle 5 17 true (0),
.last 19 (2,true),
.cycle 0 23 true (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 18 (2,true),
.cycle 5 13 true (0),
.cycle 19 9 true (2),
.cycle 41 3 true (7)
])
theorem kid21_part80_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part80) = true := by rfl

def kid21_part81 : Audit := .split 17 (2,true) (byMove [
.cycle 0 49 true (0),
.cycle 0 40 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 21 true (0),
.last 18 (1,true),
.cycle 22 1 false (6),
.cycle 25 1 false (5),
.cycle 31 1 false (5),
.cycle 22 1 false (6),
.last 19 (1,true),
.last 20 (1,true),
.cycle 0 23 true (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 21 true (0),
.last 18 (1,true),
.cycle 2 19 true (0),
.cycle 5 13 true (0),
.cycle 19 9 true (2),
.cycle 0 29 true (0)
])
theorem kid21_part81_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part81) = true := by rfl

def kid21_part82 : Audit := .cycle 0 21 true (0)
theorem kid21_part82_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part82) = true := by rfl

def kid21_part83 : Audit := .cycle 5 13 true (0)
theorem kid21_part83_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part83) = true := by rfl

def kid21_part84 : Audit := .cycle 21 1 false (5)
theorem kid21_part84_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part84) = true := by rfl

def kid21_part85 : Audit := .split 18 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 5 58 true (-2),
.last 19 (2,true),
.cycle 0 32 true (-1),
.cycle 5 19 true (-1),
.cycle 16 3 false (0),
.cycle 6 23 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 31, 27, 64],[16, 2, 64, 1, 8, 10, 64],64⟩,
.last 19 (2,true),
.cycle 0 23 true (-1),
.cycle 5 15 true (-1),
.cycle 22 19 true (1),
.cycle 0 25 true (-1),
.last 21 (2,true),
.last 19 (2,true),
.cycle 5 17 true (-1),
.cycle 5 27 true (-1),
.cycle 16 3 false (0),
.cycle 5 36 true (-1),
.cycle 0 45 true (-1),
.last 19 (2,true),
.cycle 0 23 true (-1),
.cycle 0 38 true (-1),
.cycle 5 17 true (-1)
])
theorem kid21_part85_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part85) = true := by rfl

def kid21_part86 : Audit := .split 18 (2,true) (byMove [
.cycle 21 1 false (-1),
.last 19 (1,true),
.cycle 21 1 false (-1),
.last 21 (1,true),
.cycle 5 19 true (-1),
.cycle 16 3 false (0),
.cycle 6 23 true (-1),
.last 19 (1,true),
.cycle 5 51 true (-1),
.cycle 0 23 true (-1),
.cycle 5 15 true (-1),
.last 34 (1,true),
.cycle 0 25 true (-1),
.last 19 (1,true),
.cycle 5 19 true (-2),
.cycle 5 17 true (-1),
.cycle 5 27 true (-1),
.cycle 16 3 false (0),
.last 39 (1,true),
.last 19 (1,true),
.last 38 (1,true),
.cycle 0 23 true (-1),
.last 32 (1,true),
.last 20 (1,true)
])
theorem kid21_part86_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part86) = true := by rfl

def kid21_part87 : Audit := .cycle 35 1 false (5)
theorem kid21_part87_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part87) = true := by rfl

def kid21_part88 : Audit := .cycle 17 1 false (-1)
theorem kid21_part88_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part88) = true := by rfl

def kid21_part89 : Audit := .cycle 18 1 false (-2)
theorem kid21_part89_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part89) = true := by rfl

def kid21_part90 : Audit := .cycle 17 1 false (-1)
theorem kid21_part90_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part90) = true := by rfl

def kid21_part91 : Audit := .cycle 0 38 true (0)
theorem kid21_part91_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part91) = true := by rfl

def kid21_part92 : Audit := .split 17 (1,true) (byMove [
.cycle 20 1 false (0),
.cycle 5 21 true (-1),
.last 18 (2,true),
.cycle 0 28 true (0),
.cycle 39 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 4, 2, 64],[16, 2, 64, 1, 8, 2, 64],64⟩,
.last 18 (2,true),
.cycle 0 36 true (0),
.cycle 0 38 true (0),
.cycle 1 20 true (0),
.cycle 5 15 true (0),
.last 20 (2,true),
.last 18 (2,true),
.cycle 35 1 false (5),
.cycle 0 23 true (0),
.cycle 16 2 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 18 (2,true),
.cycle 5 13 true (0),
.cycle 19 9 true (2),
.cycle 1 20 true (0)
])
theorem kid21_part92_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part92) = true := by rfl

def kid21_part93 : Audit := .split 17 (2,true) (byMove [
.cycle 20 1 false (0),
.last 18 (1,true),
.cycle 20 1 false (0),
.last 20 (1,true),
.cycle 39 1 false (5),
.cycle 0 40 true (0),
.cycle 0 21 true (0),
.last 18 (1,true),
.cycle 0 35 true (0),
.cycle 0 36 true (0),
.cycle 0 38 true (0),
.cycle 18 26 true (2),
.cycle 5 15 true (0),
.last 18 (1,true),
.cycle 39 1 false (5),
.cycle 35 1 false (5),
.cycle 0 23 true (0),
.cycle 16 2 true (0),
.cycle 0 21 true (0),
.last 18 (1,true),
.cycle 2 19 true (0),
.cycle 5 13 true (0),
.cycle 19 9 true (2),
.cycle 2 19 true (0)
])
theorem kid21_part93_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part93) = true := by rfl

def kid21_part94 : Audit := .cycle 0 21 true (0)
theorem kid21_part94_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part94) = true := by rfl

def kid21_part95 : Audit := .cycle 5 13 true (0)
theorem kid21_part95_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part95) = true := by rfl

def kid21_part96 : Audit := .cycle 19 3 true (3)
theorem kid21_part96_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part96) = true := by rfl

def kid21_part72 : Audit := .split 16 (5,true) (byMove [(kid21_part73),(kid21_part74),(kid21_part75),(kid21_part76),(kid21_part77),(kid21_part78),(kid21_part79),(kid21_part80),(kid21_part81),(kid21_part82),(kid21_part83),(kid21_part84),(kid21_part85),(kid21_part86),(kid21_part87),(kid21_part88),(kid21_part89),(kid21_part90),(kid21_part91),(kid21_part92),(kid21_part93),(kid21_part94),(kid21_part95),(kid21_part96)])

theorem kid21_part72_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid21_part72) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 16 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part73),(kid21_part74),(kid21_part75),(kid21_part76),(kid21_part77),(kid21_part78),(kid21_part79),(kid21_part80),(kid21_part81),(kid21_part82),(kid21_part83),(kid21_part84),(kid21_part85),(kid21_part86),(kid21_part87),(kid21_part88),(kid21_part89),(kid21_part90),(kid21_part91),(kid21_part92),(kid21_part93),(kid21_part94),(kid21_part95),(kid21_part96)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part73_checked

  · exact kid21_part79_checked

  · exact kid21_part85_checked

  · exact kid21_part91_checked

  · exact kid21_part74_checked

  · exact kid21_part80_checked

  · exact kid21_part86_checked

  · exact kid21_part92_checked

  · exact kid21_part75_checked

  · exact kid21_part81_checked

  · exact kid21_part87_checked

  · exact kid21_part93_checked

  · exact kid21_part76_checked

  · exact kid21_part82_checked

  · exact kid21_part88_checked

  · exact kid21_part94_checked

  · exact kid21_part77_checked

  · exact kid21_part83_checked

  · exact kid21_part89_checked

  · exact kid21_part95_checked

  · exact kid21_part78_checked

  · exact kid21_part84_checked

  · exact kid21_part90_checked

  · exact kid21_part96_checked

def kid21_part97 : Audit := .cycle 0 13 true (0)
theorem kid21_part97_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid21_part97) = true := by rfl

def kid21_part98 : Audit := .cycle 1 12 true (1)
theorem kid21_part98_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid21_part98) = true := by rfl

def kid21_part99 : Audit := .cycle 2 11 true (1)
theorem kid21_part99_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid21_part99) = true := by rfl

def kid21_part100 : Audit := .cycle 8 5 true (3)
theorem kid21_part100_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid21_part100) = true := by rfl

def kid21_part101 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 19 4 false (1),
.cycle 24 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 12 3 true (4),
.split 16 (1,true) (byMove [
.cycle 40 7 false (3),
.cycle 1 17 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 32 3 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 6 15 true (2),
.cycle 12 5 true (3),
.cycle 6 11 true (2),
.last 19 (2,true),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 5 21 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 13 true (2),
.cycle 6 14 true (2)
]),
.split 16 (2,true) (byMove [
.last 36 (1,true),
.last 17 (1,true),
.cycle 0 26 true (0),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 24 (1,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.last 21 (1,true),
.cycle 12 5 true (3),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 9 10 true (2),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 24 (1,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 19 (1,true),
.last 20 (1,true)
]),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 19 4 false (1),
.cycle 7 9 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 13 2 true (4),
.cycle 12 3 true (4)
])
theorem kid21_part101_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid21_part101) = true := by rfl

def kid21_part102 : Audit := .cycle 12 1 true (4)
theorem kid21_part102_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid21_part102) = true := by rfl

def kid21_part6 : Audit := .split 12 (5,false) (byMove [(kid21_part7),(kid21_part8),(kid21_part9),(kid21_part10),(kid21_part11),(kid21_part12),(kid21_part13),(kid21_part14),(kid21_part15),(kid21_part16),(kid21_part17),(kid21_part18),(kid21_part19),(kid21_part20),(kid21_part45),(kid21_part46),(kid21_part47),(kid21_part72),(kid21_part97),(kid21_part98),(kid21_part99),(kid21_part100),(kid21_part101),(kid21_part102)])

theorem kid21_part6_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (kid21_part6) = true := by

  change (zipQueryOK 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid21_part7),(kid21_part8),(kid21_part9),(kid21_part10),(kid21_part11),(kid21_part12),(kid21_part13),(kid21_part14),(kid21_part15),(kid21_part16),(kid21_part17),(kid21_part18),(kid21_part19),(kid21_part20),(kid21_part45),(kid21_part46),(kid21_part47),(kid21_part72),(kid21_part97),(kid21_part98),(kid21_part99),(kid21_part100),(kid21_part101),(kid21_part102)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part7_checked

  · exact kid21_part13_checked

  · exact kid21_part19_checked

  · exact kid21_part97_checked

  · exact kid21_part8_checked

  · exact kid21_part14_checked

  · exact kid21_part20_checked

  · exact kid21_part98_checked

  · exact kid21_part9_checked

  · exact kid21_part15_checked

  · exact kid21_part45_checked

  · exact kid21_part99_checked

  · exact kid21_part10_checked

  · exact kid21_part16_checked

  · exact kid21_part46_checked

  · exact kid21_part100_checked

  · exact kid21_part11_checked

  · exact kid21_part17_checked

  · exact kid21_part47_checked

  · exact kid21_part101_checked

  · exact kid21_part12_checked

  · exact kid21_part18_checked

  · exact kid21_part72_checked

  · exact kid21_part102_checked

def kid21_part103 : Audit := .cycle 0 12 true (0)
theorem kid21_part103_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,0⟩)) (kid21_part103) = true := by rfl

def kid21_part104 : Audit := .cycle 1 11 true (1)
theorem kid21_part104_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,1⟩)) (kid21_part104) = true := by rfl

def kid21_part105 : Audit := .cycle 5 33 true (0)
theorem kid21_part105_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,2⟩)) (kid21_part105) = true := by rfl

def kid21_part106 : Audit := .cycle 0 25 true (0)
theorem kid21_part106_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,3⟩)) (kid21_part106) = true := by rfl

def kid21_part107 : Audit := .cycle 11 1 true (5)
theorem kid21_part107_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,4⟩)) (kid21_part107) = true := by rfl

def kid21_part109 : Audit := .cycle 0 13 true (0)
theorem kid21_part109_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid21_part109) = true := by rfl

def kid21_part110 : Audit := .cycle 1 12 true (1)
theorem kid21_part110_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid21_part110) = true := by rfl

def kid21_part111 : Audit := .cycle 0 27 true (0)
theorem kid21_part111_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid21_part111) = true := by rfl

def kid21_part112 : Audit := .cycle 5 16 true (0)
theorem kid21_part112_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid21_part112) = true := by rfl

def kid21_part113 : Audit := .cycle 11 2 true (5)
theorem kid21_part113_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid21_part113) = true := by rfl

def kid21_part114 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 false (6),
.cycle 30 1 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 19 true (0),
.cycle 30 1 false (6),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.split 20 (1,true) (byMove [
.cycle 23 1 false (1),
.cycle 33 1 false (3),
.last 21 (2,true),
.cycle 0 22 true (-1),
.cycle 26 1 false (2),
.cycle 18 3 false (0),
.cycle 0 21 true (-1),
.cycle 12 21 false (6),
.cycle 0 29 true (-1),
.cycle 30 1 false (4),
.cycle 15 7 false (3),
.cycle 16 5 false (2),
.cycle 27 1 false (3),
.last 23 (2,true),
.last 21 (2,true),
.cycle 24 1 false (2),
.cycle 0 23 true (-1),
.cycle 18 3 false (0),
.cycle 13 33 false (7),
.cycle 45 1 false (3),
.cycle 2 19 false (6),
.cycle 14 11 false (4),
.cycle 31 1 false (3),
.cycle 29 1 false (3)
]),
.split 20 (2,true) (byMove [
.cycle 23 1 false (1),
.last 21 (1,true),
.cycle 23 1 false (-1),
.cycle 0 22 true (-1),
.cycle 26 1 false (2),
.cycle 18 3 false (0),
.cycle 0 21 true (-1),
.cycle 12 21 false (6),
.cycle 0 29 true (-1),
.cycle 30 1 false (4),
.cycle 15 7 false (3),
.cycle 16 5 false (2),
.cycle 27 1 false (3),
.last 21 (1,true),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 0 23 true (-1),
.cycle 18 3 false (0),
.last 40 (1,true),
.last 39 (1,true),
.cycle 2 19 false (6),
.cycle 14 11 false (4),
.last 25 (1,true),
.last 23 (1,true)
]),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.cycle 18 2 true (-1),
.cycle 19 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 29 1 false (5),
.cycle 23 1 false (3),
.cycle 16 4 true (0),
.cycle 17 2 true (0)
])
theorem kid21_part114_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid21_part114) = true := by rfl

def kid21_part115 : Audit := .cycle 0 13 true (0)
theorem kid21_part115_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid21_part115) = true := by rfl

def kid21_part116 : Audit := .cycle 1 12 true (1)
theorem kid21_part116_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid21_part116) = true := by rfl

def kid21_part117 : Audit := .cycle 5 23 true (0)
theorem kid21_part117_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid21_part117) = true := by rfl

def kid21_part118 : Audit := .cycle 5 33 true (0)
theorem kid21_part118_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid21_part118) = true := by rfl

def kid21_part119 : Audit := .cycle 11 2 true (5)
theorem kid21_part119_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid21_part119) = true := by rfl

def kid21_part120 : Audit := .cycle 12 1 true (6)
theorem kid21_part120_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid21_part120) = true := by rfl

def kid21_part121 : Audit := .split 14 (1,true) (byMove [
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 40 5 false (3),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (5),
.cycle 12 4 true (5),
.cycle 35 3 false (4),
.cycle 5 22 true (0),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 17 (5,true),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 11 5 true (5),
.cycle 6 11 true (2)
]),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 40 5 false (3),
.cycle 24 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (5),
.cycle 12 4 true (5),
.cycle 35 3 false (4),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 15 2 true (4),
.cycle 24 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 11 5 true (5),
.cycle 6 11 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.cycle 6 9 true (2),
.split 17 (2,true) (byMove [
.last 20 (5,true),
.cycle 28 3 false (0),
.last 30 (5,true),
.cycle 13 6 true (4),
.cycle 4 15 true (1),
.last 18 (5,true),
.cycle 10 8 true (4),
.cycle 1 20 true (1),
.cycle 9 18 true (3),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.last 18 (5,true),
.cycle 0 21 true (0),
.cycle 28 3 false (0),
.cycle 5 15 true (1),
.cycle 5 13 true (1),
.cycle 9 10 true (3),
.last 18 (5,true),
.cycle 10 8 true (4),
.cycle 34 5 false (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.last 18 (5,true)
]),
.split 15 (2,true) (byMove [
.cycle 10 9 true (4),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.last 26 (5,true),
.cycle 0 45 true (0),
.last 24 (5,true),
.cycle 10 6 true (4),
.cycle 0 19 true (0),
.cycle 5 27 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 5 43 true (0),
.cycle 5 15 true (1),
.cycle 9 8 true (3),
.cycle 0 27 true (0),
.last 17 (5,true),
.last 24 (5,true),
.cycle 10 6 true (4),
.cycle 14 2 true (5),
.cycle 2 15 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.cycle 0 34 true (0),
.cycle 0 45 true (0),
.cycle 24 4 false (0),
.cycle 10 6 true (4),
.cycle 5 59 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 12 5 true (5),
.cycle 5 43 true (0),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 27 true (0),
.cycle 15 2 true (4),
.cycle 24 4 false (0),
.cycle 10 6 true (4),
.cycle 14 2 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 6 12 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 6 10 true (2)
])
theorem kid21_part121_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid21_part121) = true := by rfl

def kid21_part122 : Audit := .split 14 (2,true) (byMove [
.cycle 10 5 true (4),
.split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 40 5 false (3),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (5),
.cycle 12 4 true (5),
.cycle 6 12 true (2),
.cycle 28 3 false (0),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 17 (5,true),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 11 5 true (5),
.last 18 (5,true)
]),
.cycle 5 20 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 40 5 false (3),
.cycle 24 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (5),
.cycle 12 4 true (5),
.last 17 (1,true),
.last 28 (1,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 15 2 true (4),
.cycle 24 4 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 11 5 true (5),
.last 17 (1,true)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.cycle 6 9 true (2),
.split 15 (1,true) (byMove [
.last 22 (5,true),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.last 26 (5,true),
.cycle 0 45 true (0),
.last 24 (5,true),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 13 4 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 21 true (0),
.cycle 28 3 false (0),
.cycle 9 8 true (3),
.cycle 0 27 true (0),
.last 17 (5,true),
.last 24 (5,true),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 14 2 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.cycle 9 8 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.split 15 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.cycle 0 34 true (0),
.cycle 0 45 true (0),
.cycle 24 4 false (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.last 38 (1,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 12 5 true (5),
.last 17 (1,true),
.last 28 (1,true),
.cycle 9 8 true (3),
.cycle 0 27 true (0),
.cycle 15 2 true (4),
.cycle 24 4 false (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 14 2 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 18 (1,true)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.split 16 (1,true) (byMove [
.last 19 (5,true),
.cycle 0 26 true (0),
.cycle 5 45 true (0),
.cycle 0 21 true (0),
.cycle 4 14 true (1),
.last 17 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 14 3 true (6),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 20 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.last 17 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 14 3 true (6),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
])
])
theorem kid21_part122_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid21_part122) = true := by rfl

def kid21_part123 : Audit := .cycle 0 15 true (0)
theorem kid21_part123_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid21_part123) = true := by rfl

def kid21_part124 : Audit := .cycle 0 25 true (0)
theorem kid21_part124_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid21_part124) = true := by rfl

def kid21_part125 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.cycle 0 30 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.cycle 12 3 true (5),
.split 16 (1,true) (byMove [
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 38 3 false (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (5),
.cycle 12 5 true (5),
.cycle 6 11 true (2),
.last 19 (2,true),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 5 47 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 11 6 true (5),
.cycle 0 20 true (0)
]),
.split 16 (2,true) (byMove [
.cycle 10 7 true (4),
.last 17 (1,true),
.cycle 5 22 true (0),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 30 (1,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (5),
.cycle 12 5 true (5),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 9 10 true (3),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 30 (1,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 11 6 true (5),
.cycle 0 20 true (0)
]),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.cycle 13 2 true (5),
.cycle 5 27 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 0 18 true (0)
])
theorem kid21_part125_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid21_part125) = true := by rfl

def kid21_part127 : Audit := .split 21 (2,true) (byMove [
.cycle 0 37 true (-1),
.last 22 (1,true),
.cycle 25 1 false (-1),
.last 24 (1,true),
.cycle 0 31 true (-1),
.cycle 25 1 false (1),
.cycle 5 19 true (-1),
.last 22 (1,true),
.cycle 5 37 true (-1),
.cycle 18 35 true (-1),
.cycle 0 27 true (-1),
.cycle 60 9 true (9),
.cycle 5 35 true (-1),
.last 22 (1,true),
.cycle 5 43 true (-2),
.cycle 0 29 true (-1),
.cycle 5 21 true (-1),
.cycle 0 61 true (-1),
.cycle 5 19 true (-1),
.last 22 (1,true),
.cycle 22 27 true (2),
.cycle 0 60 true (-1),
.cycle 0 27 true (-1),
.cycle 0 33 true (-1)
])
theorem kid21_part127_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part127) = true := by rfl

def kid21_part128 : Audit := .cycle 5 19 true (-1)
theorem kid21_part128_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part128) = true := by rfl

def kid21_part129 : Audit := .cycle 20 1 false (0)
theorem kid21_part129_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part129) = true := by rfl

def kid21_part130 : Audit := .cycle 19 1 false (-1)
theorem kid21_part130_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part130) = true := by rfl

def kid21_part131 : Audit := .cycle 20 1 false (0)
theorem kid21_part131_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part131) = true := by rfl

def kid21_part132 : Audit := .cycle 19 1 false (-1)
theorem kid21_part132_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part132) = true := by rfl

def kid21_part133 : Audit := .cycle 0 25 true (0)
theorem kid21_part133_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part133) = true := by rfl

def kid21_part134 : Audit := .split 19 (1,true) (byMove [
.last 22 (2,true),
.cycle 5 52 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 5 17 true (0),
.cycle 36 1 false (12),
.last 20 (2,true),
.cycle 39 1 false (11),
.cycle 0 25 true (0),
.cycle 36 1 false (12),
.cycle 5 35 true (0),
.last 21 (2,true),
.cycle 5 19 true (0),
.cycle 20 1 false (0),
.cycle 48 1 false (12),
.cycle 20 1 false (0),
.cycle 5 17 true (0),
.cycle 1 24 true (0),
.last 20 (2,true),
.cycle 5 27 true (0),
.cycle 0 25 true (0),
.cycle 49 3 true (11)
])
theorem kid21_part134_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part134) = true := by rfl

def kid21_part135 : Audit := .split 19 (2,true) (byMove [
.cycle 5 37 true (0),
.cycle 5 52 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 5 17 true (0),
.last 20 (1,true),
.cycle 26 1 false (8),
.cycle 39 1 false (11),
.cycle 0 25 true (0),
.cycle 26 1 false (8),
.last 21 (1,true),
.last 22 (1,true),
.cycle 5 19 true (0),
.cycle 20 1 false (0),
.cycle 38 1 false (8),
.cycle 20 1 false (0),
.cycle 5 17 true (0),
.last 20 (1,true),
.cycle 2 23 true (0),
.cycle 5 27 true (0),
.cycle 0 25 true (0),
.cycle 0 33 true (0)
])
theorem kid21_part135_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part135) = true := by rfl

def kid21_part136 : Audit := .cycle 5 17 true (0)
theorem kid21_part136_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part136) = true := by rfl

def kid21_part137 : Audit := .cycle 5 27 true (0)
theorem kid21_part137_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part137) = true := by rfl

def kid21_part138 : Audit := .cycle 25 1 false (7)
theorem kid21_part138_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part138) = true := by rfl

def kid21_part139 : Audit := .split 20 (1,true) (byMove [
.cycle 53 1 false (7),
.cycle 5 27 true (-2),
.last 21 (2,true),
.cycle 0 40 true (-1),
.cycle 5 39 true (-1),
.cycle 18 3 false (0),
.cycle 0 27 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 32, 27, 64],[16, 2, 64, 1, 8, 10, 64],64⟩,
.last 21 (2,true),
.cycle 5 19 true (-1),
.cycle 5 31 true (-1),
.cycle 24 27 true (1),
.cycle 5 21 true (-1),
.last 23 (2,true),
.last 21 (2,true),
.cycle 5 35 true (-1),
.cycle 0 29 true (-1),
.cycle 18 3 false (0),
.cycle 0 27 true (-1),
.cycle 5 45 true (-1),
.last 21 (2,true),
.cycle 5 19 true (-1),
.cycle 5 50 true (-1),
.cycle 5 35 true (-1)
])
theorem kid21_part139_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part139) = true := by rfl

def kid21_part140 : Audit := .split 20 (2,true) (byMove [
.cycle 53 1 false (7),
.last 21 (1,true),
.cycle 23 1 false (-1),
.last 23 (1,true),
.cycle 5 39 true (-1),
.cycle 18 3 false (0),
.cycle 0 27 true (-1),
.last 21 (1,true),
.cycle 0 47 true (-1),
.cycle 5 19 true (-1),
.cycle 5 31 true (-1),
.last 42 (1,true),
.cycle 5 21 true (-1),
.last 21 (1,true),
.cycle 5 39 true (-2),
.cycle 5 35 true (-1),
.cycle 0 29 true (-1),
.cycle 18 3 false (0),
.cycle 0 27 true (-1),
.last 21 (1,true),
.last 44 (1,true),
.cycle 5 19 true (-1),
.last 50 (1,true),
.last 22 (1,true)
])
theorem kid21_part140_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part140) = true := by rfl

def kid21_part141 : Audit := .cycle 0 27 true (-1)
theorem kid21_part141_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part141) = true := by rfl

def kid21_part142 : Audit := .cycle 19 1 false (-1)
theorem kid21_part142_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part142) = true := by rfl

def kid21_part143 : Audit := .cycle 18 2 true (-1)
theorem kid21_part143_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part143) = true := by rfl

def kid21_part144 : Audit := .cycle 19 1 false (-1)
theorem kid21_part144_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part144) = true := by rfl

def kid21_part145 : Audit := .cycle 0 25 true (0)
theorem kid21_part145_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part145) = true := by rfl

def kid21_part146 : Audit := .split 19 (1,true) (byMove [
.cycle 1 30 true (0),
.cycle 5 43 true (-1),
.last 20 (2,true),
.cycle 0 36 true (0),
.cycle 0 29 true (0),
.last 22 (2,true),
.cycle 5 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 32, 2, 64],[16, 2, 64, 1, 8, 2, 64],64⟩,
.last 20 (2,true),
.cycle 5 46 true (0),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 5 31 true (0),
.last 22 (2,true),
.last 20 (2,true),
.cycle 0 27 true (0),
.cycle 5 19 true (0),
.cycle 18 2 true (0),
.cycle 5 17 true (0),
.cycle 1 24 true (0),
.last 20 (2,true),
.cycle 5 27 true (0),
.cycle 0 25 true (0),
.cycle 1 24 true (0)
])
theorem kid21_part146_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part146) = true := by rfl

def kid21_part147 : Audit := .split 19 (2,true) (byMove [
.cycle 41 1 false (11),
.last 20 (1,true),
.cycle 22 1 false (0),
.last 22 (1,true),
.cycle 0 29 true (0),
.cycle 5 52 true (0),
.cycle 5 17 true (0),
.last 20 (1,true),
.cycle 5 35 true (0),
.cycle 5 46 true (0),
.cycle 0 25 true (0),
.cycle 22 30 true (4),
.cycle 5 31 true (0),
.last 20 (1,true),
.cycle 0 29 true (-1),
.cycle 0 27 true (0),
.cycle 5 19 true (0),
.cycle 18 2 true (0),
.cycle 5 17 true (0),
.last 20 (1,true),
.cycle 2 23 true (0),
.cycle 5 27 true (0),
.cycle 0 25 true (0),
.cycle 2 23 true (0)
])
theorem kid21_part147_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part147) = true := by rfl

def kid21_part148 : Audit := .cycle 5 17 true (0)
theorem kid21_part148_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part148) = true := by rfl

def kid21_part149 : Audit := .cycle 5 27 true (0)
theorem kid21_part149_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part149) = true := by rfl

def kid21_part150 : Audit := .cycle 23 3 true (5)
theorem kid21_part150_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part150) = true := by rfl

def kid21_part126 : Audit := .split 18 (5,true) (byMove [(kid21_part127),(kid21_part128),(kid21_part129),(kid21_part130),(kid21_part131),(kid21_part132),(kid21_part133),(kid21_part134),(kid21_part135),(kid21_part136),(kid21_part137),(kid21_part138),(kid21_part139),(kid21_part140),(kid21_part141),(kid21_part142),(kid21_part143),(kid21_part144),(kid21_part145),(kid21_part146),(kid21_part147),(kid21_part148),(kid21_part149),(kid21_part150)])

theorem kid21_part126_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid21_part126) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part127),(kid21_part128),(kid21_part129),(kid21_part130),(kid21_part131),(kid21_part132),(kid21_part133),(kid21_part134),(kid21_part135),(kid21_part136),(kid21_part137),(kid21_part138),(kid21_part139),(kid21_part140),(kid21_part141),(kid21_part142),(kid21_part143),(kid21_part144),(kid21_part145),(kid21_part146),(kid21_part147),(kid21_part148),(kid21_part149),(kid21_part150)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part127_checked

  · exact kid21_part133_checked

  · exact kid21_part139_checked

  · exact kid21_part145_checked

  · exact kid21_part128_checked

  · exact kid21_part134_checked

  · exact kid21_part140_checked

  · exact kid21_part146_checked

  · exact kid21_part129_checked

  · exact kid21_part135_checked

  · exact kid21_part141_checked

  · exact kid21_part147_checked

  · exact kid21_part130_checked

  · exact kid21_part136_checked

  · exact kid21_part142_checked

  · exact kid21_part148_checked

  · exact kid21_part131_checked

  · exact kid21_part137_checked

  · exact kid21_part143_checked

  · exact kid21_part149_checked

  · exact kid21_part132_checked

  · exact kid21_part138_checked

  · exact kid21_part144_checked

  · exact kid21_part150_checked

def kid21_part151 : Audit := .cycle 0 13 true (0)
theorem kid21_part151_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid21_part151) = true := by rfl

def kid21_part152 : Audit := .cycle 1 12 true (1)
theorem kid21_part152_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid21_part152) = true := by rfl

def kid21_part153 : Audit := .cycle 2 11 true (1)
theorem kid21_part153_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid21_part153) = true := by rfl

def kid21_part154 : Audit := .cycle 8 5 true (3)
theorem kid21_part154_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid21_part154) = true := by rfl

def kid21_part155 : Audit := .cycle 11 2 true (5)
theorem kid21_part155_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid21_part155) = true := by rfl

def kid21_part156 : Audit := .cycle 12 1 true (6)
theorem kid21_part156_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid21_part156) = true := by rfl

def kid21_part108 : Audit := .split 12 (5,false) (byMove [(kid21_part109),(kid21_part110),(kid21_part111),(kid21_part112),(kid21_part113),(kid21_part114),(kid21_part115),(kid21_part116),(kid21_part117),(kid21_part118),(kid21_part119),(kid21_part120),(kid21_part121),(kid21_part122),(kid21_part123),(kid21_part124),(kid21_part125),(kid21_part126),(kid21_part151),(kid21_part152),(kid21_part153),(kid21_part154),(kid21_part155),(kid21_part156)])

theorem kid21_part108_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (kid21_part108) = true := by

  change (zipQueryOK 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid21_part109),(kid21_part110),(kid21_part111),(kid21_part112),(kid21_part113),(kid21_part114),(kid21_part115),(kid21_part116),(kid21_part117),(kid21_part118),(kid21_part119),(kid21_part120),(kid21_part121),(kid21_part122),(kid21_part123),(kid21_part124),(kid21_part125),(kid21_part126),(kid21_part151),(kid21_part152),(kid21_part153),(kid21_part154),(kid21_part155),(kid21_part156)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part109_checked

  · exact kid21_part115_checked

  · exact kid21_part121_checked

  · exact kid21_part151_checked

  · exact kid21_part110_checked

  · exact kid21_part116_checked

  · exact kid21_part122_checked

  · exact kid21_part152_checked

  · exact kid21_part111_checked

  · exact kid21_part117_checked

  · exact kid21_part123_checked

  · exact kid21_part153_checked

  · exact kid21_part112_checked

  · exact kid21_part118_checked

  · exact kid21_part124_checked

  · exact kid21_part154_checked

  · exact kid21_part113_checked

  · exact kid21_part119_checked

  · exact kid21_part125_checked

  · exact kid21_part155_checked

  · exact kid21_part114_checked

  · exact kid21_part120_checked

  · exact kid21_part126_checked

  · exact kid21_part156_checked

def kid21_part158 : Audit := .cycle 10 4 true (4)
theorem kid21_part158_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid21_part158) = true := by rfl

def kid21_part159 : Audit := .cycle 1 14 true (1)
theorem kid21_part159_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid21_part159) = true := by rfl

def kid21_part160 : Audit := .split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 25 4 false (3),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.last 30 (5,true),
.cycle 15 1 true (3),
.cycle 26 4 false (3),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 15 1 true (3)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 37 5 false (3),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 12 4 true (4),
.cycle 14 3 true (4),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 38 true (0),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 15 1 true (5)
]),
.cycle 30 3 false (3),
.cycle 39 1 false (1),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 0 30 true (0),
.split 15 (5,false) (byMove [
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 33 1 false (1),
.cycle 33 1 false (3),
.last 20 (5,true),
.last 18 (5,true),
.cycle 10 6 true (3),
.cycle 49 1 false (5),
.cycle 14 2 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 30 true (0),
.last 18 (5,true),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.last 20 (5,true),
.last 18 (5,true),
.last 21 (5,true),
.last 24 (5,true),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 6 10 true (2),
.split 15 (5,false) (byMove [
.cycle 10 6 true (4),
.cycle 49 1 false (5),
.cycle 14 2 true (4),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 6 10 true (2),
.cycle 5 20 true (0),
.last 17 (5,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 15 1 true (5)
])
])
theorem kid21_part160_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid21_part160) = true := by rfl

def kid21_part161 : Audit := .cycle 0 15 true (0)
theorem kid21_part161_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid21_part161) = true := by rfl

def kid21_part162 : Audit := .cycle 7 7 true (3)
theorem kid21_part162_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid21_part162) = true := by rfl

def kid21_part163 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 25 4 false (3),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 30 5 false (0),
.cycle 15 1 true (3),
.cycle 26 4 false (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 15 1 true (3)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 37 5 false (3),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 12 4 true (4),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 38 true (0),
.cycle 26 1 false (6),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 15 1 true (5)
]),
.cycle 30 3 false (3),
.split 16 (2,true) (byMove [
.last 37 (5,false),
.last 18 (5,false),
.cycle 0 26 true (0),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 25 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.last 22 (5,false),
.last 17 (5,false),
.cycle 6 11 true (2),
.last 18 (5,false),
.cycle 9 10 true (2),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 25 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 12 true (2),
.last 17 (5,false)
]),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 0 30 true (0),
.split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.last 30 (2,true),
.cycle 33 1 false (3),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 10 6 true (3),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 14 2 true (3),
.cycle 0 30 true (0),
.last 17 (2,true),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 6 17 true (2),
.cycle 24 3 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 23 3 false (1)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 6 10 true (2),
.split 15 (5,false) (byMove [
.cycle 10 6 true (4),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 14 2 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 6 10 true (2),
.last 19 (2,true),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 14 3 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 15 1 true (5)
])
])
theorem kid21_part163_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid21_part163) = true := by rfl

def kid21_part164 : Audit := .cycle 0 14 true (0)
theorem kid21_part164_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid21_part164) = true := by rfl

def kid21_part165 : Audit := .cycle 1 13 true (1)
theorem kid21_part165_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid21_part165) = true := by rfl

def kid21_part166 : Audit := .cycle 0 22 true (0)
theorem kid21_part166_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid21_part166) = true := by rfl

def kid21_part167 : Audit := .cycle 3 11 true (1)
theorem kid21_part167_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid21_part167) = true := by rfl

def kid21_part168 : Audit := .cycle 11 3 true (4)
theorem kid21_part168_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid21_part168) = true := by rfl

def kid21_part169 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 6 10 true (2),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 49 1 false (5),
.cycle 0 24 true (0),
.cycle 29 6 false (4),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 31 true (0),
.cycle 5 20 true (0),
.cycle 11 6 true (4),
.cycle 23 1 false (1),
.cycle 38 5 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 44 1 false (4),
.cycle 0 25 true (0),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 12 true (2),
.cycle 15 2 true (4)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (3),
.cycle 0 22 true (0),
.cycle 11 4 true (4),
.cycle 14 1 true (6),
.cycle 12 3 true (4),
.split 16 (2,true) (byMove [
.cycle 10 7 true (4),
.cycle 13 4 true (5),
.cycle 55 1 false (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 14 3 true (5),
.cycle 6 11 true (2),
.last 18 (5,true),
.cycle 5 15 true (1),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 12 true (2),
.last 19 (5,true)
]),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 0 19 true (0),
.split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 9 10 true (3),
.cycle 0 29 true (0),
.cycle 0 46 true (0),
.cycle 5 25 true (0),
.cycle 21 1 false (-1),
.cycle 6 11 true (2),
.cycle 1 18 true (1),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 34 1 false (8),
.cycle 9 21 true (3),
.last 18 (2,true),
.cycle 5 13 true (1),
.cycle 0 27 true (0),
.cycle 5 19 true (1),
.cycle 21 1 false (-1),
.cycle 6 11 true (2),
.cycle 1 18 true (1),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 17 3 true (5)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 6 10 true (2),
.cycle 14 1 true (6)
])
theorem kid21_part169_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid21_part169) = true := by rfl

def kid21_part170 : Audit := .cycle 6 8 true (2)
theorem kid21_part170_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid21_part170) = true := by rfl

def kid21_part171 : Audit := .split 16 (2,true) (byMove [
.cycle 35 7 false (1),
.cycle 24 3 false (0),
.cycle 34 1 false (2),
.cycle 12 6 true (3),
.cycle 4 14 true (1),
.split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 0 26 true (0),
.last 33 (5,false),
.cycle 33 1 false (1),
.cycle 21 7 false (1),
.last 18 (5,false),
.cycle 12 6 true (3),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.cycle 35 7 false (1),
.last 18 (5,false),
.cycle 38 6 false (7),
.cycle 25 3 false (0),
.cycle 12 8 true (2),
.cycle 39 1 false (1),
.cycle 21 7 false (1),
.last 18 (5,false),
.cycle 34 7 false (2),
.cycle 1 20 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 22 true (0),
.last 18 (5,false)
]),
.cycle 10 7 true (3),
.cycle 1 19 true (1),
.cycle 9 17 true (3),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 8 10 true (3),
.cycle 6 13 true (2),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 17 true (3),
.cycle 0 25 true (0),
.cycle 11 7 true (3),
.last 18 (5,false),
.cycle 34 7 false (2),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 22 true (0),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 8 10 true (3),
.cycle 6 13 true (2),
.last 18 (5,false)
]),
.cycle 0 20 true (0),
.cycle 24 3 false (0),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.split 17 (5,true) (byMove [
.cycle 27 12 false (2),
.cycle 9 11 true (2),
.cycle 5 20 true (0),
.cycle 0 28 true (0),
.cycle 21 7 false (1),
.last 18 (5,false),
.cycle 6 12 true (2),
.cycle 14 4 true (3),
.last 19 (5,false),
.cycle 9 9 true (3),
.cycle 0 20 true (0),
.last 20 (5,false),
.cycle 0 30 true (0),
.cycle 25 3 false (0),
.cycle 5 14 true (1),
.cycle 5 18 true (0),
.cycle 21 7 false (1),
.last 18 (5,false),
.cycle 6 12 true (2),
.cycle 29 5 false (1),
.cycle 16 2 true (3),
.cycle 9 9 true (3),
.cycle 0 20 true (0),
.last 20 (5,false)
]),
.cycle 0 29 true (0),
.cycle 28 5 false (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.split 17 (5,true) (byMove [
.cycle 40 9 false (2),
.cycle 29 5 false (1),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.last 20 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 26 true (0),
.cycle 3 15 true (1),
.cycle 0 29 true (0),
.last 18 (5,false),
.cycle 6 12 true (2),
.cycle 29 5 false (1),
.cycle 16 2 true (4),
.cycle 9 9 true (3),
.cycle 0 20 true (0),
.last 20 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 8 10 true (3),
.cycle 6 13 true (2),
.last 18 (5,false)
])
])
theorem kid21_part171_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid21_part171) = true := by rfl

def kid21_part172 : Audit := .split 14 (2,true) (byMove [
.cycle 48 13 false (2),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 32 1 false (2),
.cycle 33 4 false (7),
.split 15 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.cycle 31 1 false (1),
.cycle 29 1 false (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 12 4 true (3),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 30 (5,true),
.last 17 (5,true),
.cycle 34 4 false (7),
.last 18 (5,true),
.cycle 12 6 true (2),
.cycle 33 1 false (1),
.last 20 (5,true),
.last 18 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 20 true (0),
.last 17 (5,true)
]),
.cycle 10 5 true (4),
.cycle 0 18 true (0),
.cycle 5 41 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 37 5 false (3),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 12 4 true (4),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 38 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.last 16 (5,false)
]),
.cycle 0 30 true (0),
.cycle 5 14 true (1),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.cycle 0 26 true (0),
.split 15 (5,false) (byMove [
.last 19 (5,true),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 6 10 true (2),
.cycle 9 9 true (3),
.cycle 14 2 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 26 true (0),
.last 18 (5,true),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 6 10 true (2),
.last 24 (5,true),
.last 17 (5,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true)
]),
.cycle 10 5 true (4),
.cycle 13 2 true (4),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 10 6 true (4),
.cycle 0 19 true (0),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 6 10 true (2),
.cycle 9 9 true (3),
.cycle 14 2 true (4),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.last 16 (5,false)
])
])
theorem kid21_part172_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid21_part172) = true := by rfl

def kid21_part173 : Audit := .cycle 9 5 true (3)
theorem kid21_part173_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid21_part173) = true := by rfl

def kid21_part174 : Audit := .cycle 0 16 true (0)
theorem kid21_part174_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid21_part174) = true := by rfl

def kid21_part176 : Audit := .split 17 (2,true) (byMove [
.cycle 49 13 false (2),
.cycle 33 5 false (1),
.cycle 0 28 true (0),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.cycle 41 9 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 26 true (0),
.cycle 3 15 true (1),
.cycle 0 37 true (0),
.last 18 (5,false),
.cycle 6 12 true (2),
.cycle 33 5 false (1),
.cycle 5 16 true (1),
.cycle 9 9 true (3),
.cycle 0 20 true (0),
.cycle 41 9 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 8 10 true (3),
.cycle 6 13 true (2),
.last 18 (5,false)
])
theorem kid21_part176_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part176) = true := by rfl

def kid21_part177 : Audit := .cycle 0 18 true (0)
theorem kid21_part177_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part177) = true := by rfl

def kid21_part178 : Audit := .cycle 5 18 true (0)
theorem kid21_part178_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part178) = true := by rfl

def kid21_part179 : Audit := .cycle 32 1 false (2)
theorem kid21_part179_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part179) = true := by rfl

def kid21_part180 : Audit := .cycle 33 4 false (7)
theorem kid21_part180_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part180) = true := by rfl

def kid21_part181 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 28 (2,true),
.cycle 29 1 false (1),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 12 4 true (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 30 5 false (0),
.cycle 18 1 true (4),
.cycle 34 4 false (7),
.last 17 (2,true),
.cycle 12 6 true (2),
.cycle 33 1 false (1),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.last 23 (2,true),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 20 true (0),
.cycle 20 1 true (2)
])
theorem kid21_part181_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part181) = true := by rfl

def kid21_part182 : Audit := .cycle 10 5 true (4)
theorem kid21_part182_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part182) = true := by rfl

def kid21_part183 : Audit := .split 16 (5,false) (byMove [
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.cycle 38 1 false (2),
.cycle 37 6 false (7),
.cycle 40 1 false (6),
.cycle 10 7 true (4),
.cycle 15 2 true (4),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 1 17 true (1),
.cycle 0 38 true (0),
.last 18 (2,true),
.cycle 9 9 true (3),
.cycle 5 18 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (0),
.cycle 10 7 true (4),
.cycle 13 4 true (4),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 1 17 true (1)
])
theorem kid21_part183_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part183) = true := by rfl

def kid21_part184 : Audit := .split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 37 5 false (3),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 12 4 true (4),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 38 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.last 16 (5,false)
])
theorem kid21_part184_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part184) = true := by rfl

def kid21_part185 : Audit := .cycle 0 16 true (0)
theorem kid21_part185_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part185) = true := by rfl

def kid21_part186 : Audit := .cycle 7 8 true (3)
theorem kid21_part186_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part186) = true := by rfl

def kid21_part187 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 31 true (0),
.cycle 5 20 true (0),
.cycle 11 6 true (4),
.cycle 23 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 5 27 true (0),
.cycle 5 41 true (0),
.cycle 11 6 true (4),
.cycle 16 1 true (6),
.cycle 12 5 true (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.cycle 14 7 true (4),
.cycle 29 1 false (7),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 12 true (2),
.cycle 16 1 true (6)
])
theorem kid21_part187_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part187) = true := by rfl

def kid21_part188 : Audit := .cycle 0 30 true (0)
theorem kid21_part188_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part188) = true := by rfl

def kid21_part189 : Audit := .split 16 (2,true) (byMove [
.last 37 (5,false),
.last 18 (5,false),
.cycle 34 1 false (2),
.cycle 12 6 true (3),
.cycle 4 14 true (1),
.last 25 (5,false),
.cycle 10 7 true (3),
.last 18 (5,false),
.cycle 9 17 true (3),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 20 (5,false),
.cycle 0 20 true (0),
.last 18 (5,false),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.last 25 (5,false),
.cycle 0 29 true (0),
.last 20 (5,false),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 31 (5,false)
])
theorem kid21_part189_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part189) = true := by rfl

def kid21_part190 : Audit := .cycle 9 7 true (3)
theorem kid21_part190_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part190) = true := by rfl

def kid21_part191 : Audit := .cycle 5 16 true (0)
theorem kid21_part191_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part191) = true := by rfl

def kid21_part192 : Audit := .cycle 0 26 true (0)
theorem kid21_part192_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part192) = true := by rfl

def kid21_part193 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 6 10 true (2),
.cycle 15 2 true (3),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 14 2 true (3),
.cycle 0 26 true (0),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 6 10 true (2),
.cycle 24 3 false (0),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 23 3 false (1)
])
theorem kid21_part193_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part193) = true := by rfl

def kid21_part194 : Audit := .cycle 10 5 true (4)
theorem kid21_part194_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part194) = true := by rfl

def kid21_part195 : Audit := .cycle 13 2 true (4)
theorem kid21_part195_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part195) = true := by rfl

def kid21_part196 : Audit := .split 15 (2,true) (byMove [
.cycle 10 6 true (4),
.last 17 (5,false),
.cycle 49 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 2 15 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 6 10 true (2),
.last 17 (5,false),
.cycle 9 9 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 14 2 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.last 16 (5,false)
])
theorem kid21_part196_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part196) = true := by rfl

def kid21_part197 : Audit := .cycle 0 16 true (0)
theorem kid21_part197_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part197) = true := by rfl

def kid21_part198 : Audit := .cycle 7 8 true (3)
theorem kid21_part198_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part198) = true := by rfl

def kid21_part199 : Audit := .split 16 (5,false) (byMove [
.cycle 10 7 true (4),
.cycle 13 4 true (4),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 15 2 true (5),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 16 1 true (6),
.cycle 6 11 true (2),
.cycle 14 5 true (4),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 14 3 true (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 12 true (2),
.cycle 16 1 true (6)
])
theorem kid21_part199_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part199) = true := by rfl

def kid21_part175 : Audit := .split 14 (5,true) (byMove [(kid21_part176),(kid21_part177),(kid21_part178),(kid21_part179),(kid21_part180),(kid21_part181),(kid21_part182),(kid21_part183),(kid21_part184),(kid21_part185),(kid21_part186),(kid21_part187),(kid21_part188),(kid21_part189),(kid21_part190),(kid21_part191),(kid21_part192),(kid21_part193),(kid21_part194),(kid21_part195),(kid21_part196),(kid21_part197),(kid21_part198),(kid21_part199)])

theorem kid21_part175_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid21_part175) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 14 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part176),(kid21_part177),(kid21_part178),(kid21_part179),(kid21_part180),(kid21_part181),(kid21_part182),(kid21_part183),(kid21_part184),(kid21_part185),(kid21_part186),(kid21_part187),(kid21_part188),(kid21_part189),(kid21_part190),(kid21_part191),(kid21_part192),(kid21_part193),(kid21_part194),(kid21_part195),(kid21_part196),(kid21_part197),(kid21_part198),(kid21_part199)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part176_checked

  · exact kid21_part182_checked

  · exact kid21_part188_checked

  · exact kid21_part194_checked

  · exact kid21_part177_checked

  · exact kid21_part183_checked

  · exact kid21_part189_checked

  · exact kid21_part195_checked

  · exact kid21_part178_checked

  · exact kid21_part184_checked

  · exact kid21_part190_checked

  · exact kid21_part196_checked

  · exact kid21_part179_checked

  · exact kid21_part185_checked

  · exact kid21_part191_checked

  · exact kid21_part197_checked

  · exact kid21_part180_checked

  · exact kid21_part186_checked

  · exact kid21_part192_checked

  · exact kid21_part198_checked

  · exact kid21_part181_checked

  · exact kid21_part187_checked

  · exact kid21_part193_checked

  · exact kid21_part199_checked

def kid21_part200 : Audit := .cycle 0 14 true (0)
theorem kid21_part200_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid21_part200) = true := by rfl

def kid21_part201 : Audit := .cycle 1 13 true (1)
theorem kid21_part201_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid21_part201) = true := by rfl

def kid21_part202 : Audit := .cycle 2 12 true (1)
theorem kid21_part202_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid21_part202) = true := by rfl

def kid21_part203 : Audit := .cycle 8 6 true (3)
theorem kid21_part203_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid21_part203) = true := by rfl

def kid21_part204 : Audit := .cycle 6 9 true (2)
theorem kid21_part204_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid21_part204) = true := by rfl

def kid21_part205 : Audit := .split 14 (5,false) (byMove [
.cycle 10 5 true (4),
.cycle 13 2 true (5),
.split 15 (2,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 18 true (1),
.cycle 49 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 2 15 true (1),
.cycle 6 10 true (2),
.last 17 (5,true),
.cycle 9 9 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 14 2 true (5)
]),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 18 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 25 1 false (1),
.cycle 6 10 true (2),
.cycle 15 2 true (4),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 11 true (2),
.cycle 14 2 true (5)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (4),
.cycle 14 1 true (6),
.cycle 6 9 true (2),
.split 16 (5,true) (byMove [
.cycle 10 7 true (4),
.cycle 13 4 true (5),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 21 (2,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.last 19 (2,true),
.cycle 6 11 true (2),
.cycle 15 2 true (5),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 21 (2,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 6 12 true (2),
.cycle 14 3 true (5)
]),
.split 15 (2,true) (byMove [
.last 20 (5,true),
.cycle 9 12 true (3),
.last 30 (5,true),
.cycle 12 5 true (4),
.cycle 4 13 true (1),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.cycle 9 16 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 5 13 true (1),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.cycle 2 15 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.split 15 (5,true) (byMove [
.cycle 10 11 true (4),
.cycle 9 12 true (3),
.last 16 (2,true),
.cycle 12 5 true (4),
.cycle 4 13 true (1),
.cycle 21 1 false (-1),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 41 1 false (9),
.cycle 0 19 true (0),
.cycle 15 2 true (4),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.cycle 21 1 false (-1),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 14 3 true (5)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 6 10 true (2),
.cycle 14 1 true (6)
])
theorem kid21_part205_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid21_part205) = true := by rfl

def kid21_part157 : Audit := .split 13 (1,true) (byMove [(kid21_part158),(kid21_part159),(kid21_part160),(kid21_part161),(kid21_part162),(kid21_part163),(kid21_part164),(kid21_part165),(kid21_part166),(kid21_part167),(kid21_part168),(kid21_part169),(kid21_part170),(kid21_part171),(kid21_part172),(kid21_part173),(kid21_part174),(kid21_part175),(kid21_part200),(kid21_part201),(kid21_part202),(kid21_part203),(kid21_part204),(kid21_part205)])

theorem kid21_part157_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (kid21_part157) = true := by

  change (zipQueryOK 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) 13 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid21_part158),(kid21_part159),(kid21_part160),(kid21_part161),(kid21_part162),(kid21_part163),(kid21_part164),(kid21_part165),(kid21_part166),(kid21_part167),(kid21_part168),(kid21_part169),(kid21_part170),(kid21_part171),(kid21_part172),(kid21_part173),(kid21_part174),(kid21_part175),(kid21_part200),(kid21_part201),(kid21_part202),(kid21_part203),(kid21_part204),(kid21_part205)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part158_checked

  · exact kid21_part164_checked

  · exact kid21_part170_checked

  · exact kid21_part200_checked

  · exact kid21_part159_checked

  · exact kid21_part165_checked

  · exact kid21_part171_checked

  · exact kid21_part201_checked

  · exact kid21_part160_checked

  · exact kid21_part166_checked

  · exact kid21_part172_checked

  · exact kid21_part202_checked

  · exact kid21_part161_checked

  · exact kid21_part167_checked

  · exact kid21_part173_checked

  · exact kid21_part203_checked

  · exact kid21_part162_checked

  · exact kid21_part168_checked

  · exact kid21_part174_checked

  · exact kid21_part204_checked

  · exact kid21_part163_checked

  · exact kid21_part169_checked

  · exact kid21_part175_checked

  · exact kid21_part205_checked

def kid21_part207 : Audit := .cycle 10 4 true (4)
theorem kid21_part207_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid21_part207) = true := by rfl

def kid21_part208 : Audit := .split 14 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 20 4 false (0),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.last 30 (5,true),
.cycle 15 1 true (3),
.last 18 (5,true),
.cycle 20 4 false (0),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 24 (5,true),
.cycle 15 1 true (3)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.last 33 (5,true),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 14 3 true (4),
.cycle 12 4 true (4),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 33 (5,true),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 18 (5,true),
.cycle 15 1 true (5)
]),
.cycle 6 11 true (2),
.cycle 24 3 false (0),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 20 4 false (0),
.split 15 (5,false) (byMove [
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 0 39 true (0),
.cycle 33 1 false (3),
.last 20 (5,true),
.last 18 (5,true),
.cycle 10 6 true (3),
.cycle 14 2 true (3),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.last 18 (5,true),
.cycle 20 4 false (0),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.last 20 (5,true),
.last 18 (5,true),
.last 21 (5,true),
.last 17 (5,true),
.last 24 (5,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 10 true (3),
.split 15 (5,false) (byMove [
.cycle 10 6 true (4),
.cycle 14 2 true (4),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 6 10 true (2),
.last 17 (5,true),
.cycle 0 20 true (0),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 18 (5,true),
.cycle 15 1 true (5)
])
])
theorem kid21_part208_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid21_part208) = true := by rfl

def kid21_part209 : Audit := .cycle 43 1 false (5)
theorem kid21_part209_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid21_part209) = true := by rfl

def kid21_part210 : Audit := .cycle 0 15 true (0)
theorem kid21_part210_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid21_part210) = true := by rfl

def kid21_part211 : Audit := .cycle 7 7 true (3)
theorem kid21_part211_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid21_part211) = true := by rfl

def kid21_part213 : Audit := .cycle 0 15 true (0)
theorem kid21_part213_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part213) = true := by rfl

def kid21_part214 : Audit := .cycle 1 14 true (1)
theorem kid21_part214_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part214) = true := by rfl

def kid21_part215 : Audit := .cycle 43 1 false (5)
theorem kid21_part215_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part215) = true := by rfl

def kid21_part216 : Audit := .cycle 0 22 true (0)
theorem kid21_part216_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part216) = true := by rfl

def kid21_part217 : Audit := .split 20 (1,true) (byMove [
.cycle 29 4 false (1),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 22 4 false (2),
.cycle 32 4 false (6),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 25 4 false (3),
.cycle 21 4 false (1),
.cycle 0 26 true (-1),
.cycle 21 4 false (0),
.cycle 24 4 false (2),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 30 4 false (2),
.cycle 1 21 true (0),
.cycle 21 4 false (1),
.cycle 0 22 true (0),
.cycle 15 10 true (0),
.cycle 26 4 false (2)
])
theorem kid21_part217_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part217) = true := by rfl

def kid21_part218 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 29 1 false (1),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 30 5 false (0),
.cycle 15 1 true (3),
.last 17 (1,true),
.last 20 (1,true),
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (1,true),
.cycle 15 1 true (3)
])
theorem kid21_part218_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part218) = true := by rfl

def kid21_part219 : Audit := .cycle 0 15 true (0)
theorem kid21_part219_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part219) = true := by rfl

def kid21_part220 : Audit := .cycle 1 14 true (1)
theorem kid21_part220_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part220) = true := by rfl

def kid21_part221 : Audit := .cycle 0 29 true (0)
theorem kid21_part221_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part221) = true := by rfl

def kid21_part222 : Audit := .cycle 5 18 true (0)
theorem kid21_part222_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part222) = true := by rfl

def kid21_part223 : Audit := .cycle 11 4 true (4)
theorem kid21_part223_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part223) = true := by rfl

def kid21_part224 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.last 32 (1,true),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.last 17 (1,true),
.cycle 12 4 true (4),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 32 (1,true),
.cycle 26 1 false (6),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (1,true),
.cycle 15 1 true (5)
])
theorem kid21_part224_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part224) = true := by rfl

def kid21_part225 : Audit := .split 16 (1,true) (byMove [
.cycle 40 7 false (3),
.cycle 1 17 true (1),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 32 3 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 6 15 true (2),
.last 17 (5,false),
.cycle 6 11 true (2),
.cycle 23 6 false (1),
.last 18 (5,false),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 5 21 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 7 12 true (3),
.last 17 (5,false)
])
theorem kid21_part225_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part225) = true := by rfl

def kid21_part226 : Audit := .split 24 (1,true) (byMove [
.cycle 21 5 false (2),
.cycle 0 28 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 26 3 false (-1),
.last 25 (5,false),
.cycle 27 3 false (2),
.cycle 37 3 false (6),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 30 3 false (3),
.cycle 25 3 false (1),
.cycle 0 30 true (-1),
.cycle 25 3 false (0),
.cycle 29 3 false (2),
.cycle 25 1 false (-1),
.cycle 26 3 false (-1),
.last 25 (5,false),
.cycle 21 6 true (0),
.cycle 1 25 true (0),
.cycle 25 3 false (1),
.cycle 0 26 true (0),
.cycle 18 12 true (0),
.cycle 23 2 true (0)
])
theorem kid21_part226_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part226) = true := by rfl

def kid21_part227 : Audit := .cycle 0 17 true (0)
theorem kid21_part227_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part227) = true := by rfl

def kid21_part228 : Audit := .cycle 38 1 false (4)
theorem kid21_part228_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part228) = true := by rfl

def kid21_part229 : Audit := .split 20 (1,true) (byMove [
.cycle 15 15 false (3),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 2, 32, 18, 18, 16, 64],96⟩,
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 30 4 false (6),
.cycle 23 4 false (4),
.last 22 (5,false),
.cycle 23 4 false (3),
.cycle 0 31 true (0),
.cycle 21 4 false (1),
.cycle 15 12 true (-1),
.cycle 21 4 false (0),
.cycle 32 4 false (6),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 0 48 true (0),
.cycle 0 28 true (0),
.cycle 21 4 false (1),
.cycle 15 8 true (0),
.cycle 0 39 true (0),
.cycle 15 10 true (0)
])
theorem kid21_part229_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part229) = true := by rfl

def kid21_part230 : Audit := .split 15 (5,false) (byMove [
.cycle 26 6 false (0),
.cycle 0 19 true (0),
.cycle 33 1 false (1),
.cycle 33 1 false (3),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 10 6 true (3),
.last 16 (1,true),
.cycle 5 22 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 14 2 true (3),
.last 17 (1,true),
.last 20 (1,true),
.cycle 9 8 true (2),
.cycle 39 1 false (3),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 6 17 true (2),
.last 16 (1,true),
.cycle 24 3 false (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 23 3 false (1)
])
theorem kid21_part230_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part230) = true := by rfl

def kid21_part231 : Audit := .cycle 0 15 true (0)
theorem kid21_part231_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part231) = true := by rfl

def kid21_part232 : Audit := .cycle 1 14 true (1)
theorem kid21_part232_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part232) = true := by rfl

def kid21_part233 : Audit := .cycle 2 13 true (1)
theorem kid21_part233_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part233) = true := by rfl

def kid21_part234 : Audit := .cycle 8 7 true (3)
theorem kid21_part234_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part234) = true := by rfl

def kid21_part235 : Audit := .split 16 (1,true) (byMove [
.cycle 51 13 false (2),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.cycle 0 27 true (0),
.cycle 23 6 false (1),
.last 17 (5,false),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 14 3 true (4),
.cycle 0 22 true (0),
.cycle 32 5 false (0),
.cycle 9 9 true (3),
.cycle 5 18 true (0),
.cycle 23 6 false (1),
.last 17 (5,false),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 14 3 true (4)
])
theorem kid21_part235_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part235) = true := by rfl

def kid21_part236 : Audit := .split 15 (5,false) (byMove [
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 0 26 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 14 2 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 15 1 true (5),
.cycle 6 10 true (2),
.last 16 (1,true),
.last 21 (1,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 14 3 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (1,true),
.cycle 15 1 true (5)
])
theorem kid21_part236_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part236) = true := by rfl

def kid21_part212 : Audit := .split 14 (5,true) (byMove [(kid21_part213),(kid21_part214),(kid21_part215),(kid21_part216),(kid21_part217),(kid21_part218),(kid21_part219),(kid21_part220),(kid21_part221),(kid21_part222),(kid21_part223),(kid21_part224),(kid21_part225),(kid21_part226),(kid21_part227),(kid21_part228),(kid21_part229),(kid21_part230),(kid21_part231),(kid21_part232),(kid21_part233),(kid21_part234),(kid21_part235),(kid21_part236)])

theorem kid21_part212_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid21_part212) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) 14 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part213),(kid21_part214),(kid21_part215),(kid21_part216),(kid21_part217),(kid21_part218),(kid21_part219),(kid21_part220),(kid21_part221),(kid21_part222),(kid21_part223),(kid21_part224),(kid21_part225),(kid21_part226),(kid21_part227),(kid21_part228),(kid21_part229),(kid21_part230),(kid21_part231),(kid21_part232),(kid21_part233),(kid21_part234),(kid21_part235),(kid21_part236)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part213_checked

  · exact kid21_part219_checked

  · exact kid21_part225_checked

  · exact kid21_part231_checked

  · exact kid21_part214_checked

  · exact kid21_part220_checked

  · exact kid21_part226_checked

  · exact kid21_part232_checked

  · exact kid21_part215_checked

  · exact kid21_part221_checked

  · exact kid21_part227_checked

  · exact kid21_part233_checked

  · exact kid21_part216_checked

  · exact kid21_part222_checked

  · exact kid21_part228_checked

  · exact kid21_part234_checked

  · exact kid21_part217_checked

  · exact kid21_part223_checked

  · exact kid21_part229_checked

  · exact kid21_part235_checked

  · exact kid21_part218_checked

  · exact kid21_part224_checked

  · exact kid21_part230_checked

  · exact kid21_part236_checked

def kid21_part237 : Audit := .cycle 0 14 true (0)
theorem kid21_part237_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid21_part237) = true := by rfl

def kid21_part238 : Audit := .cycle 1 13 true (1)
theorem kid21_part238_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid21_part238) = true := by rfl

def kid21_part239 : Audit := .cycle 0 22 true (0)
theorem kid21_part239_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid21_part239) = true := by rfl

def kid21_part240 : Audit := .cycle 3 11 true (1)
theorem kid21_part240_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid21_part240) = true := by rfl

def kid21_part241 : Audit := .cycle 11 3 true (4)
theorem kid21_part241_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid21_part241) = true := by rfl

def kid21_part242 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.split 16 (1,true) (byMove [
.last 27 (5,true),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.cycle 0 27 true (0),
.cycle 23 6 false (1),
.last 24 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 11 8 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 22 true (0),
.last 19 (5,true),
.cycle 9 9 true (3),
.cycle 5 18 true (0),
.last 20 (5,true),
.last 24 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 49 1 false (5),
.cycle 0 24 true (0),
.last 24 (1,true),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 31 true (0),
.cycle 5 20 true (0),
.cycle 11 6 true (4),
.cycle 23 1 false (1),
.last 18 (1,true),
.last 32 (1,true),
.cycle 0 19 true (0),
.cycle 44 1 false (4),
.last 22 (1,true),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 18 (1,true),
.cycle 15 2 true (4)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (3),
.cycle 0 22 true (0),
.cycle 11 4 true (4),
.cycle 14 1 true (6),
.split 16 (1,true) (byMove [
.cycle 10 7 true (4),
.cycle 1 18 true (1),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 14 3 true (5),
.cycle 6 11 true (2),
.last 21 (5,true),
.last 18 (5,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 7 12 true (3),
.cycle 6 12 true (2)
]),
.cycle 12 3 true (4),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.split 16 (1,true) (byMove [
.last 20 (5,true),
.cycle 9 10 true (3),
.cycle 0 29 true (0),
.cycle 0 30 true (0),
.cycle 23 6 false (1),
.last 21 (5,true),
.cycle 6 11 true (2),
.cycle 1 18 true (1),
.last 18 (5,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 9 12 true (3),
.last 19 (5,true),
.cycle 5 13 true (1),
.cycle 0 27 true (0),
.last 20 (5,true),
.last 21 (5,true),
.cycle 6 11 true (2),
.cycle 1 18 true (1),
.last 18 (5,true),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true)
]),
.split 16 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 9 10 true (3),
.cycle 0 29 true (0),
.last 25 (1,true),
.last 24 (1,true),
.cycle 21 1 false (-1),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 5 29 true (0),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 34 1 false (8),
.last 18 (1,true),
.last 28 (1,true),
.cycle 5 13 true (1),
.cycle 0 27 true (0),
.last 22 (1,true),
.cycle 21 1 false (-1),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 2 17 true (1),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 17 3 true (5)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.split 16 (1,true) (byMove [
.cycle 12 6 true (4),
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 23 (5,true),
.cycle 4 20 true (1),
.last 20 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 22 true (0),
.last 19 (5,true),
.cycle 9 9 true (3),
.cycle 0 22 true (0),
.last 22 (5,true),
.cycle 0 20 true (0),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.cycle 14 1 true (6)
])
theorem kid21_part242_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid21_part242) = true := by rfl

def kid21_part243 : Audit := .cycle 6 8 true (2)
theorem kid21_part243_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid21_part243) = true := by rfl

def kid21_part244 : Audit := .split 14 (1,true) (byMove [
.cycle 39 9 false (2),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 25 true (0),
.cycle 20 4 false (0),
.split 15 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 26 (5,true),
.cycle 29 1 false (1),
.last 20 (5,true),
.last 18 (5,true),
.last 18 (5,true),
.cycle 12 4 true (3),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 30 (5,true),
.last 17 (5,true),
.last 18 (5,true),
.cycle 20 4 false (0),
.last 20 (5,true),
.last 24 (5,true),
.last 20 (5,true),
.last 18 (5,true),
.last 18 (5,true),
.last 19 (5,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 24 (5,true),
.last 17 (5,true)
]),
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.cycle 12 4 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 32 5 false (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.last 16 (5,false),
.last 18 (5,false),
.cycle 12 4 true (4),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 32 5 false (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 14 3 true (4),
.last 16 (5,false)
]),
.cycle 0 20 true (0),
.cycle 24 3 false (0),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.cycle 20 4 false (0),
.split 15 (5,false) (byMove [
.last 20 (5,true),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 6 10 true (2),
.cycle 14 2 true (3),
.last 30 (5,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.last 18 (5,true),
.cycle 20 4 false (0),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.last 20 (5,true),
.last 18 (5,true),
.cycle 6 10 true (2),
.last 17 (5,true),
.last 24 (5,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true)
]),
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.cycle 13 2 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 10 6 true (4),
.last 17 (5,false),
.cycle 31 5 false (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 6 10 true (2),
.cycle 14 2 true (4),
.cycle 31 5 false (1),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 14 3 true (4),
.last 16 (5,false)
])
])
theorem kid21_part244_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid21_part244) = true := by rfl

def kid21_part245 : Audit := .cycle 9 7 true (3)
theorem kid21_part245_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid21_part245) = true := by rfl

def kid21_part246 : Audit := .cycle 9 5 true (3)
theorem kid21_part246_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid21_part246) = true := by rfl

def kid21_part247 : Audit := .cycle 0 16 true (0)
theorem kid21_part247_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid21_part247) = true := by rfl

def kid21_part249 : Audit := .cycle 39 9 false (2)
theorem kid21_part249_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part249) = true := by rfl

def kid21_part250 : Audit := .cycle 0 18 true (0)
theorem kid21_part250_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part250) = true := by rfl

def kid21_part251 : Audit := .cycle 5 18 true (0)
theorem kid21_part251_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part251) = true := by rfl

def kid21_part252 : Audit := .split 23 (1,true) (byMove [
.cycle 36 1 false (2),
.cycle 1 24 true (0),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 48 1 false (6),
.cycle 32 1 false (2),
.cycle 0 24 true (0),
.cycle 78 1 false (4),
.cycle 0 32 true (0),
.cycle 56 1 false (4),
.cycle 21 7 true (3),
.last 24 (5,false),
.cycle 6 18 true (0),
.cycle 35 1 false (1),
.last 25 (5,false),
.cycle 46 1 false (6),
.cycle 0 26 true (0),
.cycle 32 1 false (2),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 0 48 true (0),
.cycle 70 1 false (6),
.last 24 (5,false)
])
theorem kid21_part252_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part252) = true := by rfl

def kid21_part253 : Audit := .split 20 (1,true) (byMove [
.cycle 41 4 false (7),
.cycle 77 4 false (9),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 22 4 false (2),
.cycle 22 4 false (3),
.last 22 (5,false),
.cycle 0 30 true (0),
.cycle 33 4 false (7),
.cycle 21 4 false (1),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 2, 64, 64],[19, 1, 32, 19, 19, 16, 64],96⟩,
.cycle 21 4 false (0),
.cycle 24 4 false (2),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 0 34 true (0),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 18, 32, 18, 18, 16, 64],96⟩,
.cycle 21 4 false (1),
.cycle 4 20 true (0),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 18, 32, 18, 18, 16, 64],96⟩,
.cycle 26 4 false (2)
])
theorem kid21_part253_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part253) = true := by rfl

def kid21_part254 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 25 (1,true),
.cycle 29 1 false (1),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.last 17 (1,true),
.cycle 12 4 true (3),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 30 5 false (0),
.cycle 18 1 true (4),
.last 17 (1,true),
.last 20 (1,true),
.last 19 (1,true),
.last 23 (1,true),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.last 17 (1,true),
.cycle 0 24 true (0),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (1,true),
.cycle 20 1 true (2)
])
theorem kid21_part254_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part254) = true := by rfl

def kid21_part255 : Audit := .cycle 10 5 true (4)
theorem kid21_part255_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part255) = true := by rfl

def kid21_part256 : Audit := .split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 20 true (0),
.cycle 43 1 false (5),
.cycle 32 5 false (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 5 41 true (0),
.cycle 0 29 true (0),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 6 12 true (2),
.cycle 12 4 true (4),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 32 5 false (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.last 16 (5,false)
])
theorem kid21_part256_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part256) = true := by rfl

def kid21_part257 : Audit := .split 16 (5,false) (byMove [
.cycle 51 13 false (2),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.last 25 (1,true),
.last 24 (1,true),
.cycle 22 1 false (2),
.cycle 10 7 true (4),
.last 17 (1,true),
.cycle 15 2 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 5 45 true (0),
.last 18 (1,true),
.last 32 (1,true),
.cycle 9 9 true (3),
.cycle 5 18 true (0),
.last 24 (1,true),
.cycle 22 1 false (0),
.cycle 10 7 true (4),
.last 17 (1,true),
.cycle 13 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 0 26 true (0)
])
theorem kid21_part257_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part257) = true := by rfl

def kid21_part258 : Audit := .cycle 0 16 true (0)
theorem kid21_part258_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part258) = true := by rfl

def kid21_part259 : Audit := .cycle 7 8 true (3)
theorem kid21_part259_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part259) = true := by rfl

def kid21_part260 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 31 true (0),
.cycle 5 20 true (0),
.cycle 11 6 true (4),
.cycle 23 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 5 27 true (0),
.cycle 5 41 true (0),
.cycle 11 6 true (4),
.cycle 16 1 true (6),
.last 18 (1,true),
.cycle 12 5 true (4),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.cycle 14 7 true (4),
.cycle 29 1 false (7),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 18 (1,true),
.cycle 16 1 true (6)
])
theorem kid21_part260_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part260) = true := by rfl

def kid21_part261 : Audit := .split 16 (1,true) (byMove [
.cycle 0 42 true (0),
.cycle 0 26 true (0),
.last 18 (5,false),
.cycle 0 21 true (0),
.cycle 4 14 true (1),
.cycle 32 3 false (2),
.cycle 10 7 true (3),
.cycle 1 17 true (1),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 23 6 false (1),
.last 18 (5,false),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.cycle 0 30 true (0),
.cycle 0 25 true (0),
.cycle 1 17 true (1),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 6 12 true (2)
])
theorem kid21_part261_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part261) = true := by rfl

def kid21_part262 : Audit := .split 24 (1,true) (byMove [
.cycle 21 5 false (2),
.cycle 5 65 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 26 3 false (-1),
.last 25 (5,false),
.cycle 5 22 true (0),
.cycle 41 3 false (10),
.last 26 (5,false),
.cycle 45 3 false (8),
.cycle 0 30 true (0),
.cycle 25 3 false (1),
.cycle 5 41 true (-1),
.cycle 25 3 false (0),
.cycle 5 24 true (-1),
.cycle 25 1 false (-1),
.cycle 26 3 false (-1),
.last 25 (5,false),
.cycle 5 22 true (0),
.cycle 1 29 true (0),
.cycle 25 3 false (1),
.cycle 5 33 true (0),
.cycle 0 30 true (0),
.cycle 23 2 true (0)
])
theorem kid21_part262_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part262) = true := by rfl

def kid21_part263 : Audit := .cycle 9 7 true (3)
theorem kid21_part263_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part263) = true := by rfl

def kid21_part264 : Audit := .cycle 5 16 true (0)
theorem kid21_part264_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part264) = true := by rfl

def kid21_part265 : Audit := .split 20 (1,true) (byMove [
.cycle 5 24 true (-1),
.cycle 5 53 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 5 18 true (0),
.cycle 36 4 false (10),
.last 22 (5,false),
.cycle 38 4 false (8),
.cycle 0 26 true (0),
.cycle 21 4 false (1),
.cycle 5 35 true (-1),
.cycle 21 4 false (0),
.cycle 5 20 true (-1),
.cycle 21 1 false (-1),
.cycle 21 4 false (-1),
.last 21 (5,false),
.cycle 5 18 true (0),
.cycle 1 25 true (0),
.cycle 21 4 false (1),
.cycle 5 27 true (0),
.cycle 0 26 true (0),
.cycle 5 31 true (0)
])
theorem kid21_part265_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part265) = true := by rfl

def kid21_part266 : Audit := .split 15 (5,false) (byMove [
.cycle 26 6 false (0),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 15 2 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 14 2 true (3),
.last 17 (1,true),
.last 20 (1,true),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.cycle 20 5 false (0),
.cycle 19 1 false (-1),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 24 3 false (0),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 23 3 false (1)
])
theorem kid21_part266_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part266) = true := by rfl

def kid21_part267 : Audit := .cycle 10 5 true (4)
theorem kid21_part267_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part267) = true := by rfl

def kid21_part268 : Audit := .split 15 (1,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.last 16 (5,false),
.cycle 6 10 true (2),
.cycle 31 5 false (1),
.last 17 (5,false),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 14 2 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.last 16 (5,false)
])
theorem kid21_part268_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part268) = true := by rfl

def kid21_part269 : Audit := .cycle 13 2 true (4)
theorem kid21_part269_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part269) = true := by rfl

def kid21_part270 : Audit := .cycle 0 16 true (0)
theorem kid21_part270_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part270) = true := by rfl

def kid21_part271 : Audit := .cycle 7 8 true (3)
theorem kid21_part271_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part271) = true := by rfl

def kid21_part272 : Audit := .split 16 (5,false) (byMove [
.cycle 10 7 true (4),
.last 17 (1,true),
.cycle 13 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 15 2 true (5),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 16 1 true (6),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 14 5 true (4),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 14 3 true (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 18 (1,true),
.cycle 16 1 true (6)
])
theorem kid21_part272_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part272) = true := by rfl

def kid21_part248 : Audit := .split 14 (5,true) (byMove [(kid21_part249),(kid21_part250),(kid21_part251),(kid21_part252),(kid21_part253),(kid21_part254),(kid21_part255),(kid21_part256),(kid21_part257),(kid21_part258),(kid21_part259),(kid21_part260),(kid21_part261),(kid21_part262),(kid21_part263),(kid21_part264),(kid21_part265),(kid21_part266),(kid21_part267),(kid21_part268),(kid21_part269),(kid21_part270),(kid21_part271),(kid21_part272)])

theorem kid21_part248_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid21_part248) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 14 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part249),(kid21_part250),(kid21_part251),(kid21_part252),(kid21_part253),(kid21_part254),(kid21_part255),(kid21_part256),(kid21_part257),(kid21_part258),(kid21_part259),(kid21_part260),(kid21_part261),(kid21_part262),(kid21_part263),(kid21_part264),(kid21_part265),(kid21_part266),(kid21_part267),(kid21_part268),(kid21_part269),(kid21_part270),(kid21_part271),(kid21_part272)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part249_checked

  · exact kid21_part255_checked

  · exact kid21_part261_checked

  · exact kid21_part267_checked

  · exact kid21_part250_checked

  · exact kid21_part256_checked

  · exact kid21_part262_checked

  · exact kid21_part268_checked

  · exact kid21_part251_checked

  · exact kid21_part257_checked

  · exact kid21_part263_checked

  · exact kid21_part269_checked

  · exact kid21_part252_checked

  · exact kid21_part258_checked

  · exact kid21_part264_checked

  · exact kid21_part270_checked

  · exact kid21_part253_checked

  · exact kid21_part259_checked

  · exact kid21_part265_checked

  · exact kid21_part271_checked

  · exact kid21_part254_checked

  · exact kid21_part260_checked

  · exact kid21_part266_checked

  · exact kid21_part272_checked

def kid21_part273 : Audit := .cycle 0 14 true (0)
theorem kid21_part273_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid21_part273) = true := by rfl

def kid21_part274 : Audit := .cycle 1 13 true (1)
theorem kid21_part274_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid21_part274) = true := by rfl

def kid21_part275 : Audit := .cycle 2 12 true (1)
theorem kid21_part275_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid21_part275) = true := by rfl

def kid21_part276 : Audit := .cycle 8 6 true (3)
theorem kid21_part276_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid21_part276) = true := by rfl

def kid21_part277 : Audit := .split 15 (1,true) (byMove [
.cycle 7 13 true (3),
.cycle 0 25 true (0),
.cycle 0 31 true (0),
.cycle 0 20 true (0),
.cycle 4 13 true (1),
.split 16 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.cycle 46 32 true (4),
.cycle 23 7 true (3),
.last 25 (5,false),
.last 17 (5,false),
.cycle 0 20 true (0),
.cycle 12 5 true (4),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.cycle 7 13 true (3),
.last 17 (5,false),
.cycle 35 3 false (3),
.last 33 (5,false),
.cycle 0 24 true (0),
.cycle 42 28 true (4),
.cycle 4 17 true (1),
.last 17 (5,false),
.cycle 0 20 true (0),
.cycle 12 5 true (4),
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.last 19 (5,false),
.last 17 (5,false)
]),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 44 9 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 16 true (3),
.cycle 0 24 true (0),
.cycle 11 6 true (4),
.last 17 (5,false),
.last 19 (5,false),
.cycle 12 5 true (4),
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.cycle 0 25 true (0),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 14 3 true (5),
.last 17 (5,false)
]),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.split 16 (5,true) (byMove [
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 29 true (0),
.cycle 0 35 true (0),
.last 25 (5,false),
.last 17 (5,false),
.cycle 6 11 true (2),
.last 18 (5,false),
.cycle 7 11 true (3),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 19 (5,false),
.cycle 5 39 true (0),
.cycle 0 21 true (0),
.cycle 5 13 true (1),
.cycle 0 27 true (0),
.cycle 5 31 true (1),
.last 17 (5,false),
.cycle 6 11 true (2),
.cycle 15 2 true (4),
.cycle 7 11 true (3),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 19 (5,false)
]),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.split 16 (5,true) (byMove [
.cycle 10 7 true (4),
.last 18 (5,false),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 19 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.last 17 (5,false),
.cycle 6 11 true (2),
.cycle 15 2 true (5),
.cycle 7 11 true (3),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 19 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 14 3 true (5),
.last 17 (5,false)
])
])
theorem kid21_part277_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid21_part277) = true := by rfl

def kid21_part278 : Audit := .split 14 (5,false) (byMove [
.cycle 10 5 true (4),
.split 15 (1,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 55 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 1 16 true (1),
.cycle 6 10 true (2),
.last 19 (5,true),
.last 17 (5,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.cycle 14 2 true (5)
]),
.cycle 13 2 true (5),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.split 15 (5,true) (byMove [
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 55 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 25 1 false (1),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 15 2 true (4),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (1,true),
.cycle 14 2 true (5)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (4),
.cycle 14 1 true (6),
.cycle 6 9 true (2),
.split 15 (1,true) (byMove [
.last 20 (5,true),
.cycle 0 25 true (0),
.cycle 0 31 true (0),
.cycle 0 20 true (0),
.cycle 4 13 true (1),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 17 (5,true),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
]),
.split 16 (5,true) (byMove [
.cycle 10 7 true (4),
.last 17 (1,true),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 0 22 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 0 20 true (0),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 15 2 true (5),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 0 25 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 18 (1,true),
.cycle 14 3 true (5)
]),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.split 15 (5,true) (byMove [
.cycle 10 11 true (4),
.last 16 (1,true),
.cycle 0 31 true (0),
.last 18 (1,true),
.cycle 4 13 true (1),
.cycle 21 1 false (-1),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 41 1 false (9),
.cycle 0 19 true (0),
.last 16 (1,true),
.cycle 15 2 true (4),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.cycle 21 1 false (-1),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 14 3 true (5)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.split 16 (1,true) (byMove [
.last 21 (5,true),
.cycle 4 22 true (1),
.cycle 7 12 true (3),
.cycle 0 21 true (0),
.cycle 4 14 true (1),
.last 17 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 20 true (0),
.last 21 (5,true),
.last 18 (5,true),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.last 17 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.cycle 14 1 true (6)
])
theorem kid21_part278_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid21_part278) = true := by rfl

def kid21_part206 : Audit := .split 13 (2,true) (byMove [(kid21_part207),(kid21_part208),(kid21_part209),(kid21_part210),(kid21_part211),(kid21_part212),(kid21_part237),(kid21_part238),(kid21_part239),(kid21_part240),(kid21_part241),(kid21_part242),(kid21_part243),(kid21_part244),(kid21_part245),(kid21_part246),(kid21_part247),(kid21_part248),(kid21_part273),(kid21_part274),(kid21_part275),(kid21_part276),(kid21_part277),(kid21_part278)])

theorem kid21_part206_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (kid21_part206) = true := by

  change (zipQueryOK 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) 13 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid21_part207),(kid21_part208),(kid21_part209),(kid21_part210),(kid21_part211),(kid21_part212),(kid21_part237),(kid21_part238),(kid21_part239),(kid21_part240),(kid21_part241),(kid21_part242),(kid21_part243),(kid21_part244),(kid21_part245),(kid21_part246),(kid21_part247),(kid21_part248),(kid21_part273),(kid21_part274),(kid21_part275),(kid21_part276),(kid21_part277),(kid21_part278)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part207_checked

  · exact kid21_part237_checked

  · exact kid21_part243_checked

  · exact kid21_part273_checked

  · exact kid21_part208_checked

  · exact kid21_part238_checked

  · exact kid21_part244_checked

  · exact kid21_part274_checked

  · exact kid21_part209_checked

  · exact kid21_part239_checked

  · exact kid21_part245_checked

  · exact kid21_part275_checked

  · exact kid21_part210_checked

  · exact kid21_part240_checked

  · exact kid21_part246_checked

  · exact kid21_part276_checked

  · exact kid21_part211_checked

  · exact kid21_part241_checked

  · exact kid21_part247_checked

  · exact kid21_part277_checked

  · exact kid21_part212_checked

  · exact kid21_part242_checked

  · exact kid21_part248_checked

  · exact kid21_part278_checked

def kid21_part279 : Audit := .cycle 0 14 true (0)
theorem kid21_part279_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,2⟩)) (kid21_part279) = true := by rfl

def kid21_part280 : Audit := .cycle 5 14 true (0)
theorem kid21_part280_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,3⟩)) (kid21_part280) = true := by rfl

def kid21_part281 : Audit := .cycle 5 21 true (0)
theorem kid21_part281_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,4⟩)) (kid21_part281) = true := by rfl

def kid21_part283 : Audit := .split 15 (2,true) (byMove [
.cycle 37 9 false (2),
.split 16 (1,true) (byMove [
.cycle 34 7 false (1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 38 9 false (2),
.cycle 0 18 true (0),
.cycle 6 11 true (2),
.cycle 24 3 false (0),
.cycle 0 21 true (0),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 18 (5,true),
.cycle 42 11 false (2)
]),
.cycle 0 26 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.split 16 (5,true) (byMove [
.cycle 34 7 false (1),
.last 17 (1,true),
.cycle 0 19 true (0),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 38 9 false (2),
.cycle 0 18 true (0),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 0 23 true (0),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 23 6 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 7 12 true (3),
.cycle 42 11 false (2)
]),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 0 29 true (0),
.cycle 0 17 true (0),
.cycle 6 10 true (2),
.split 16 (1,true) (byMove [
.cycle 34 7 false (1),
.cycle 0 26 true (0),
.cycle 39 1 false (1),
.cycle 0 21 true (0),
.cycle 4 14 true (1),
.last 17 (5,true),
.cycle 10 7 true (3),
.cycle 1 17 true (1),
.cycle 14 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 20 true (0),
.cycle 24 3 false (0),
.cycle 0 26 true (0),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.last 17 (5,true),
.cycle 0 33 true (0),
.cycle 1 17 true (1),
.cycle 15 2 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.cycle 5 14 true (1),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.split 16 (5,true) (byMove [
.cycle 34 7 false (1),
.last 17 (1,true),
.cycle 26 1 false (0),
.last 19 (1,true),
.cycle 4 14 true (1),
.cycle 0 28 true (0),
.cycle 10 7 true (3),
.last 17 (1,true),
.cycle 39 9 false (1),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 0 19 true (0),
.cycle 0 20 true (0),
.last 17 (1,true),
.cycle 5 24 true (-1),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.cycle 23 6 false (1),
.cycle 0 33 true (0),
.last 17 (1,true),
.cycle 15 2 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 32, 36, 64],[16, 64, 32, 1, 8, 32, 64],64⟩
]),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.split 17 (5,true) (byMove [
.cycle 0 29 true (0),
.last 18 (1,true),
.cycle 0 35 true (0),
.last 20 (1,true),
.cycle 4 15 true (1),
.cycle 4 25 true (1),
.cycle 10 8 true (3),
.last 18 (1,true),
.cycle 15 3 true (5),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.cycle 0 20 true (0),
.cycle 0 21 true (0),
.last 18 (1,true),
.cycle 0 21 true (0),
.cycle 5 13 true (1),
.cycle 9 10 true (3),
.cycle 101 71 true (9),
.cycle 5 69 true (1),
.last 18 (1,true),
.cycle 15 3 true (5),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.cycle 5 73 true (1)
]),
.split 29 (5,true) (byMove [
.cycle 46 13 false (3),
.last 30 (1,true),
.cycle 49 15 false (3),
.last 32 (1,true),
.cycle 4 27 true (1),
.cycle 0 127 false (6),
.cycle 6 79 true (1),
.last 30 (1,true),
.cycle 0 73 true (0),
.cycle 0 31 true (0),
.cycle 7 23 true (2),
.cycle 0 32 true (0),
.cycle 0 33 true (0),
.last 30 (1,true),
.cycle 28 2 true (4),
.cycle 5 25 true (1),
.cycle 5 85 true (1),
.cycle 36 8 false (2),
.cycle 0 52 true (0),
.last 30 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 36, 36, 64],[16, 64, 32, 1, 8, 4, 64],64⟩,
.cycle 0 31 true (0),
.cycle 0 70 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 32, 36, 64],[16, 64, 32, 1, 8, 32, 64],64⟩
])
])
theorem kid21_part283_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid21_part283) = true := by rfl

def kid21_part284 : Audit := .cycle 0 16 true (0)
theorem kid21_part284_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid21_part284) = true := by rfl

def kid21_part285 : Audit := .cycle 5 16 true (0)
theorem kid21_part285_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid21_part285) = true := by rfl

def kid21_part286 : Audit := .split 21 (1,true) (byMove [
.cycle 30 1 false (2),
.cycle 1 22 true (0),
.split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 34 1 false (4),
.cycle 28 1 false (2),
.last 24 (5,true),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 26 20 true (2),
.cycle 40 1 false (4),
.cycle 0 30 true (0),
.cycle 30 1 false (2),
.cycle 34 1 false (4),
.cycle 33 1 false (3),
.cycle 31 1 false (1),
.cycle 0 25 true (0),
.cycle 32 1 false (4),
.last 24 (5,true),
.cycle 29 1 false (1),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 50 1 false (4),
.cycle 42 1 false (6),
.last 24 (5,true),
.cycle 0 25 true (0)
]),
.cycle 0 23 true (0),
.cycle 42 1 false (6),
.split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 34 1 false (4),
.cycle 28 1 false (2),
.cycle 27 1 false (-1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 26 20 true (2),
.cycle 40 1 false (4),
.cycle 0 30 true (0),
.cycle 30 1 false (2),
.cycle 34 1 false (4),
.cycle 33 1 false (3),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 32 1 false (4),
.cycle 27 1 false (-1),
.cycle 29 1 false (1),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 50 1 false (4),
.cycle 42 1 false (6),
.cycle 0 46 true (0),
.cycle 0 25 true (0)
]),
.cycle 0 22 true (0),
.cycle 66 1 false (4),
.cycle 0 30 true (0),
.cycle 48 1 false (4),
.cycle 19 5 true (3),
.cycle 42 1 false (6),
.cycle 6 16 true (0),
.split 24 (2,true) (byMove [
.cycle 37 1 false (1),
.cycle 26 3 false (2),
.cycle 28 1 false (2),
.cycle 19 6 true (3),
.cycle 4 22 true (0),
.last 25 (5,true),
.cycle 38 1 false (2),
.cycle 22 49 true (3),
.cycle 5 61 true (0),
.cycle 0 26 true (0),
.cycle 33 20 true (2),
.last 25 (5,true),
.cycle 0 28 true (0),
.cycle 26 3 false (2),
.cycle 0 32 true (0),
.cycle 5 20 true (0),
.cycle 40 1 false (2),
.last 25 (5,true),
.cycle 19 9 true (3),
.cycle 26 5 false (4),
.cycle 2 24 true (0),
.cycle 0 26 true (0),
.cycle 46 1 false (2),
.last 25 (5,true)
]),
.split 22 (2,true) (byMove [
.cycle 19 10 true (3),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 28 1 false (2),
.last 24 (5,true),
.last 28 (5,true),
.cycle 40 1 false (6),
.cycle 0 26 true (0),
.cycle 5 28 true (0),
.cycle 0 24 true (0),
.cycle 7 16 true (0),
.last 23 (5,true),
.cycle 37 1 false (3),
.cycle 43 1 false (3),
.cycle 42 1 false (6),
.cycle 0 28 true (0),
.last 24 (5,true),
.cycle 29 1 false (1),
.cycle 19 7 true (3),
.cycle 21 2 true (4),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.cycle 0 44 true (0),
.last 23 (5,true)
]),
.cycle 40 1 false (6),
.cycle 0 24 true (0),
.split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 28 1 false (2),
.cycle 27 1 false (-1),
.last 27 (2,true),
.cycle 40 1 false (6),
.cycle 30 1 false (2),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 7 16 true (0),
.cycle 0 32 true (0),
.cycle 37 1 false (3),
.last 24 (2,true),
.cycle 42 1 false (6),
.cycle 0 28 true (0),
.cycle 27 1 false (-1),
.cycle 29 1 false (1),
.cycle 19 7 true (3),
.cycle 21 2 true (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 0 44 true (0),
.cycle 0 26 true (0)
]),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 0 42 true (0),
.split 23 (5,true) (byMove [
.cycle 32 1 false (2),
.cycle 35 20 true (2),
.last 24 (2,true),
.cycle 19 5 true (3),
.cycle 50 1 false (4),
.cycle 0 31 true (0),
.cycle 0 42 true (0),
.cycle 21 3 true (5),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 16 37 true (0),
.cycle 52 1 false (4),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.last 24 (2,true),
.cycle 48 1 false (4),
.cycle 0 44 true (0),
.cycle 0 31 true (0),
.cycle 19 8 true (3),
.cycle 21 3 true (5),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 58 1 false (6),
.cycle 0 27 true (0)
]),
.cycle 0 24 true (0)
])
theorem kid21_part286_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid21_part286) = true := by rfl

def kid21_part288 : Audit := .split 19 (2,true) (byMove [
.cycle 39 2 false (7),
.last 20 (1,true),
.cycle 23 1 false (-1),
.cycle 0 29 true (-1),
.cycle 13 11 false (3),
.cycle 22 2 false (0),
.last 21 (1,true),
.far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 6, 4, 6, 6, 2, 3, 6, 6],[4096, 34359738368, 2097152, 512, 2048, 16, 4398046511104, 34359738368, 4096, 2097152, 8388608, 65536, 4096, 5497558138880, 134217728, 8589934592, 34359738368, 268435456, 4398046511104, 4398046511104, 1099511693312, 134217728, 536870912, 1099511627776, 7799660679168, 5497558142976, 2162688, 549755813888, 2199023255552, 1099511627776, 4398046511104, 34359738368, 4398046511104, 2097152, 8388608, 65536, 7799660679168, 7799660679168, 8349416493056, 549755813888, 2199023255552, 1099511627776, 4398046511104],[65536, 4398046511104, 65536, 4096, 34359738368, 1, 65536, 4398046511104, 4398046511104, 34359738368, 1099511627776, 4096, 1099511627776, 4398046511104, 65536, 4398046511104, 34359738368, 16777216, 6597069766656, 4398046511104, 4398046511104, 34359738368, 68719480832, 68719476736, 7799660679168, 4398046511104, 6597069766656, 5497558142976, 2199023259648, 68719476736, 65536, 4398046511104, 4398046511104, 2199023255552, 4398046511104, 4096, 7799660679168, 4398046511104, 7799660679168, 7799660679168, 7799660679168, 68719476736, 4398046511104],4884502683712⟩,
.last 23 (1,true),
.last 27 (1,true),
.last 29 (1,true),
.cycle 24 2 false (0),
.cycle 61 2 false (9),
.last 20 (1,true),
.cycle 37 2 false (7),
.cycle 13 9 false (3),
.last 23 (1,true),
.cycle 22 2 false (0),
.last 21 (1,true),
.last 50 (1,true),
.last 23 (1,true),
.cycle 40 2 false (0),
.cycle 5 44 true (-1),
.cycle 42 2 false (0)
])
theorem kid21_part288_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part288) = true := by rfl

def kid21_part289 : Audit := .split 21 (1,true) (byMove [
.cycle 43 2 false (7),
.cycle 65 2 false (9),
.last 22 (2,true),
.last 25 (2,true),
.cycle 7 15 false (5),
.cycle 65 2 false (9),
.cycle 0 24 true (-1),
.last 23 (2,true),
.cycle 0 24 true (-1),
.cycle 0 28 true (-1),
.cycle 0 30 true (-1),
.cycle 0 36 true (-1),
.cycle 59 2 false (9),
.last 24 (2,true),
.last 22 (2,true),
.cycle 9 13 false (5),
.cycle 0 28 true (-1),
.cycle 0 32 true (-1),
.cycle 20 24 true (2),
.last 23 (2,true),
.cycle 0 24 true (-1),
.cycle 4 18 true (-1),
.cycle 91 2 false (11),
.cycle 4 20 true (-1)
])
theorem kid21_part289_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part289) = true := by rfl

def kid21_part290 : Audit := .cycle 18 1 false (0)
theorem kid21_part290_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part290) = true := by rfl

def kid21_part291 : Audit := .cycle 17 1 false (-1)
theorem kid21_part291_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part291) = true := by rfl

def kid21_part292 : Audit := .cycle 17 2 false (-1)
theorem kid21_part292_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part292) = true := by rfl

def kid21_part293 : Audit := .cycle 17 2 false (-1)
theorem kid21_part293_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part293) = true := by rfl

def kid21_part294 : Audit := .cycle 18 2 false (2)
theorem kid21_part294_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part294) = true := by rfl

def kid21_part295 : Audit := .split 17 (1,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 529, 513, 152, 128, 256, 8, 16, 256, 16, 4096],[16, 256, 4096, 1, 512, 2, 16, 513, 4096, 1, 512, 2, 4096],4096⟩,
.cycle 1 28 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 0 30 true (0),
.cycle 18 1 false (2),
.cycle 18 2 false (2),
.cycle 18 2 false (2),
.cycle 33 2 false (7),
.last 19 (2,true),
.last 22 (2,true),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 2 20 true (0),
.cycle 29 2 false (7),
.cycle 4 18 true (0),
.cycle 31 2 false (7)
])
theorem kid21_part295_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part295) = true := by rfl

def kid21_part296 : Audit := .split 17 (2,true) (byMove [
.last 23 (1,true),
.last 27 (1,true),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.last 19 (1,true),
.cycle 88 2 false (14),
.last 21 (1,true),
.cycle 18 1 false (2),
.cycle 18 2 false (2),
.cycle 18 2 false (2),
.last 19 (1,true),
.last 20 (1,true),
.last 21 (1,true),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.last 19 (1,true),
.cycle 1 21 true (0),
.last 21 (1,true),
.cycle 29 2 false (7),
.cycle 4 18 true (0),
.cycle 31 2 false (7)
])
theorem kid21_part296_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part296) = true := by rfl

def kid21_part297 : Audit := .split 19 (1,true) (byMove [
.cycle 21 2 false (3),
.cycle 35 2 false (7),
.last 20 (2,true),
.last 23 (2,true),
.cycle 24 2 false (4),
.cycle 21 1 false (3),
.cycle 0 22 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.cycle 29 2 false (7),
.last 22 (2,true),
.last 20 (2,true),
.cycle 22 2 false (4),
.cycle 0 26 true (0),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (0),
.cycle 40 2 false (8),
.cycle 4 18 true (0)
])
theorem kid21_part297_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part297) = true := by rfl

def kid21_part298 : Audit := .cycle 29 2 false (7)
theorem kid21_part298_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part298) = true := by rfl

def kid21_part299 : Audit := .cycle 18 2 false (2)
theorem kid21_part299_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part299) = true := by rfl

def kid21_part300 : Audit := .split 18 (1,true) (byMove [
.cycle 20 2 false (0),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 1, 2, 3],[128, 256, 8, 4624, 512, 16, 524288, 1048576, 32768, 16, 4608, 16, 128, 256, 8, 512, 512, 144, 524288, 1048576, 32768, 16, 4096, 16, 16777216],[16, 32768, 16777216, 1, 512, 512, 65536, 512, 16777216, 4096, 2097152, 512, 16, 32768, 16777216, 1, 512, 528, 65536, 528, 16777216, 4096, 2097152, 512, 16777216],16777216⟩,
.last 19 (2,true),
.last 25 (2,true),
.cycle 35 2 false (7),
.cycle 16 3 false (0),
.cycle 13 7 false (3),
.last 21 (2,true),
.last 19 (2,true),
.cycle 0 28 true (-1),
.cycle 59 2 false (9),
.cycle 0 60 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 25, 27, 64],[16, 8, 64, 1, 8, 8, 64],64⟩,
.last 21 (2,true),
.last 19 (2,true),
.cycle 33 2 false (7),
.cycle 13 9 false (3),
.cycle 16 3 false (0),
.cycle 28 24 true (4),
.last 21 (2,true),
.last 19 (2,true),
.cycle 4 18 true (-1),
.cycle 0 62 true (-1),
.cycle 61 2 false (9)
])
theorem kid21_part300_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part300) = true := by rfl

def kid21_part301 : Audit := .split 18 (2,true) (byMove [
.cycle 20 2 false (0),
.last 19 (1,true),
.cycle 21 1 false (-1),
.last 21 (1,true),
.cycle 35 2 false (7),
.cycle 16 3 false (0),
.cycle 13 7 false (3),
.last 19 (1,true),
.last 23 (1,true),
.last 21 (1,true),
.cycle 59 2 false (9),
.last 25 (1,true),
.last 23 (1,true),
.last 19 (1,true),
.cycle 35 2 false (7),
.cycle 33 2 false (7),
.cycle 13 9 false (3),
.cycle 16 3 false (0),
.last 29 (1,true),
.last 19 (1,true),
.last 23 (1,true),
.last 21 (1,true),
.last 39 (1,true),
.last 20 (1,true)
])
theorem kid21_part301_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part301) = true := by rfl

def kid21_part302 : Audit := .cycle 20 2 false (2)
theorem kid21_part302_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part302) = true := by rfl

def kid21_part303 : Audit := .cycle 17 1 false (-1)
theorem kid21_part303_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part303) = true := by rfl

def kid21_part304 : Audit := .cycle 17 2 false (-1)
theorem kid21_part304_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part304) = true := by rfl

def kid21_part305 : Audit := .cycle 17 2 false (-1)
theorem kid21_part305_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part305) = true := by rfl

def kid21_part306 : Audit := .split 27 (1,true) (byMove [
.cycle 0 42 true (0),
.cycle 1 28 true (0),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 48 2 false (8),
.cycle 0 29 true (0),
.cycle 0 28 true (0),
.cycle 94 2 false (14),
.cycle 0 36 true (0),
.cycle 58 2 false (10),
.cycle 60 2 false (10),
.cycle 64 2 false (10),
.cycle 6 22 true (0),
.last 30 (2,true),
.last 28 (2,true),
.cycle 46 2 false (8),
.cycle 0 30 true (0),
.cycle 62 2 false (10),
.cycle 0 28 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.cycle 0 44 true (0),
.cycle 4 30 true (0),
.cycle 0 46 true (0)
])
theorem kid21_part306_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part306) = true := by rfl

def kid21_part307 : Audit := .split 17 (1,true) (byMove [
.cycle 19 2 false (1),
.cycle 37 2 false (7),
.last 18 (2,true),
.last 21 (2,true),
.cycle 22 2 false (2),
.cycle 1 24 true (0),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 0 30 true (0),
.cycle 56 2 false (10),
.cycle 60 2 false (10),
.cycle 14 4 true (0),
.cycle 31 2 false (7),
.last 20 (2,true),
.last 18 (2,true),
.cycle 20 2 false (2),
.cycle 0 28 true (0),
.cycle 16 2 true (0),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 2 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 25, 27, 64],[16, 8, 64, 1, 8, 2, 64],64⟩,
.cycle 4 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 529, 512, 16, 128, 256, 8, 16, 2048, 16, 4096],[16, 2048, 4096, 1, 512, 128, 16, 2048, 4096, 1, 512, 128, 4096],4096⟩
])
theorem kid21_part307_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part307) = true := by rfl

def kid21_part308 : Audit := .split 17 (2,true) (byMove [
.cycle 19 2 false (1),
.last 18 (1,true),
.cycle 20 1 false (0),
.cycle 0 27 true (0),
.cycle 22 2 false (2),
.last 27 (1,true),
.last 19 (1,true),
.cycle 134 2 false (16),
.last 21 (1,true),
.last 25 (1,true),
.last 27 (1,true),
.cycle 14 4 true (0),
.cycle 31 2 false (7),
.last 18 (1,true),
.cycle 22 2 false (2),
.cycle 20 2 false (2),
.last 21 (1,true),
.cycle 16 2 true (0),
.last 19 (1,true),
.cycle 1 21 true (0),
.last 21 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 529, 512, 16, 128, 256, 8, 16, 512, 16, 4096],[16, 4096, 512, 1, 512, 256, 16, 4096, 512, 1, 512, 256, 4096],4096⟩,
.cycle 4 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 529, 512, 16, 128, 256, 8, 16, 2048, 16, 4096],[16, 4096, 2048, 1, 512, 256, 16, 4096, 2048, 1, 512, 256, 4096],4096⟩
])
theorem kid21_part308_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part308) = true := by rfl

def kid21_part309 : Audit := .split 19 (1,true) (byMove [
.cycle 13 8 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 529, 529, 657, 8192, 16384, 8, 16, 1, 16, 8192, 16384, 8, 16, 1, 16, 262144],[16, 8, 262144, 1, 512, 512, 16, 529, 262144, 1, 32768, 32768, 16, 17049, 262144, 1, 32768, 32768, 262144],262144⟩,
.last 20 (2,true),
.last 23 (2,true),
.cycle 0 38 true (0),
.cycle 0 38 true (0),
.cycle 0 22 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 25, 27, 64],[16, 8, 64, 1, 8, 8, 64],64⟩,
.last 22 (2,true),
.last 20 (2,true),
.cycle 0 36 true (0),
.cycle 0 26 true (0),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (0),
.cycle 0 34 true (0),
.cycle 4 18 true (0)
])
theorem kid21_part309_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part309) = true := by rfl

def kid21_part310 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 529, 512, 16, 128, 256, 8, 16, 512, 16, 4096],[16, 4096, 4096, 1, 512, 1024, 16, 4096, 4096, 1, 512, 1024, 4096],4096⟩
theorem kid21_part310_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part310) = true := by rfl

def kid21_part311 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 529, 512, 16, 128, 256, 8, 16, 2048, 16, 4096],[16, 4096, 4096, 1, 512, 2048, 16, 4096, 4096, 1, 512, 2048, 4096],4096⟩
theorem kid21_part311_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part311) = true := by rfl

def kid21_part287 : Audit := .split 16 (5,true) (byMove [(kid21_part288),(kid21_part289),(kid21_part290),(kid21_part291),(kid21_part292),(kid21_part293),(kid21_part294),(kid21_part295),(kid21_part296),(kid21_part297),(kid21_part298),(kid21_part299),(kid21_part300),(kid21_part301),(kid21_part302),(kid21_part303),(kid21_part304),(kid21_part305),(kid21_part306),(kid21_part307),(kid21_part308),(kid21_part309),(kid21_part310),(kid21_part311)])

theorem kid21_part287_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid21_part287) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 16 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (5,true) (some mv)) (byMove [(kid21_part288),(kid21_part289),(kid21_part290),(kid21_part291),(kid21_part292),(kid21_part293),(kid21_part294),(kid21_part295),(kid21_part296),(kid21_part297),(kid21_part298),(kid21_part299),(kid21_part300),(kid21_part301),(kid21_part302),(kid21_part303),(kid21_part304),(kid21_part305),(kid21_part306),(kid21_part307),(kid21_part308),(kid21_part309),(kid21_part310),(kid21_part311)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part288_checked

  · exact kid21_part294_checked

  · exact kid21_part300_checked

  · exact kid21_part306_checked

  · exact kid21_part289_checked

  · exact kid21_part295_checked

  · exact kid21_part301_checked

  · exact kid21_part307_checked

  · exact kid21_part290_checked

  · exact kid21_part296_checked

  · exact kid21_part302_checked

  · exact kid21_part308_checked

  · exact kid21_part291_checked

  · exact kid21_part297_checked

  · exact kid21_part303_checked

  · exact kid21_part309_checked

  · exact kid21_part292_checked

  · exact kid21_part298_checked

  · exact kid21_part304_checked

  · exact kid21_part310_checked

  · exact kid21_part293_checked

  · exact kid21_part299_checked

  · exact kid21_part305_checked

  · exact kid21_part311_checked

def kid21_part312 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (5),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 26 true (0),
.cycle 32 1 false (6),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.split 18 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 31 1 false (1),
.last 19 (2,true),
.proven (BB6.Agent11Raw39B0RECounter2293.M2293.table) (fun m hm => BB6.Agent11Raw39B0RECounter2293.M2293.never m hm),
.cycle 24 1 false (0),
.cycle 16 3 false (0),
.cycle 0 28 true (-1),
.cycle 36 19 false (4),
.last 29 (2,true),
.cycle 28 1 false (2),
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.cycle 25 1 false (1),
.last 21 (2,true),
.last 19 (2,true),
.cycle 22 1 false (0),
.cycle 0 30 true (-1),
.cycle 16 3 false (0),
.cycle 0 28 true (-1),
.cycle 47 1 false (1),
.cycle 2 17 false (5),
.cycle 14 9 false (2),
.cycle 0 28 true (-1),
.cycle 27 1 false (1)
]),
.split 18 (2,true) (byMove [
.cycle 21 1 false (-1),
.last 19 (1,true),
.cycle 21 1 false (-1),
.proven (BB6.Agent11Raw39B0RECounter2294.M2294.table) (fun m hm => BB6.Agent11Raw39B0RECounter2294.M2294.never m hm),
.cycle 24 1 false (0),
.cycle 16 3 false (0),
.cycle 0 28 true (-1),
.cycle 36 19 false (4),
.cycle 0 38 true (-1),
.cycle 28 1 false (2),
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.cycle 25 1 false (1),
.last 19 (1,true),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 0 30 true (-1),
.cycle 16 3 false (0),
.cycle 0 28 true (-1),
.last 41 (1,true),
.cycle 2 17 false (5),
.cycle 14 9 false (2),
.last 21 (1,true),
.last 21 (1,true)
]),
.cycle 0 28 true (-1),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 26 true (0),
.proven (BB6.Agent11Raw39B0RECounter2295.M2295.table) (fun m hm => BB6.Agent11Raw39B0RECounter2295.M2295.never m hm),
.cycle 27 1 false (3),
.cycle 21 1 false (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 2, 1],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 4194320, 512, 512, 524288, 1048576, 2097152, 6296064, 4096, 4194320, 128, 256, 32768, 4264448, 512, 512, 16777216],[16, 16777216, 16777216, 1, 512, 1024, 65536, 16777216, 16777216, 4096, 512, 1024, 4194304, 16777216, 16777216, 262144, 2097152, 4194304, 65536, 16777216, 16777216, 4096, 512, 1024, 16777216],16777216⟩,
.cycle 15 2 true (0)
])
theorem kid21_part312_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid21_part312) = true := by rfl

def kid21_part313 : Audit := .cycle 10 3 true (4)
theorem kid21_part313_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid21_part313) = true := by rfl

def kid21_part314 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 18 true (0),
.cycle 37 1 false (5),
.split 24 (5,true) (byMove [
.last 27 (2,true),
.cycle 0 28 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.last 27 (2,true),
.cycle 26 3 false (2),
.cycle 25 3 false (1),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 29 3 false (3),
.cycle 37 3 false (7),
.cycle 35 3 false (3),
.last 26 (2,true),
.cycle 28 3 false (2),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.cycle 25 3 false (0),
.cycle 20 6 true (0),
.cycle 30 3 false (2),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 17 12 true (0),
.cycle 11 29 true (0)
]),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 37 true (0),
.cycle 0 27 true (0),
.cycle 11 3 true (4),
.cycle 1 14 true (1),
.cycle 6 10 true (2),
.split 15 (2,true) (byMove [
.cycle 10 6 true (4),
.cycle 26 3 false (0),
.cycle 49 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 1 16 true (1),
.cycle 6 10 true (2),
.cycle 26 3 false (0),
.cycle 9 9 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 1 16 true (1)
]),
.cycle 0 16 true (0),
.cycle 5 16 true (0),
.split 24 (5,true) (byMove [
.last 27 (2,true),
.cycle 5 65 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.last 27 (2,true),
.cycle 5 22 true (0),
.cycle 25 3 false (1),
.last 25 (2,true),
.cycle 44 3 false (8),
.cycle 0 30 true (0),
.cycle 41 3 false (11),
.cycle 5 26 true (-1),
.last 26 (2,true),
.cycle 5 24 true (-1),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.cycle 25 3 false (0),
.cycle 5 22 true (0),
.cycle 5 37 true (0),
.last 25 (2,true),
.cycle 5 33 true (0),
.cycle 0 30 true (0),
.cycle 24 34 true (0)
]),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.cycle 95 5 true (13),
.cycle 31 5 false (1),
.last 18 (2,true),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 1 17 true (1),
.cycle 7 11 true (3),
.last 17 (2,true),
.cycle 9 8 true (3),
.cycle 0 27 true (0),
.cycle 0 21 true (0),
.cycle 7 11 true (3),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 1 17 true (1)
]),
.cycle 1 14 true (1)
])
theorem kid21_part314_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid21_part314) = true := by rfl

def kid21_part315 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 18 true (0),
.cycle 37 1 false (5),
.split 24 (5,true) (byMove [
.cycle 17 15 false (3),
.cycle 0 28 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.cycle 0 28 true (-1),
.cycle 26 3 false (2),
.last 25 (1,true),
.cycle 25 3 false (1),
.cycle 0 26 true (0),
.cycle 29 3 false (3),
.cycle 28 1 false (4),
.last 26 (1,true),
.cycle 35 3 false (3),
.cycle 28 3 false (2),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.cycle 25 3 false (0),
.cycle 20 6 true (0),
.last 25 (1,true),
.cycle 30 3 false (2),
.cycle 0 26 true (0),
.cycle 17 12 true (0),
.cycle 0 35 true (0)
]),
.cycle 0 29 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 37 true (0),
.cycle 0 27 true (0),
.cycle 11 3 true (4),
.cycle 5 25 true (0),
.split 15 (1,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 33 3 false (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 9 16 true (3),
.cycle 6 10 true (2),
.cycle 0 22 true (0),
.cycle 0 32 true (0),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 0 25 true (0)
]),
.split 16 (1,true) (byMove [
.cycle 47 11 false (2),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.cycle 0 27 true (0),
.last 24 (5,true),
.cycle 0 20 true (0),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 22 true (0),
.cycle 26 3 false (0),
.cycle 9 9 true (3),
.cycle 5 18 true (0),
.last 24 (5,true),
.last 32 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 15 2 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.cycle 0 16 true (0),
.cycle 5 16 true (0),
.split 24 (5,true) (byMove [
.cycle 76 3 false (0),
.cycle 5 65 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.cycle 48 3 false (8),
.cycle 5 22 true (0),
.last 25 (1,true),
.cycle 25 3 false (1),
.cycle 44 3 false (8),
.cycle 0 30 true (0),
.cycle 32 1 false (8),
.last 26 (1,true),
.cycle 5 26 true (-1),
.cycle 5 24 true (-1),
.cycle 25 1 false (-1),
.cycle 25 3 false (-1),
.cycle 25 3 false (0),
.cycle 5 22 true (0),
.last 25 (1,true),
.cycle 5 37 true (0),
.cycle 5 33 true (0),
.cycle 0 30 true (0),
.cycle 0 39 true (0)
]),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.split 15 (5,true) (byMove [
.cycle 7 18 true (3),
.cycle 0 19 true (0),
.cycle 0 29 true (0),
.last 97 (1,true),
.cycle 31 5 false (1),
.cycle 0 19 true (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 0 38 true (0),
.last 17 (1,true),
.cycle 7 11 true (3),
.cycle 9 8 true (3),
.cycle 0 27 true (0),
.cycle 0 21 true (0),
.cycle 7 11 true (3),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 0 26 true (0)
]),
.cycle 0 23 true (0)
])
theorem kid21_part315_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid21_part315) = true := by rfl

def kid21_part316 : Audit := .cycle 0 14 true (0)
theorem kid21_part316_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid21_part316) = true := by rfl

def kid21_part317 : Audit := .cycle 7 6 true (3)
theorem kid21_part317_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid21_part317) = true := by rfl

def kid21_part318 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 18 true (0),
.cycle 37 1 false (5),
.cycle 24 3 false (0),
.cycle 14 1 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 37 true (0),
.cycle 0 27 true (0),
.cycle 11 3 true (4),
.cycle 14 1 true (6),
.split 15 (1,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 33 3 false (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 16 1 true (6),
.cycle 6 10 true (2),
.last 18 (2,true),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 0 32 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 0 21 true (0),
.cycle 16 1 true (6)
]),
.split 15 (2,true) (byMove [
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 49 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 26 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 16 1 true (6),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 9 9 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 26 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 18 (1,true),
.cycle 16 1 true (6)
]),
.cycle 0 16 true (0),
.cycle 5 16 true (0),
.cycle 24 3 false (0),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.cycle 7 9 true (3),
.cycle 14 1 true (6)
])
theorem kid21_part318_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid21_part318) = true := by rfl

def kid21_part320 : Audit := .cycle 0 34 true (0)
theorem kid21_part320_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid21_part320) = true := by rfl

def kid21_part321 : Audit := .cycle 0 24 true (0)
theorem kid21_part321_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid21_part321) = true := by rfl

def kid21_part322 : Audit := .split 15 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.cycle 42 1 false (4),
.cycle 29 1 false (1),
.last 43 (5,true),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 34 true (0),
.cycle 12 4 true (3),
.cycle 29 3 false (2),
.cycle 37 1 false (1),
.cycle 0 23 true (0),
.cycle 37 1 false (3),
.last 33 (5,true),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 0 20 true (0)
])
theorem kid21_part322_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid21_part322) = true := by rfl

def kid21_part323 : Audit := .cycle 0 19 true (0)
theorem kid21_part323_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid21_part323) = true := by rfl

def kid21_part324 : Audit := .cycle 4 12 true (1)
theorem kid21_part324_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid21_part324) = true := by rfl

def kid21_part325 : Audit := .split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.cycle 42 1 false (4),
.cycle 29 1 false (1),
.last 23 (2,true),
.cycle 20 4 false (0),
.cycle 0 19 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 34 true (0),
.cycle 12 4 true (3),
.cycle 29 3 false (2),
.last 17 (2,true),
.cycle 0 23 true (0),
.cycle 37 1 false (3),
.cycle 33 5 false (1),
.cycle 20 4 false (0),
.cycle 0 19 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 20 true (0),
.cycle 0 20 true (0)
])
theorem kid21_part325_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid21_part325) = true := by rfl

def kid21_part326 : Audit := .cycle 10 5 true (3)
theorem kid21_part326_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid21_part326) = true := by rfl

def kid21_part327 : Audit := .cycle 1 15 true (1)
theorem kid21_part327_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid21_part327) = true := by rfl

def kid21_part328 : Audit := .split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 6 11 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 9 15 true (3),
.cycle 0 23 true (0),
.cycle 11 5 true (3),
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 14 4 true (4),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 0 20 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 6 11 true (2)
])
theorem kid21_part328_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid21_part328) = true := by rfl

def kid21_part329 : Audit := .cycle 0 16 true (0)
theorem kid21_part329_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid21_part329) = true := by rfl

def kid21_part330 : Audit := .cycle 7 8 true (3)
theorem kid21_part330_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid21_part330) = true := by rfl

def kid21_part331 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 23 3 true (3),
.cycle 6 11 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 9 15 true (3),
.cycle 0 23 true (0),
.cycle 11 5 true (3),
.cycle 16 3 true (5),
.cycle 16 3 true (4),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 26 true (0),
.cycle 0 20 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.cycle 6 11 true (2)
])
theorem kid21_part331_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid21_part331) = true := by rfl

def kid21_part332 : Audit := .cycle 0 18 true (0)
theorem kid21_part332_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid21_part332) = true := by rfl

def kid21_part333 : Audit := .split 17 (2,true) (byMove [
.cycle 23 8 false (1),
.cycle 22 3 false (0),
.cycle 0 30 true (0),
.cycle 13 6 true (2),
.cycle 0 24 true (0),
.last 18 (5,true),
.cycle 6 12 true (2),
.cycle 1 23 true (1),
.cycle 5 24 true (1),
.cycle 9 9 true (2),
.cycle 0 20 true (0),
.last 18 (5,true),
.cycle 5 27 true (1),
.cycle 22 3 false (0),
.cycle 0 24 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (1),
.last 18 (5,true),
.cycle 6 12 true (2),
.cycle 24 5 false (2),
.cycle 2 18 true (1),
.cycle 0 33 true (0),
.cycle 0 20 true (0),
.last 18 (5,true)
])
theorem kid21_part333_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid21_part333) = true := by rfl

def kid21_part334 : Audit := .split 15 (2,true) (byMove [
.cycle 0 49 true (0),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.last 25 (5,true),
.last 20 (5,true),
.cycle 6 10 true (2),
.cycle 9 9 true (3),
.cycle 5 45 true (0),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 28 true (0),
.cycle 0 24 true (0),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.cycle 0 24 true (0),
.last 20 (5,true),
.cycle 6 10 true (2),
.cycle 14 2 true (3),
.cycle 2 16 true (1),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true)
])
theorem kid21_part334_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid21_part334) = true := by rfl

def kid21_part335 : Audit := .cycle 5 10 true (1)
theorem kid21_part335_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid21_part335) = true := by rfl

def kid21_part336 : Audit := .cycle 9 7 true (3)
theorem kid21_part336_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid21_part336) = true := by rfl

def kid21_part337 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.cycle 25 5 false (1),
.cycle 20 4 false (0),
.cycle 6 10 true (2),
.cycle 0 34 true (0),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 16 5 true (4),
.cycle 0 28 true (0),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.cycle 0 24 true (0),
.cycle 20 4 false (0),
.cycle 6 10 true (2),
.cycle 14 2 true (3),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 6 13 true (2)
])
theorem kid21_part337_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid21_part337) = true := by rfl

def kid21_part338 : Audit := .cycle 0 21 true (0)
theorem kid21_part338_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid21_part338) = true := by rfl

def kid21_part339 : Audit := .cycle 1 15 true (1)
theorem kid21_part339_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid21_part339) = true := by rfl

def kid21_part340 : Audit := .split 15 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 2 15 true (1),
.cycle 0 26 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 0 21 true (0),
.cycle 2 17 true (1),
.cycle 6 10 true (2),
.cycle 14 2 true (4),
.cycle 5 14 true (1),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 6 11 true (2)
])
theorem kid21_part340_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid21_part340) = true := by rfl

def kid21_part341 : Audit := .cycle 0 16 true (0)
theorem kid21_part341_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid21_part341) = true := by rfl

def kid21_part342 : Audit := .cycle 7 8 true (3)
theorem kid21_part342_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid21_part342) = true := by rfl

def kid21_part343 : Audit := .split 15 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 6 12 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 34 29 false (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 0 21 true (0),
.cycle 6 14 true (2),
.cycle 6 10 true (2),
.cycle 14 2 true (4),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 22 6 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.cycle 6 11 true (2)
])
theorem kid21_part343_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid21_part343) = true := by rfl

def kid21_part319 : Audit := .split 14 (1,true) (byMove [(kid21_part320),(kid21_part321),(kid21_part322),(kid21_part323),(kid21_part324),(kid21_part325),(kid21_part326),(kid21_part327),(kid21_part328),(kid21_part329),(kid21_part330),(kid21_part331),(kid21_part332),(kid21_part333),(kid21_part334),(kid21_part335),(kid21_part336),(kid21_part337),(kid21_part338),(kid21_part339),(kid21_part340),(kid21_part341),(kid21_part342),(kid21_part343)])

theorem kid21_part319_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid21_part319) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 14 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid21_part320),(kid21_part321),(kid21_part322),(kid21_part323),(kid21_part324),(kid21_part325),(kid21_part326),(kid21_part327),(kid21_part328),(kid21_part329),(kid21_part330),(kid21_part331),(kid21_part332),(kid21_part333),(kid21_part334),(kid21_part335),(kid21_part336),(kid21_part337),(kid21_part338),(kid21_part339),(kid21_part340),(kid21_part341),(kid21_part342),(kid21_part343)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part320_checked

  · exact kid21_part326_checked

  · exact kid21_part332_checked

  · exact kid21_part338_checked

  · exact kid21_part321_checked

  · exact kid21_part327_checked

  · exact kid21_part333_checked

  · exact kid21_part339_checked

  · exact kid21_part322_checked

  · exact kid21_part328_checked

  · exact kid21_part334_checked

  · exact kid21_part340_checked

  · exact kid21_part323_checked

  · exact kid21_part329_checked

  · exact kid21_part335_checked

  · exact kid21_part341_checked

  · exact kid21_part324_checked

  · exact kid21_part330_checked

  · exact kid21_part336_checked

  · exact kid21_part342_checked

  · exact kid21_part325_checked

  · exact kid21_part331_checked

  · exact kid21_part337_checked

  · exact kid21_part343_checked

def kid21_part345 : Audit := .split 28 (1,true) (byMove [
.cycle 23 7 false (2),
.cycle 5 75 true (-1),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 29 5 false (-1),
.cycle 29 5 false (-1),
.cycle 5 26 true (0),
.cycle 43 5 false (10),
.cycle 23 8 true (0),
.cycle 47 5 false (8),
.cycle 0 34 true (0),
.last 29 (5,true),
.cycle 5 45 true (-1),
.cycle 29 5 false (0),
.cycle 5 28 true (-1),
.cycle 29 1 false (-1),
.cycle 29 5 false (-1),
.cycle 29 5 false (-1),
.cycle 5 26 true (0),
.cycle 1 33 true (0),
.cycle 29 5 false (1),
.cycle 5 37 true (0),
.cycle 0 34 true (0),
.last 29 (5,true)
])
theorem kid21_part345_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid21_part345) = true := by rfl

def kid21_part346 : Audit := .split 15 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.cycle 1 26 true (0),
.cycle 29 1 false (1),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 0 18 true (0),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 34 true (0),
.cycle 12 4 true (3),
.cycle 4 16 true (1),
.cycle 22 3 false (0),
.cycle 0 24 true (0),
.cycle 47 1 false (5),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 0 18 true (0),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.last 18 (5,true)
])
theorem kid21_part346_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid21_part346) = true := by rfl

def kid21_part347 : Audit := .split 25 (1,true) (byMove [
.cycle 34 1 false (2),
.cycle 1 26 true (0),
.cycle 42 1 false (4),
.cycle 0 27 true (0),
.cycle 54 1 false (6),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 74 1 false (4),
.cycle 0 34 true (0),
.cycle 56 1 false (4),
.cycle 0 31 true (0),
.cycle 46 1 false (4),
.cycle 6 20 true (0),
.cycle 32 1 false (2),
.cycle 0 34 true (0),
.cycle 52 1 false (6),
.cycle 0 28 true (0),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 50 1 false (4),
.last 27 (5,true),
.last 28 (5,true)
])
theorem kid21_part347_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid21_part347) = true := by rfl

def kid21_part348 : Audit := .split 17 (1,true) (byMove [
.cycle 10 8 true (3),
.cycle 1 18 true (1),
.cycle 0 26 true (0),
.cycle 0 19 true (0),
.cycle 7 11 true (3),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 26 true (0),
.cycle 3 15 true (1),
.cycle 0 23 true (0),
.cycle 0 22 true (0),
.cycle 6 12 true (2),
.cycle 13 6 true (3),
.cycle 40 1 false (2),
.cycle 9 9 true (3),
.cycle 0 20 true (0),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 8 10 true (3),
.last 19 (5,true),
.last 20 (5,true)
])
theorem kid21_part348_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid21_part348) = true := by rfl

def kid21_part349 : Audit := .cycle 4 12 true (1)
theorem kid21_part349_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid21_part349) = true := by rfl

def kid21_part350 : Audit := .split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.last 25 (1,true),
.cycle 29 1 false (1),
.last 18 (1,true),
.cycle 20 4 false (0),
.last 17 (1,true),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 28 (1,true),
.cycle 12 4 true (3),
.last 17 (1,true),
.last 22 (1,true),
.last 19 (1,true),
.last 23 (1,true),
.last 18 (1,true),
.cycle 20 4 false (0),
.last 17 (1,true),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 20 true (0),
.last 17 (1,true)
])
theorem kid21_part350_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid21_part350) = true := by rfl

def kid21_part351 : Audit := .cycle 10 5 true (3)
theorem kid21_part351_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid21_part351) = true := by rfl

def kid21_part352 : Audit := .split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.cycle 1 22 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 9 15 true (3),
.cycle 0 23 true (0),
.cycle 11 5 true (3),
.cycle 1 18 true (1),
.cycle 6 12 true (2),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.last 24 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.last 18 (5,true)
])
theorem kid21_part352_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid21_part352) = true := by rfl

def kid21_part353 : Audit := .cycle 9 15 true (3)
theorem kid21_part353_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid21_part353) = true := by rfl

def kid21_part354 : Audit := .cycle 0 16 true (0)
theorem kid21_part354_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid21_part354) = true := by rfl

def kid21_part355 : Audit := .cycle 7 8 true (3)
theorem kid21_part355_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid21_part355) = true := by rfl

def kid21_part356 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 20 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 9 15 true (3),
.cycle 0 23 true (0),
.cycle 11 5 true (3),
.cycle 16 3 true (5),
.last 17 (1,true),
.cycle 16 3 true (4),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 20 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.last 17 (1,true)
])
theorem kid21_part356_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid21_part356) = true := by rfl

def kid21_part357 : Audit := .cycle 0 18 true (0)
theorem kid21_part357_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid21_part357) = true := by rfl

def kid21_part358 : Audit := .split 15 (1,true) (byMove [
.cycle 23 10 false (2),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 6 10 true (2),
.cycle 1 17 true (1),
.cycle 13 4 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 17 9 true (2),
.cycle 22 3 false (0),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.cycle 18 5 false (0),
.last 20 (5,true),
.cycle 6 10 true (2),
.cycle 1 17 true (1),
.cycle 14 2 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true)
])
theorem kid21_part358_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid21_part358) = true := by rfl

def kid21_part359 : Audit := .cycle 5 12 true (1)
theorem kid21_part359_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid21_part359) = true := by rfl

def kid21_part360 : Audit := .cycle 5 10 true (1)
theorem kid21_part360_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid21_part360) = true := by rfl

def kid21_part361 : Audit := .cycle 9 7 true (3)
theorem kid21_part361_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid21_part361) = true := by rfl

def kid21_part362 : Audit := .split 15 (5,true) (byMove [
.cycle 23 10 false (2),
.cycle 9 9 true (2),
.cycle 5 18 true (0),
.cycle 0 26 true (0),
.last 18 (1,true),
.cycle 20 4 false (0),
.cycle 6 10 true (2),
.last 16 (1,true),
.last 28 (1,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 16 5 true (4),
.last 17 (1,true),
.last 22 (1,true),
.cycle 5 12 true (1),
.cycle 5 16 true (0),
.last 18 (1,true),
.cycle 20 4 false (0),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 14 2 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 19 (1,true)
])
theorem kid21_part362_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid21_part362) = true := by rfl

def kid21_part363 : Audit := .split 18 (1,true) (byMove [
.cycle 0 27 true (0),
.cycle 0 51 true (0),
.cycle 0 26 true (0),
.cycle 0 26 true (0),
.cycle 0 25 true (0),
.last 19 (5,true),
.cycle 6 13 true (2),
.cycle 1 20 true (1),
.cycle 14 5 true (4),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.last 19 (5,true),
.cycle 9 12 true (3),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 5 15 true (1),
.last 19 (5,true),
.cycle 6 13 true (2),
.cycle 1 20 true (1),
.cycle 14 5 true (4),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.last 19 (5,true)
])
theorem kid21_part363_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid21_part363) = true := by rfl

def kid21_part364 : Audit := .split 15 (1,true) (byMove [
.cycle 31 18 false (3),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 0 21 true (0),
.cycle 1 18 true (1),
.cycle 6 10 true (2),
.cycle 26 5 false (2),
.cycle 14 2 true (4),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 17 (5,true),
.last 18 (5,true)
])
theorem kid21_part364_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid21_part364) = true := by rfl

def kid21_part365 : Audit := .cycle 2 14 true (1)
theorem kid21_part365_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid21_part365) = true := by rfl

def kid21_part366 : Audit := .cycle 0 16 true (0)
theorem kid21_part366_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid21_part366) = true := by rfl

def kid21_part367 : Audit := .cycle 7 8 true (3)
theorem kid21_part367_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid21_part367) = true := by rfl

def kid21_part368 : Audit := .split 15 (5,true) (byMove [
.last 19 (1,true),
.last 16 (1,true),
.last 18 (1,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 22 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.last 18 (1,true),
.last 20 (1,true),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 14 2 true (4),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 22 6 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.last 17 (1,true)
])
theorem kid21_part368_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid21_part368) = true := by rfl

def kid21_part344 : Audit := .split 14 (2,true) (byMove [(kid21_part345),(kid21_part346),(kid21_part347),(kid21_part348),(kid21_part349),(kid21_part350),(kid21_part351),(kid21_part352),(kid21_part353),(kid21_part354),(kid21_part355),(kid21_part356),(kid21_part357),(kid21_part358),(kid21_part359),(kid21_part360),(kid21_part361),(kid21_part362),(kid21_part363),(kid21_part364),(kid21_part365),(kid21_part366),(kid21_part367),(kid21_part368)])

theorem kid21_part344_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid21_part344) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid21_part345),(kid21_part346),(kid21_part347),(kid21_part348),(kid21_part349),(kid21_part350),(kid21_part351),(kid21_part352),(kid21_part353),(kid21_part354),(kid21_part355),(kid21_part356),(kid21_part357),(kid21_part358),(kid21_part359),(kid21_part360),(kid21_part361),(kid21_part362),(kid21_part363),(kid21_part364),(kid21_part365),(kid21_part366),(kid21_part367),(kid21_part368)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part345_checked

  · exact kid21_part351_checked

  · exact kid21_part357_checked

  · exact kid21_part363_checked

  · exact kid21_part346_checked

  · exact kid21_part352_checked

  · exact kid21_part358_checked

  · exact kid21_part364_checked

  · exact kid21_part347_checked

  · exact kid21_part353_checked

  · exact kid21_part359_checked

  · exact kid21_part365_checked

  · exact kid21_part348_checked

  · exact kid21_part354_checked

  · exact kid21_part360_checked

  · exact kid21_part366_checked

  · exact kid21_part349_checked

  · exact kid21_part355_checked

  · exact kid21_part361_checked

  · exact kid21_part367_checked

  · exact kid21_part350_checked

  · exact kid21_part356_checked

  · exact kid21_part362_checked

  · exact kid21_part368_checked

def kid21_part369 : Audit := .cycle 9 5 true (3)
theorem kid21_part369_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid21_part369) = true := by rfl

def kid21_part370 : Audit := .cycle 5 14 true (0)
theorem kid21_part370_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid21_part370) = true := by rfl

def kid21_part372 : Audit := .split 19 (2,true) (byMove [
.cycle 5 22 true (-1),
.last 20 (1,true),
.cycle 23 1 false (-1),
.last 22 (1,true),
.cycle 5 20 true (-1),
.cycle 22 2 false (0),
.cycle 48 2 false (0),
.last 20 (1,true),
.cycle 5 53 true (-1),
.cycle 0 24 true (-1),
.cycle 5 16 true (-1),
.cycle 0 39 true (-1),
.cycle 0 26 true (-1),
.last 20 (1,true),
.cycle 57 15 true (7),
.cycle 5 18 true (-1),
.cycle 52 2 false (0),
.cycle 22 2 false (0),
.cycle 0 45 true (-1),
.last 20 (1,true),
.cycle 0 50 true (-1),
.cycle 0 24 true (-1),
.cycle 0 44 true (-1),
.cycle 60 2 false (0)
])
theorem kid21_part372_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part372) = true := by rfl

def kid21_part373 : Audit := .cycle 5 41 true (-1)
theorem kid21_part373_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part373) = true := by rfl

def kid21_part374 : Audit := .cycle 18 1 false (0)
theorem kid21_part374_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part374) = true := by rfl

def kid21_part375 : Audit := .cycle 17 1 false (-1)
theorem kid21_part375_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part375) = true := by rfl

def kid21_part376 : Audit := .cycle 17 2 false (-1)
theorem kid21_part376_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part376) = true := by rfl

def kid21_part377 : Audit := .cycle 17 2 false (-1)
theorem kid21_part377_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part377) = true := by rfl

def kid21_part378 : Audit := .cycle 5 14 true (0)
theorem kid21_part378_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part378) = true := by rfl

def kid21_part379 : Audit := .split 17 (1,true) (byMove [
.last 20 (2,true),
.cycle 0 24 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.cycle 32 2 false (8),
.cycle 32 2 false (10),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 22 2 false (6),
.cycle 0 26 true (0),
.last 19 (2,true),
.cycle 36 2 false (8),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.cycle 0 41 true (0),
.cycle 1 21 true (0),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 0 25 true (0)
])
theorem kid21_part379_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part379) = true := by rfl

def kid21_part380 : Audit := .split 17 (2,true) (byMove [
.cycle 5 37 true (0),
.cycle 0 24 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.cycle 32 2 false (8),
.last 18 (1,true),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 22 2 false (6),
.last 19 (1,true),
.last 20 (1,true),
.cycle 36 2 false (8),
.cycle 18 1 false (0),
.cycle 18 2 false (0),
.cycle 18 2 false (0),
.cycle 0 41 true (0),
.last 18 (1,true),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 0 25 true (0)
])
theorem kid21_part380_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part380) = true := by rfl

def kid21_part381 : Audit := .cycle 32 2 false (8)
theorem kid21_part381_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part381) = true := by rfl

def kid21_part382 : Audit := .cycle 0 22 true (0)
theorem kid21_part382_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part382) = true := by rfl

def kid21_part383 : Audit := .cycle 22 2 false (6)
theorem kid21_part383_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part383) = true := by rfl

def kid21_part384 : Audit := .split 18 (1,true) (byMove [
.cycle 20 2 false (0),
.cycle 5 41 true (-2),
.last 19 (2,true),
.cycle 0 35 true (-1),
.cycle 0 28 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 27, 27, 64],[16, 2, 64, 1, 8, 10, 64],64⟩,
.last 19 (2,true),
.cycle 5 41 true (-1),
.cycle 0 24 true (-1),
.cycle 22 22 true (1),
.cycle 5 29 true (-1),
.last 21 (2,true),
.last 19 (2,true),
.cycle 0 26 true (-1),
.cycle 5 18 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.cycle 20 32 true (2),
.last 19 (2,true),
.cycle 19 25 true (1),
.cycle 0 24 true (-1),
.cycle 0 26 true (-1)
])
theorem kid21_part384_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part384) = true := by rfl

def kid21_part385 : Audit := .split 18 (2,true) (byMove [
.cycle 20 2 false (0),
.last 19 (1,true),
.cycle 21 1 false (-1),
.last 21 (1,true),
.cycle 0 28 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.last 19 (1,true),
.cycle 5 34 true (-1),
.cycle 5 41 true (-1),
.cycle 0 24 true (-1),
.last 37 (1,true),
.cycle 5 29 true (-1),
.last 19 (1,true),
.cycle 53 13 true (7),
.cycle 0 26 true (-1),
.cycle 5 18 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.last 19 (1,true),
.last 39 (1,true),
.last 42 (1,true),
.cycle 0 24 true (-1),
.last 20 (1,true)
])
theorem kid21_part385_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part385) = true := by rfl

def kid21_part386 : Audit := .cycle 5 16 true (-1)
theorem kid21_part386_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part386) = true := by rfl

def kid21_part387 : Audit := .cycle 17 1 false (-1)
theorem kid21_part387_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part387) = true := by rfl

def kid21_part388 : Audit := .cycle 17 2 false (-1)
theorem kid21_part388_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part388) = true := by rfl

def kid21_part389 : Audit := .cycle 17 2 false (-1)
theorem kid21_part389_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part389) = true := by rfl

def kid21_part390 : Audit := .cycle 5 14 true (0)
theorem kid21_part390_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part390) = true := by rfl

def kid21_part391 : Audit := .split 17 (1,true) (byMove [
.cycle 19 2 false (1),
.cycle 0 30 true (-1),
.last 18 (2,true),
.cycle 0 31 true (0),
.cycle 5 18 true (0),
.last 20 (2,true),
.cycle 6 21 true (0),
.cycle 0 53 true (0),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 1 26 true (0),
.cycle 0 24 true (0),
.last 20 (2,true),
.last 18 (2,true),
.cycle 5 16 true (0),
.cycle 5 25 true (0),
.cycle 16 2 true (0),
.cycle 0 41 true (0),
.cycle 1 21 true (0),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 0 25 true (0)
])
theorem kid21_part391_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part391) = true := by rfl

def kid21_part392 : Audit := .split 17 (2,true) (byMove [
.cycle 19 2 false (1),
.last 18 (1,true),
.cycle 20 1 false (0),
.last 20 (1,true),
.cycle 5 18 true (0),
.cycle 0 24 true (0),
.cycle 6 21 true (0),
.last 18 (1,true),
.cycle 5 49 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 5 41 true (0),
.cycle 0 24 true (0),
.last 18 (1,true),
.cycle 5 18 true (-1),
.cycle 5 16 true (0),
.cycle 5 25 true (0),
.cycle 16 2 true (0),
.cycle 0 41 true (0),
.last 18 (1,true),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 0 25 true (0)
])
theorem kid21_part392_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part392) = true := by rfl

def kid21_part393 : Audit := .cycle 5 21 true (0)
theorem kid21_part393_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part393) = true := by rfl

def kid21_part394 : Audit := .cycle 0 22 true (0)
theorem kid21_part394_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part394) = true := by rfl

def kid21_part395 : Audit := .cycle 0 25 true (0)
theorem kid21_part395_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part395) = true := by rfl

def kid21_part371 : Audit := .split 16 (5,true) (byMove [(kid21_part372),(kid21_part373),(kid21_part374),(kid21_part375),(kid21_part376),(kid21_part377),(kid21_part378),(kid21_part379),(kid21_part380),(kid21_part381),(kid21_part382),(kid21_part383),(kid21_part384),(kid21_part385),(kid21_part386),(kid21_part387),(kid21_part388),(kid21_part389),(kid21_part390),(kid21_part391),(kid21_part392),(kid21_part393),(kid21_part394),(kid21_part395)])

theorem kid21_part371_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid21_part371) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 16 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid21_part372),(kid21_part373),(kid21_part374),(kid21_part375),(kid21_part376),(kid21_part377),(kid21_part378),(kid21_part379),(kid21_part380),(kid21_part381),(kid21_part382),(kid21_part383),(kid21_part384),(kid21_part385),(kid21_part386),(kid21_part387),(kid21_part388),(kid21_part389),(kid21_part390),(kid21_part391),(kid21_part392),(kid21_part393),(kid21_part394),(kid21_part395)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part372_checked

  · exact kid21_part378_checked

  · exact kid21_part384_checked

  · exact kid21_part390_checked

  · exact kid21_part373_checked

  · exact kid21_part379_checked

  · exact kid21_part385_checked

  · exact kid21_part391_checked

  · exact kid21_part374_checked

  · exact kid21_part380_checked

  · exact kid21_part386_checked

  · exact kid21_part392_checked

  · exact kid21_part375_checked

  · exact kid21_part381_checked

  · exact kid21_part387_checked

  · exact kid21_part393_checked

  · exact kid21_part376_checked

  · exact kid21_part382_checked

  · exact kid21_part388_checked

  · exact kid21_part394_checked

  · exact kid21_part377_checked

  · exact kid21_part383_checked

  · exact kid21_part389_checked

  · exact kid21_part395_checked

def kid21_part397 : Audit := .split 19 (2,true) (byMove [
.cycle 15 7 false (1),
.last 20 (1,true),
.cycle 23 1 false (-1),
.last 22 (1,true),
.cycle 5 20 true (-1),
.cycle 23 1 false (-1),
.cycle 49 1 false (-1),
.last 20 (1,true),
.cycle 5 53 true (-1),
.cycle 0 24 true (-1),
.cycle 5 16 true (-1),
.cycle 41 1 false (-1),
.cycle 0 26 true (-1),
.last 20 (1,true),
.cycle 57 15 true (7),
.cycle 5 18 true (-1),
.cycle 53 1 false (-1),
.cycle 23 1 false (-1),
.cycle 51 1 false (-1),
.last 20 (1,true),
.cycle 49 1 false (-1),
.cycle 0 24 true (-1),
.cycle 39 1 false (-1),
.cycle 27 1 false (-1)
])
theorem kid21_part397_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part397) = true := by rfl

def kid21_part398 : Audit := .cycle 5 43 true (-1)
theorem kid21_part398_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part398) = true := by rfl

def kid21_part399 : Audit := .cycle 18 1 false (0)
theorem kid21_part399_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part399) = true := by rfl

def kid21_part400 : Audit := .cycle 17 1 false (-1)
theorem kid21_part400_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part400) = true := by rfl

def kid21_part401 : Audit := .cycle 18 1 false (-2)
theorem kid21_part401_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part401) = true := by rfl

def kid21_part402 : Audit := .cycle 17 1 false (-1)
theorem kid21_part402_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part402) = true := by rfl

def kid21_part403 : Audit := .cycle 5 14 true (0)
theorem kid21_part403_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part403) = true := by rfl

def kid21_part404 : Audit := .split 17 (1,true) (byMove [
.last 20 (2,true),
.cycle 0 24 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 33 1 false (7),
.cycle 33 1 false (9),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 22 1 false (6),
.cycle 0 26 true (0),
.last 19 (2,true),
.cycle 37 1 false (7),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 41 true (0),
.cycle 1 21 true (0),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 20 3 true (4)
])
theorem kid21_part404_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part404) = true := by rfl

def kid21_part405 : Audit := .split 17 (2,true) (byMove [
.cycle 15 8 true (0),
.cycle 0 24 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 33 1 false (7),
.last 18 (1,true),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 22 1 false (6),
.last 19 (1,true),
.last 20 (1,true),
.cycle 37 1 false (7),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 41 true (0),
.last 18 (1,true),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 20 3 true (4)
])
theorem kid21_part405_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part405) = true := by rfl

def kid21_part406 : Audit := .cycle 33 1 false (7)
theorem kid21_part406_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part406) = true := by rfl

def kid21_part407 : Audit := .cycle 0 22 true (0)
theorem kid21_part407_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part407) = true := by rfl

def kid21_part408 : Audit := .cycle 22 1 false (6)
theorem kid21_part408_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part408) = true := by rfl

def kid21_part409 : Audit := .split 18 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 5 41 true (-2),
.last 19 (2,true),
.cycle 0 35 true (-1),
.cycle 0 28 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 27, 27, 64],[16, 2, 64, 1, 8, 10, 64],64⟩,
.last 19 (2,true),
.cycle 5 43 true (-1),
.cycle 0 24 true (-1),
.cycle 22 22 true (1),
.cycle 5 29 true (-1),
.last 21 (2,true),
.last 19 (2,true),
.cycle 0 26 true (-1),
.cycle 5 18 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.cycle 20 32 true (2),
.last 19 (2,true),
.cycle 19 25 true (1),
.cycle 0 24 true (-1),
.cycle 0 26 true (-1)
])
theorem kid21_part409_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part409) = true := by rfl

def kid21_part410 : Audit := .split 18 (2,true) (byMove [
.cycle 21 1 false (-1),
.last 19 (1,true),
.cycle 21 1 false (-1),
.last 21 (1,true),
.cycle 0 28 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.last 19 (1,true),
.cycle 5 34 true (-1),
.cycle 5 43 true (-1),
.cycle 0 24 true (-1),
.last 37 (1,true),
.cycle 5 29 true (-1),
.last 19 (1,true),
.cycle 53 13 true (7),
.cycle 0 26 true (-1),
.cycle 5 18 true (-1),
.cycle 16 3 false (0),
.cycle 5 16 true (-1),
.last 19 (1,true),
.last 39 (1,true),
.last 42 (1,true),
.cycle 0 24 true (-1),
.last 20 (1,true)
])
theorem kid21_part410_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part410) = true := by rfl

def kid21_part411 : Audit := .cycle 5 16 true (-1)
theorem kid21_part411_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part411) = true := by rfl

def kid21_part412 : Audit := .cycle 17 1 false (-1)
theorem kid21_part412_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part412) = true := by rfl

def kid21_part413 : Audit := .cycle 18 1 false (-2)
theorem kid21_part413_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part413) = true := by rfl

def kid21_part414 : Audit := .cycle 17 1 false (-1)
theorem kid21_part414_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part414) = true := by rfl

def kid21_part415 : Audit := .cycle 5 14 true (0)
theorem kid21_part415_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part415) = true := by rfl

def kid21_part416 : Audit := .split 17 (1,true) (byMove [
.cycle 20 1 false (0),
.cycle 0 30 true (-1),
.last 18 (2,true),
.cycle 0 31 true (0),
.cycle 5 18 true (0),
.last 20 (2,true),
.cycle 6 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 2, 2, 64],[16, 2, 64, 1, 8, 2, 64],64⟩,
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 1 26 true (0),
.cycle 0 24 true (0),
.last 20 (2,true),
.last 18 (2,true),
.cycle 5 16 true (0),
.cycle 5 25 true (0),
.cycle 16 2 true (0),
.cycle 0 41 true (0),
.cycle 1 21 true (0),
.last 18 (2,true),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 20 3 true (4)
])
theorem kid21_part416_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part416) = true := by rfl

def kid21_part417 : Audit := .split 17 (2,true) (byMove [
.cycle 20 1 false (0),
.last 18 (1,true),
.cycle 20 1 false (0),
.last 20 (1,true),
.cycle 5 18 true (0),
.cycle 0 24 true (0),
.cycle 6 21 true (0),
.last 18 (1,true),
.cycle 5 49 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 24 22 true (4),
.cycle 0 24 true (0),
.last 18 (1,true),
.cycle 5 18 true (-1),
.cycle 5 16 true (0),
.cycle 5 25 true (0),
.cycle 16 2 true (0),
.cycle 0 41 true (0),
.last 18 (1,true),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.cycle 5 14 true (0),
.cycle 20 3 true (4)
])
theorem kid21_part417_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part417) = true := by rfl

def kid21_part418 : Audit := .cycle 5 21 true (0)
theorem kid21_part418_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part418) = true := by rfl

def kid21_part419 : Audit := .cycle 0 22 true (0)
theorem kid21_part419_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part419) = true := by rfl

def kid21_part420 : Audit := .cycle 20 3 true (4)
theorem kid21_part420_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part420) = true := by rfl

def kid21_part396 : Audit := .split 16 (5,true) (byMove [(kid21_part397),(kid21_part398),(kid21_part399),(kid21_part400),(kid21_part401),(kid21_part402),(kid21_part403),(kid21_part404),(kid21_part405),(kid21_part406),(kid21_part407),(kid21_part408),(kid21_part409),(kid21_part410),(kid21_part411),(kid21_part412),(kid21_part413),(kid21_part414),(kid21_part415),(kid21_part416),(kid21_part417),(kid21_part418),(kid21_part419),(kid21_part420)])

theorem kid21_part396_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid21_part396) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 16 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part397),(kid21_part398),(kid21_part399),(kid21_part400),(kid21_part401),(kid21_part402),(kid21_part403),(kid21_part404),(kid21_part405),(kid21_part406),(kid21_part407),(kid21_part408),(kid21_part409),(kid21_part410),(kid21_part411),(kid21_part412),(kid21_part413),(kid21_part414),(kid21_part415),(kid21_part416),(kid21_part417),(kid21_part418),(kid21_part419),(kid21_part420)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part397_checked

  · exact kid21_part403_checked

  · exact kid21_part409_checked

  · exact kid21_part415_checked

  · exact kid21_part398_checked

  · exact kid21_part404_checked

  · exact kid21_part410_checked

  · exact kid21_part416_checked

  · exact kid21_part399_checked

  · exact kid21_part405_checked

  · exact kid21_part411_checked

  · exact kid21_part417_checked

  · exact kid21_part400_checked

  · exact kid21_part406_checked

  · exact kid21_part412_checked

  · exact kid21_part418_checked

  · exact kid21_part401_checked

  · exact kid21_part407_checked

  · exact kid21_part413_checked

  · exact kid21_part419_checked

  · exact kid21_part402_checked

  · exact kid21_part408_checked

  · exact kid21_part414_checked

  · exact kid21_part420_checked

def kid21_part421 : Audit := .cycle 10 3 true (4)
theorem kid21_part421_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid21_part421) = true := by rfl

def kid21_part422 : Audit := .split 13 (1,true) (byMove [
.cycle 10 4 true (4),
.cycle 1 14 true (1),
.split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.last 20 (5,true),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 1 15 true (1),
.cycle 31 3 false (3),
.cycle 39 1 false (1),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.last 20 (5,true),
.last 24 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.last 16 (5,true),
.cycle 1 15 true (1)
]),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 20 4 false (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 1 15 true (1),
.cycle 31 3 false (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 20 4 false (0),
.cycle 24 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 10 true (3),
.cycle 1 15 true (1)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.cycle 11 3 true (4),
.cycle 1 14 true (1),
.cycle 6 8 true (2),
.split 16 (2,true) (byMove [
.cycle 35 7 false (1),
.cycle 24 3 false (0),
.cycle 34 1 false (2),
.cycle 13 6 true (3),
.cycle 4 14 true (1),
.last 17 (5,true),
.cycle 10 7 true (3),
.cycle 1 19 true (1),
.cycle 9 17 true (3),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 20 true (0),
.cycle 24 3 false (0),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.cycle 9 9 true (3),
.last 17 (5,true),
.cycle 0 29 true (0),
.cycle 28 5 false (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.split 14 (2,true) (byMove [
.cycle 48 13 false (2),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 32 1 false (2),
.last 20 (5,true),
.last 18 (5,true),
.cycle 10 5 true (4),
.cycle 0 18 true (0),
.cycle 5 41 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 0 30 true (0),
.cycle 5 14 true (1),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.last 20 (5,true),
.last 24 (5,true),
.cycle 10 5 true (4),
.cycle 13 2 true (4),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true)
]),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 32 1 false (2),
.cycle 20 4 false (0),
.last 17 (2,true),
.cycle 10 5 true (4),
.cycle 12 4 true (4),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 1 16 true (1),
.cycle 0 30 true (0),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.cycle 20 4 false (0),
.cycle 24 3 false (0),
.cycle 10 5 true (4),
.cycle 13 2 true (4),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 1 16 true (1)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.split 15 (5,true) (byMove [
.cycle 7 13 true (3),
.cycle 9 12 true (3),
.last 16 (2,true),
.cycle 13 5 true (4),
.cycle 4 13 true (1),
.cycle 0 21 true (0),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 1 17 true (1),
.cycle 0 19 true (0),
.cycle 0 19 true (0),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.cycle 0 21 true (0),
.cycle 10 6 true (4),
.cycle 13 3 true (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 1 17 true (1)
]),
.cycle 1 14 true (1)
])
theorem kid21_part422_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid21_part422) = true := by rfl

def kid21_part423 : Audit := .split 13 (2,true) (byMove [
.cycle 10 4 true (4),
.split 14 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.last 20 (5,true),
.cycle 2 14 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 2 14 true (1),
.cycle 6 11 true (2),
.cycle 24 3 false (0),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.last 20 (5,true),
.last 24 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.last 16 (5,true),
.cycle 2 14 true (1)
]),
.cycle 43 1 false (5),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 20 4 false (0),
.cycle 2 14 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 2 14 true (1),
.last 16 (1,true),
.last 24 (1,true),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 20 4 false (0),
.cycle 24 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 10 true (3),
.cycle 2 14 true (1)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.cycle 11 3 true (4),
.cycle 2 13 true (1),
.cycle 6 8 true (2),
.split 14 (1,true) (byMove [
.cycle 40 9 false (2),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 25 true (0),
.last 20 (5,true),
.cycle 0 18 true (0),
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.cycle 13 4 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 0 20 true (0),
.cycle 24 3 false (0),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.last 20 (5,true),
.last 24 (5,true),
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.cycle 13 2 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true)
]),
.cycle 9 7 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.split 14 (5,true) (byMove [
.cycle 40 9 false (2),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 23 (1,true),
.cycle 20 4 false (0),
.cycle 0 18 true (0),
.cycle 10 5 true (4),
.last 15 (1,true),
.cycle 12 4 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 2 15 true (1),
.last 16 (1,true),
.last 24 (1,true),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.cycle 20 4 false (0),
.cycle 24 3 false (0),
.cycle 10 5 true (4),
.last 15 (1,true),
.cycle 13 2 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 2 15 true (1)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.split 15 (5,true) (byMove [
.cycle 7 13 true (3),
.last 16 (1,true),
.cycle 0 31 true (0),
.last 18 (1,true),
.cycle 4 13 true (1),
.cycle 0 25 true (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 2 16 true (1),
.cycle 0 19 true (0),
.last 16 (1,true),
.cycle 0 19 true (0),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.cycle 0 21 true (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 13 3 true (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 2 16 true (1)
]),
.cycle 2 13 true (1)
])
theorem kid21_part423_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid21_part423) = true := by rfl

def kid21_part424 : Audit := .cycle 0 14 true (0)
theorem kid21_part424_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid21_part424) = true := by rfl

def kid21_part425 : Audit := .cycle 7 6 true (3)
theorem kid21_part425_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid21_part425) = true := by rfl

def kid21_part426 : Audit := .split 13 (5,true) (byMove [
.cycle 10 4 true (4),
.split 14 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 0 24 true (-1),
.cycle 15 1 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 15 1 true (5),
.cycle 6 11 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 0 43 true (-1),
.cycle 0 28 true (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 0 20 true (0),
.cycle 15 1 true (5)
]),
.split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 43 1 false (5),
.cycle 0 22 true (0),
.cycle 22 1 false (0),
.cycle 15 1 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (4),
.cycle 15 1 true (5),
.last 16 (1,true),
.last 17 (1,true),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.cycle 22 1 false (0),
.cycle 26 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 5 20 true (0),
.cycle 15 1 true (5)
]),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 15 1 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.cycle 11 3 true (4),
.cycle 14 1 true (6),
.cycle 6 8 true (2),
.split 14 (1,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.cycle 0 25 true (0),
.last 22 (2,true),
.last 21 (2,true),
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 17 (2,true),
.cycle 0 20 true (0),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.last 22 (2,true),
.last 26 (2,true),
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 13 2 true (4)
]),
.split 14 (2,true) (byMove [
.cycle 48 13 false (2),
.cycle 0 18 true (0),
.cycle 5 18 true (0),
.last 23 (1,true),
.cycle 24 4 false (2),
.last 23 (1,true),
.cycle 10 5 true (4),
.last 15 (1,true),
.cycle 5 41 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 0 18 true (0),
.last 16 (1,true),
.last 17 (1,true),
.cycle 9 7 true (3),
.cycle 5 16 true (0),
.cycle 5 20 true (-1),
.cycle 5 24 true (-1),
.cycle 10 5 true (4),
.last 15 (1,true),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 13 2 true (4)
]),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 23 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.cycle 7 9 true (3),
.cycle 14 1 true (6)
])
theorem kid21_part426_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid21_part426) = true := by rfl

def kid21_part282 : Audit := .split 12 (5,false) (byMove [(kid21_part283),(kid21_part284),(kid21_part285),(kid21_part286),(kid21_part287),(kid21_part312),(kid21_part313),(kid21_part314),(kid21_part315),(kid21_part316),(kid21_part317),(kid21_part318),(kid21_part319),(kid21_part344),(kid21_part369),(kid21_part370),(kid21_part371),(kid21_part396),(kid21_part421),(kid21_part422),(kid21_part423),(kid21_part424),(kid21_part425),(kid21_part426)])

theorem kid21_part282_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (kid21_part282) = true := by

  change (zipQueryOK 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid21_part283),(kid21_part284),(kid21_part285),(kid21_part286),(kid21_part287),(kid21_part312),(kid21_part313),(kid21_part314),(kid21_part315),(kid21_part316),(kid21_part317),(kid21_part318),(kid21_part319),(kid21_part344),(kid21_part369),(kid21_part370),(kid21_part371),(kid21_part396),(kid21_part421),(kid21_part422),(kid21_part423),(kid21_part424),(kid21_part425),(kid21_part426)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part283_checked

  · exact kid21_part313_checked

  · exact kid21_part319_checked

  · exact kid21_part421_checked

  · exact kid21_part284_checked

  · exact kid21_part314_checked

  · exact kid21_part344_checked

  · exact kid21_part422_checked

  · exact kid21_part285_checked

  · exact kid21_part315_checked

  · exact kid21_part369_checked

  · exact kid21_part423_checked

  · exact kid21_part286_checked

  · exact kid21_part316_checked

  · exact kid21_part370_checked

  · exact kid21_part424_checked

  · exact kid21_part287_checked

  · exact kid21_part317_checked

  · exact kid21_part371_checked

  · exact kid21_part425_checked

  · exact kid21_part312_checked

  · exact kid21_part318_checked

  · exact kid21_part396_checked

  · exact kid21_part426_checked

def kid21_part427 : Audit := .cycle 0 12 true (0)
theorem kid21_part427_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,0⟩)) (kid21_part427) = true := by rfl

def kid21_part428 : Audit := .cycle 1 11 true (1)
theorem kid21_part428_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,1⟩)) (kid21_part428) = true := by rfl

def kid21_part429 : Audit := .cycle 2 10 true (1)
theorem kid21_part429_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,2⟩)) (kid21_part429) = true := by rfl

def kid21_part430 : Audit := .cycle 8 4 true (3)
theorem kid21_part430_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,3⟩)) (kid21_part430) = true := by rfl

def kid21_part431 : Audit := .cycle 11 1 true (5)
theorem kid21_part431_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,4⟩)) (kid21_part431) = true := by rfl

def kid21_part433 : Audit := .cycle 10 3 true (4)
theorem kid21_part433_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid21_part433) = true := by rfl

def kid21_part434 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 18 true (0),
.cycle 37 1 false (5),
.cycle 30 3 false (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 37 true (0),
.cycle 0 27 true (0),
.cycle 11 3 true (5),
.cycle 1 14 true (1),
.cycle 6 10 true (2),
.split 15 (2,true) (byMove [
.cycle 10 6 true (4),
.cycle 26 3 false (0),
.cycle 49 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 1 16 true (1),
.cycle 6 10 true (2),
.cycle 26 3 false (0),
.cycle 9 9 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 0 25 true (0),
.last 21 (5,true)
]),
.cycle 0 16 true (0),
.cycle 5 16 true (0),
.split 15 (5,true) (byMove [
.cycle 10 6 true (4),
.cycle 0 28 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 1 16 true (1),
.cycle 6 10 true (2),
.cycle 5 37 true (0),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 9 11 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 0 21 true (0),
.cycle 0 20 true (0)
]),
.cycle 0 18 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (5),
.cycle 12 2 true (5)
])
theorem kid21_part434_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid21_part434) = true := by rfl

def kid21_part435 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 18 true (0),
.cycle 37 1 false (5),
.cycle 30 3 false (3),
.cycle 43 1 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 37 true (0),
.cycle 0 27 true (0),
.cycle 11 3 true (5),
.cycle 0 29 true (0),
.split 15 (1,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 33 3 false (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 2 15 true (1),
.cycle 6 10 true (2),
.cycle 0 22 true (0),
.cycle 0 32 true (0),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 13 true (2),
.cycle 6 12 true (2)
]),
.split 16 (1,true) (byMove [
.last 23 (5,true),
.cycle 0 20 true (0),
.cycle 5 20 true (0),
.cycle 0 27 true (0),
.cycle 25 6 false (1),
.last 28 (5,true),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 13 4 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 22 true (0),
.cycle 26 3 false (0),
.cycle 9 9 true (3),
.cycle 5 18 true (0),
.last 18 (5,true),
.cycle 5 20 true (0),
.cycle 10 7 true (4),
.cycle 1 17 true (1),
.cycle 15 2 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true)
]),
.cycle 0 16 true (0),
.cycle 5 16 true (0),
.split 15 (5,true) (byMove [
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 0 28 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 2 15 true (1),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 5 37 true (0),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 5 20 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 0 21 true (0),
.cycle 0 20 true (0)
]),
.cycle 5 18 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (5),
.cycle 12 2 true (5)
])
theorem kid21_part435_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid21_part435) = true := by rfl

def kid21_part436 : Audit := .cycle 0 14 true (0)
theorem kid21_part436_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid21_part436) = true := by rfl

def kid21_part437 : Audit := .cycle 7 6 true (3)
theorem kid21_part437_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid21_part437) = true := by rfl

def kid21_part438 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 18 true (0),
.cycle 37 1 false (5),
.cycle 30 3 false (3),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 5 37 true (0),
.cycle 0 27 true (0),
.cycle 11 3 true (5),
.cycle 21 1 false (1),
.split 15 (1,true) (byMove [
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 33 3 false (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.cycle 40 5 false (4),
.cycle 6 10 true (2),
.last 18 (2,true),
.last 16 (2,true),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 0 32 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 6 13 true (2),
.cycle 6 12 true (2)
]),
.split 15 (2,true) (byMove [
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 49 1 false (5),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 26 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 0 24 true (0),
.cycle 3 13 true (1),
.cycle 11 5 true (4),
.last 34 (1,true),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 9 9 true (3),
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.last 26 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.last 19 (1,true),
.last 18 (1,true)
]),
.cycle 0 16 true (0),
.cycle 5 16 true (0),
.cycle 0 18 true (0),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (5),
.cycle 12 2 true (5)
])
theorem kid21_part438_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid21_part438) = true := by rfl

def kid21_part439 : Audit := .cycle 0 13 true (0)
theorem kid21_part439_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid21_part439) = true := by rfl

def kid21_part440 : Audit := .cycle 1 12 true (1)
theorem kid21_part440_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid21_part440) = true := by rfl

def kid21_part441 : Audit := .cycle 0 21 true (0)
theorem kid21_part441_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid21_part441) = true := by rfl

def kid21_part442 : Audit := .cycle 3 10 true (1)
theorem kid21_part442_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid21_part442) = true := by rfl

def kid21_part443 : Audit := .cycle 11 2 true (5)
theorem kid21_part443_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid21_part443) = true := by rfl

def kid21_part444 : Audit := .cycle 12 1 true (6)
theorem kid21_part444_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid21_part444) = true := by rfl

def kid21_part445 : Audit := .cycle 6 7 true (2)
theorem kid21_part445_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid21_part445) = true := by rfl

def kid21_part447 : Audit := .split 16 (2,true) (byMove [
.cycle 10 7 true (4),
.cycle 10 8 true (4),
.cycle 55 1 false (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 15 3 true (5),
.cycle 6 11 true (2),
.last 20 (5,true),
.cycle 5 15 true (1),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.last 22 (5,true),
.last 21 (5,true)
])
theorem kid21_part447_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid21_part447) = true := by rfl

def kid21_part448 : Audit := .cycle 0 17 true (0)
theorem kid21_part448_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid21_part448) = true := by rfl

def kid21_part449 : Audit := .cycle 0 27 true (0)
theorem kid21_part449_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid21_part449) = true := by rfl

def kid21_part450 : Audit := .split 24 (5,true) (byMove [
.cycle 0 39 true (0),
.cycle 37 1 false (5),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 7 18 true (0),
.last 28 (2,true),
.cycle 0 25 true (0),
.cycle 0 75 true (0),
.cycle 0 33 true (0),
.cycle 0 52 true (0),
.cycle 21 8 true (3),
.last 27 (2,true),
.cycle 0 70 true (0),
.cycle 41 1 false (7),
.last 25 (2,true),
.cycle 9 16 true (0),
.cycle 0 27 true (0),
.last 28 (2,true),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 0 89 true (0),
.cycle 0 32 true (0),
.cycle 0 31 true (0)
])
theorem kid21_part450_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid21_part450) = true := by rfl

def kid21_part451 : Audit := .cycle 0 35 true (0)
theorem kid21_part451_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid21_part451) = true := by rfl

def kid21_part452 : Audit := .split 16 (2,true) (byMove [
.cycle 35 7 false (1),
.last 22 (5,true),
.cycle 48 1 false (4),
.cycle 0 22 true (0),
.last 22 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.cycle 1 18 true (1),
.cycle 0 19 true (0),
.cycle 0 23 true (0),
.last 18 (5,true),
.last 20 (5,true),
.cycle 4 15 true (1),
.last 22 (5,true),
.last 22 (5,true),
.last 20 (5,true),
.last 21 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.cycle 1 18 true (1),
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.last 18 (5,true),
.last 19 (5,true)
])
theorem kid21_part452_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid21_part452) = true := by rfl

def kid21_part453 : Audit := .cycle 10 4 true (4)
theorem kid21_part453_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid21_part453) = true := by rfl

def kid21_part454 : Audit := .cycle 1 14 true (1)
theorem kid21_part454_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid21_part454) = true := by rfl

def kid21_part455 : Audit := .split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.cycle 14 3 true (6),
.cycle 0 25 true (0),
.cycle 13 4 true (5),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.last 16 (5,true),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part455_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid21_part455) = true := by rfl

def kid21_part456 : Audit := .cycle 0 15 true (0)
theorem kid21_part456_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid21_part456) = true := by rfl

def kid21_part457 : Audit := .cycle 7 7 true (3)
theorem kid21_part457_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid21_part457) = true := by rfl

def kid21_part458 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.last 17 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.last 17 (2,true),
.last 19 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.cycle 0 19 true (0),
.last 17 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part458_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid21_part458) = true := by rfl

def kid21_part459 : Audit := .cycle 0 19 true (0)
theorem kid21_part459_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid21_part459) = true := by rfl

def kid21_part460 : Audit := .split 15 (2,true) (byMove [
.last 18 (5,true),
.cycle 26 3 false (0),
.last 28 (5,true),
.cycle 13 6 true (4),
.cycle 4 13 true (1),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 1 18 true (1),
.cycle 9 16 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 19 true (0),
.cycle 26 3 false (0),
.cycle 5 13 true (1),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 32 5 false (2),
.cycle 2 15 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
])
theorem kid21_part460_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid21_part460) = true := by rfl

def kid21_part461 : Audit := .cycle 9 6 true (3)
theorem kid21_part461_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid21_part461) = true := by rfl

def kid21_part462 : Audit := .cycle 0 25 true (0)
theorem kid21_part462_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid21_part462) = true := by rfl

def kid21_part463 : Audit := .split 15 (5,true) (byMove [
.cycle 10 9 true (4),
.cycle 0 37 true (0),
.last 16 (2,true),
.cycle 0 21 true (0),
.cycle 4 13 true (1),
.last 19 (2,true),
.cycle 10 6 true (4),
.cycle 1 18 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 19 (2,true),
.cycle 0 19 true (0),
.cycle 5 25 true (0),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.last 19 (2,true),
.cycle 10 6 true (4),
.cycle 0 19 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 9 11 true (3)
])
theorem kid21_part463_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid21_part463) = true := by rfl

def kid21_part464 : Audit := .split 16 (2,true) (byMove [
.last 19 (5,true),
.last 22 (5,true),
.last 28 (5,true),
.last 20 (5,true),
.cycle 0 23 true (0),
.last 17 (5,true),
.cycle 6 11 true (2),
.last 26 (5,true),
.cycle 5 23 true (1),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 9 10 true (3),
.last 22 (5,true),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 5 13 true (1),
.last 17 (5,true),
.cycle 6 11 true (2),
.last 18 (5,true),
.cycle 2 17 true (1),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true)
])
theorem kid21_part464_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid21_part464) = true := by rfl

def kid21_part465 : Audit := .cycle 10 4 true (4)
theorem kid21_part465_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid21_part465) = true := by rfl

def kid21_part466 : Audit := .cycle 1 14 true (1)
theorem kid21_part466_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid21_part466) = true := by rfl

def kid21_part467 : Audit := .split 14 (2,true) (byMove [
.cycle 10 5 true (4),
.cycle 2 14 true (1),
.cycle 5 20 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 14 3 true (6),
.cycle 6 9 true (2),
.cycle 13 2 true (5),
.cycle 9 8 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part467_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid21_part467) = true := by rfl

def kid21_part468 : Audit := .cycle 0 15 true (0)
theorem kid21_part468_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid21_part468) = true := by rfl

def kid21_part469 : Audit := .cycle 7 7 true (3)
theorem kid21_part469_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid21_part469) = true := by rfl

def kid21_part470 : Audit := .split 14 (5,true) (byMove [
.cycle 10 5 true (4),
.cycle 12 4 true (5),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 18 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.last 17 (2,true),
.cycle 6 9 true (2),
.cycle 13 2 true (5),
.last 15 (2,true),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.last 18 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part470_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid21_part470) = true := by rfl

def kid21_part446 : Audit := .split 13 (1,true) (byMove [(kid21_part447),(kid21_part448),(kid21_part449),(kid21_part450),(kid21_part451),(kid21_part452),(kid21_part453),(kid21_part454),(kid21_part455),(kid21_part456),(kid21_part457),(kid21_part458),(kid21_part459),(kid21_part460),(kid21_part461),(kid21_part462),(kid21_part463),(kid21_part464),(kid21_part465),(kid21_part466),(kid21_part467),(kid21_part468),(kid21_part469),(kid21_part470)])

theorem kid21_part446_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid21_part446) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 13 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid21_part447),(kid21_part448),(kid21_part449),(kid21_part450),(kid21_part451),(kid21_part452),(kid21_part453),(kid21_part454),(kid21_part455),(kid21_part456),(kid21_part457),(kid21_part458),(kid21_part459),(kid21_part460),(kid21_part461),(kid21_part462),(kid21_part463),(kid21_part464),(kid21_part465),(kid21_part466),(kid21_part467),(kid21_part468),(kid21_part469),(kid21_part470)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part447_checked

  · exact kid21_part453_checked

  · exact kid21_part459_checked

  · exact kid21_part465_checked

  · exact kid21_part448_checked

  · exact kid21_part454_checked

  · exact kid21_part460_checked

  · exact kid21_part466_checked

  · exact kid21_part449_checked

  · exact kid21_part455_checked

  · exact kid21_part461_checked

  · exact kid21_part467_checked

  · exact kid21_part450_checked

  · exact kid21_part456_checked

  · exact kid21_part462_checked

  · exact kid21_part468_checked

  · exact kid21_part451_checked

  · exact kid21_part457_checked

  · exact kid21_part463_checked

  · exact kid21_part469_checked

  · exact kid21_part452_checked

  · exact kid21_part458_checked

  · exact kid21_part464_checked

  · exact kid21_part470_checked

def kid21_part472 : Audit := .cycle 10 7 true (4)
theorem kid21_part472_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid21_part472) = true := by rfl

def kid21_part473 : Audit := .cycle 0 17 true (0)
theorem kid21_part473_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid21_part473) = true := by rfl

def kid21_part474 : Audit := .cycle 0 27 true (0)
theorem kid21_part474_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid21_part474) = true := by rfl

def kid21_part475 : Audit := .split 24 (5,true) (byMove [
.last 37 (1,true),
.last 25 (1,true),
.cycle 37 1 false (5),
.cycle 0 26 true (0),
.cycle 7 18 true (0),
.cycle 0 29 true (0),
.cycle 0 25 true (0),
.last 73 (1,true),
.cycle 0 33 true (0),
.last 50 (1,true),
.cycle 21 8 true (3),
.cycle 0 28 true (0),
.last 68 (1,true),
.last 25 (1,true),
.cycle 41 1 false (7),
.cycle 9 16 true (0),
.cycle 0 27 true (0),
.last 72 (1,true),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.last 87 (1,true),
.last 30 (1,true),
.last 29 (1,true)
])
theorem kid21_part475_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid21_part475) = true := by rfl

def kid21_part476 : Audit := .cycle 0 35 true (0)
theorem kid21_part476_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid21_part476) = true := by rfl

def kid21_part477 : Audit := .split 18 (1,true) (byMove [
.cycle 10 9 true (3),
.cycle 1 19 true (1),
.cycle 0 23 true (0),
.cycle 0 20 true (0),
.cycle 7 12 true (3),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 0 27 true (0),
.cycle 3 16 true (1),
.last 30 (5,true),
.cycle 0 22 true (0),
.cycle 6 13 true (2),
.last 22 (5,true),
.cycle 13 6 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 8 11 true (3),
.last 22 (5,true),
.last 21 (5,true)
])
theorem kid21_part477_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid21_part477) = true := by rfl

def kid21_part478 : Audit := .cycle 10 4 true (4)
theorem kid21_part478_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid21_part478) = true := by rfl

def kid21_part479 : Audit := .split 14 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.cycle 0 18 true (0),
.cycle 6 11 true (2),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.last 16 (5,true),
.cycle 9 8 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part479_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid21_part479) = true := by rfl

def kid21_part480 : Audit := .cycle 5 25 true (0)
theorem kid21_part480_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid21_part480) = true := by rfl

def kid21_part481 : Audit := .cycle 0 15 true (0)
theorem kid21_part481_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid21_part481) = true := by rfl

def kid21_part482 : Audit := .cycle 7 7 true (3)
theorem kid21_part482_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid21_part482) = true := by rfl

def kid21_part483 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.cycle 0 18 true (0),
.last 16 (1,true),
.cycle 0 20 true (0),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.cycle 0 19 true (0),
.cycle 9 8 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part483_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid21_part483) = true := by rfl

def kid21_part484 : Audit := .split 15 (1,true) (byMove [
.last 18 (5,true),
.cycle 0 25 true (0),
.cycle 33 3 false (3),
.cycle 0 20 true (0),
.cycle 4 13 true (1),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 0 27 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 19 true (0),
.cycle 9 12 true (3),
.cycle 5 39 true (0),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.last 16 (5,true),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 16 (5,true)
])
theorem kid21_part484_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid21_part484) = true := by rfl

def kid21_part485 : Audit := .split 16 (1,true) (byMove [
.last 23 (5,true),
.cycle 9 10 true (3),
.cycle 0 29 true (0),
.cycle 0 30 true (0),
.cycle 25 6 false (1),
.last 22 (5,true),
.cycle 6 11 true (2),
.cycle 1 18 true (1),
.cycle 13 4 true (4),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true),
.cycle 9 12 true (3),
.cycle 26 3 false (0),
.cycle 5 13 true (1),
.cycle 0 27 true (0),
.last 18 (5,true),
.cycle 0 23 true (0),
.cycle 6 11 true (2),
.cycle 1 18 true (1),
.cycle 15 2 true (4),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.last 17 (5,true)
])
theorem kid21_part485_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid21_part485) = true := by rfl

def kid21_part486 : Audit := .cycle 9 6 true (3)
theorem kid21_part486_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid21_part486) = true := by rfl

def kid21_part487 : Audit := .cycle 0 25 true (0)
theorem kid21_part487_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid21_part487) = true := by rfl

def kid21_part488 : Audit := .split 15 (5,true) (byMove [
.cycle 10 9 true (4),
.last 16 (1,true),
.cycle 0 37 true (0),
.last 18 (1,true),
.cycle 4 13 true (1),
.cycle 0 25 true (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 0 27 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.last 16 (1,true),
.cycle 5 25 true (0),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.cycle 0 23 true (0),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 9 11 true (3)
])
theorem kid21_part488_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid21_part488) = true := by rfl

def kid21_part489 : Audit := .cycle 5 11 true (1)
theorem kid21_part489_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid21_part489) = true := by rfl

def kid21_part490 : Audit := .cycle 10 4 true (4)
theorem kid21_part490_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid21_part490) = true := by rfl

def kid21_part491 : Audit := .split 14 (1,true) (byMove [
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 0 18 true (0),
.cycle 6 9 true (2),
.cycle 34 5 false (2),
.cycle 13 2 true (5),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part491_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid21_part491) = true := by rfl

def kid21_part492 : Audit := .cycle 2 13 true (1)
theorem kid21_part492_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid21_part492) = true := by rfl

def kid21_part493 : Audit := .cycle 0 15 true (0)
theorem kid21_part493_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid21_part493) = true := by rfl

def kid21_part494 : Audit := .cycle 7 7 true (3)
theorem kid21_part494_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid21_part494) = true := by rfl

def kid21_part495 : Audit := .split 14 (5,true) (byMove [
.cycle 10 5 true (4),
.last 15 (1,true),
.cycle 12 4 true (5),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 0 18 true (0),
.cycle 6 9 true (2),
.last 15 (1,true),
.cycle 13 2 true (5),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 5 13 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part495_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid21_part495) = true := by rfl

def kid21_part471 : Audit := .split 13 (2,true) (byMove [(kid21_part472),(kid21_part473),(kid21_part474),(kid21_part475),(kid21_part476),(kid21_part477),(kid21_part478),(kid21_part479),(kid21_part480),(kid21_part481),(kid21_part482),(kid21_part483),(kid21_part484),(kid21_part485),(kid21_part486),(kid21_part487),(kid21_part488),(kid21_part489),(kid21_part490),(kid21_part491),(kid21_part492),(kid21_part493),(kid21_part494),(kid21_part495)])

theorem kid21_part471_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid21_part471) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 13 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid21_part472),(kid21_part473),(kid21_part474),(kid21_part475),(kid21_part476),(kid21_part477),(kid21_part478),(kid21_part479),(kid21_part480),(kid21_part481),(kid21_part482),(kid21_part483),(kid21_part484),(kid21_part485),(kid21_part486),(kid21_part487),(kid21_part488),(kid21_part489),(kid21_part490),(kid21_part491),(kid21_part492),(kid21_part493),(kid21_part494),(kid21_part495)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part472_checked

  · exact kid21_part478_checked

  · exact kid21_part484_checked

  · exact kid21_part490_checked

  · exact kid21_part473_checked

  · exact kid21_part479_checked

  · exact kid21_part485_checked

  · exact kid21_part491_checked

  · exact kid21_part474_checked

  · exact kid21_part480_checked

  · exact kid21_part486_checked

  · exact kid21_part492_checked

  · exact kid21_part475_checked

  · exact kid21_part481_checked

  · exact kid21_part487_checked

  · exact kid21_part493_checked

  · exact kid21_part476_checked

  · exact kid21_part482_checked

  · exact kid21_part488_checked

  · exact kid21_part494_checked

  · exact kid21_part477_checked

  · exact kid21_part483_checked

  · exact kid21_part489_checked

  · exact kid21_part495_checked

def kid21_part496 : Audit := .cycle 9 4 true (3)
theorem kid21_part496_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid21_part496) = true := by rfl

def kid21_part497 : Audit := .cycle 0 15 true (0)
theorem kid21_part497_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid21_part497) = true := by rfl

def kid21_part499 : Audit := .split 16 (2,true) (byMove [
.cycle 10 7 true (4),
.last 17 (1,true),
.cycle 55 1 false (5),
.cycle 0 18 true (0),
.cycle 7 10 true (3),
.cycle 10 8 true (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 25 true (0),
.cycle 3 14 true (1),
.cycle 11 6 true (4),
.cycle 10 16 true (4),
.cycle 6 11 true (2),
.last 17 (1,true),
.cycle 5 15 true (1),
.cycle 9 8 true (3),
.cycle 0 19 true (0),
.cycle 10 11 true (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (3),
.cycle 10 13 true (4),
.cycle 10 12 true (4)
])
theorem kid21_part499_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid21_part499) = true := by rfl

def kid21_part500 : Audit := .cycle 0 17 true (0)
theorem kid21_part500_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid21_part500) = true := by rfl

def kid21_part501 : Audit := .cycle 0 27 true (0)
theorem kid21_part501_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid21_part501) = true := by rfl

def kid21_part502 : Audit := .cycle 0 26 true (0)
theorem kid21_part502_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid21_part502) = true := by rfl

def kid21_part503 : Audit := .cycle 0 35 true (0)
theorem kid21_part503_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid21_part503) = true := by rfl

def kid21_part504 : Audit := .cycle 19 1 false (-1)
theorem kid21_part504_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid21_part504) = true := by rfl

def kid21_part505 : Audit := .cycle 10 4 true (4)
theorem kid21_part505_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid21_part505) = true := by rfl

def kid21_part506 : Audit := .split 14 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.cycle 22 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.cycle 30 1 false (8),
.cycle 6 11 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.cycle 1 16 true (1),
.cycle 22 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part506_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid21_part506) = true := by rfl

def kid21_part507 : Audit := .split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 29 true (0),
.cycle 5 18 true (0),
.cycle 11 4 true (5),
.cycle 22 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 5 25 true (0),
.cycle 5 37 true (0),
.cycle 11 4 true (5),
.cycle 30 1 false (8),
.last 16 (1,true),
.last 17 (1,true),
.cycle 0 17 true (0),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 22 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part507_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid21_part507) = true := by rfl

def kid21_part508 : Audit := .cycle 0 15 true (0)
theorem kid21_part508_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid21_part508) = true := by rfl

def kid21_part509 : Audit := .cycle 7 7 true (3)
theorem kid21_part509_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid21_part509) = true := by rfl

def kid21_part510 : Audit := .cycle 30 1 false (8)
theorem kid21_part510_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid21_part510) = true := by rfl

def kid21_part511 : Audit := .split 15 (1,true) (byMove [
.cycle 6 13 true (2),
.cycle 0 25 true (0),
.last 16 (2,true),
.cycle 0 20 true (0),
.cycle 4 13 true (1),
.cycle 33 3 false (3),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 9 15 true (3),
.cycle 0 19 true (0),
.last 18 (2,true),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.cycle 5 39 true (0),
.cycle 10 6 true (4),
.cycle 1 16 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.cycle 6 11 true (2)
])
theorem kid21_part511_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid21_part511) = true := by rfl

def kid21_part512 : Audit := .split 15 (2,true) (byMove [
.last 19 (1,true),
.last 16 (1,true),
.last 29 (1,true),
.last 18 (1,true),
.cycle 4 13 true (1),
.last 26 (1,true),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 9 16 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 22 (1,true),
.cycle 0 19 true (0),
.last 16 (1,true),
.cycle 5 13 true (1),
.cycle 5 11 true (1),
.cycle 9 8 true (3),
.last 26 (1,true),
.cycle 10 6 true (4),
.last 16 (1,true),
.cycle 2 15 true (1),
.cycle 0 17 true (0),
.cycle 7 9 true (3),
.last 17 (1,true)
])
theorem kid21_part512_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid21_part512) = true := by rfl

def kid21_part513 : Audit := .cycle 9 6 true (3)
theorem kid21_part513_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid21_part513) = true := by rfl

def kid21_part514 : Audit := .cycle 0 25 true (0)
theorem kid21_part514_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid21_part514) = true := by rfl

def kid21_part515 : Audit := .cycle 9 8 true (3)
theorem kid21_part515_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid21_part515) = true := by rfl

def kid21_part516 : Audit := .cycle 19 1 false (-1)
theorem kid21_part516_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid21_part516) = true := by rfl

def kid21_part517 : Audit := .cycle 10 4 true (4)
theorem kid21_part517_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid21_part517) = true := by rfl

def kid21_part518 : Audit := .split 14 (1,true) (byMove [
.cycle 10 5 true (4),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 1 19 true (1),
.cycle 6 9 true (2),
.last 17 (2,true),
.last 15 (2,true),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 13 2 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part518_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid21_part518) = true := by rfl

def kid21_part519 : Audit := .split 14 (2,true) (byMove [
.cycle 10 5 true (4),
.last 15 (1,true),
.cycle 5 20 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.cycle 2 14 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 2 18 true (1),
.cycle 6 9 true (2),
.last 15 (1,true),
.cycle 9 8 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 13 2 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid21_part519_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid21_part519) = true := by rfl

def kid21_part520 : Audit := .cycle 0 15 true (0)
theorem kid21_part520_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid21_part520) = true := by rfl

def kid21_part521 : Audit := .cycle 7 7 true (3)
theorem kid21_part521_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid21_part521) = true := by rfl

def kid21_part522 : Audit := .cycle 12 3 true (5)
theorem kid21_part522_checked : zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid21_part522) = true := by rfl

def kid21_part498 : Audit := .split 13 (5,true) (byMove [(kid21_part499),(kid21_part500),(kid21_part501),(kid21_part502),(kid21_part503),(kid21_part504),(kid21_part505),(kid21_part506),(kid21_part507),(kid21_part508),(kid21_part509),(kid21_part510),(kid21_part511),(kid21_part512),(kid21_part513),(kid21_part514),(kid21_part515),(kid21_part516),(kid21_part517),(kid21_part518),(kid21_part519),(kid21_part520),(kid21_part521),(kid21_part522)])

theorem kid21_part498_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid21_part498) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 13 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid21_part499),(kid21_part500),(kid21_part501),(kid21_part502),(kid21_part503),(kid21_part504),(kid21_part505),(kid21_part506),(kid21_part507),(kid21_part508),(kid21_part509),(kid21_part510),(kid21_part511),(kid21_part512),(kid21_part513),(kid21_part514),(kid21_part515),(kid21_part516),(kid21_part517),(kid21_part518),(kid21_part519),(kid21_part520),(kid21_part521),(kid21_part522)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part499_checked

  · exact kid21_part505_checked

  · exact kid21_part511_checked

  · exact kid21_part517_checked

  · exact kid21_part500_checked

  · exact kid21_part506_checked

  · exact kid21_part512_checked

  · exact kid21_part518_checked

  · exact kid21_part501_checked

  · exact kid21_part507_checked

  · exact kid21_part513_checked

  · exact kid21_part519_checked

  · exact kid21_part502_checked

  · exact kid21_part508_checked

  · exact kid21_part514_checked

  · exact kid21_part520_checked

  · exact kid21_part503_checked

  · exact kid21_part509_checked

  · exact kid21_part515_checked

  · exact kid21_part521_checked

  · exact kid21_part504_checked

  · exact kid21_part510_checked

  · exact kid21_part516_checked

  · exact kid21_part522_checked

def kid21_part523 : Audit := .cycle 0 13 true (0)
theorem kid21_part523_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid21_part523) = true := by rfl

def kid21_part524 : Audit := .cycle 1 12 true (1)
theorem kid21_part524_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid21_part524) = true := by rfl

def kid21_part525 : Audit := .cycle 2 11 true (1)
theorem kid21_part525_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid21_part525) = true := by rfl

def kid21_part526 : Audit := .cycle 8 5 true (3)
theorem kid21_part526_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid21_part526) = true := by rfl

def kid21_part527 : Audit := .cycle 11 2 true (5)
theorem kid21_part527_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid21_part527) = true := by rfl

def kid21_part528 : Audit := .cycle 12 1 true (6)
theorem kid21_part528_checked : zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid21_part528) = true := by rfl

def kid21_part432 : Audit := .split 12 (5,false) (byMove [(kid21_part433),(kid21_part434),(kid21_part435),(kid21_part436),(kid21_part437),(kid21_part438),(kid21_part439),(kid21_part440),(kid21_part441),(kid21_part442),(kid21_part443),(kid21_part444),(kid21_part445),(kid21_part446),(kid21_part471),(kid21_part496),(kid21_part497),(kid21_part498),(kid21_part523),(kid21_part524),(kid21_part525),(kid21_part526),(kid21_part527),(kid21_part528)])

theorem kid21_part432_checked : zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (kid21_part432) = true := by

  change (zipQueryOK 944 (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨true,true,3⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid21_part433),(kid21_part434),(kid21_part435),(kid21_part436),(kid21_part437),(kid21_part438),(kid21_part439),(kid21_part440),(kid21_part441),(kid21_part442),(kid21_part443),(kid21_part444),(kid21_part445),(kid21_part446),(kid21_part471),(kid21_part496),(kid21_part497),(kid21_part498),(kid21_part523),(kid21_part524),(kid21_part525),(kid21_part526),(kid21_part527),(kid21_part528)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part433_checked

  · exact kid21_part439_checked

  · exact kid21_part445_checked

  · exact kid21_part523_checked

  · exact kid21_part434_checked

  · exact kid21_part440_checked

  · exact kid21_part446_checked

  · exact kid21_part524_checked

  · exact kid21_part435_checked

  · exact kid21_part441_checked

  · exact kid21_part471_checked

  · exact kid21_part525_checked

  · exact kid21_part436_checked

  · exact kid21_part442_checked

  · exact kid21_part496_checked

  · exact kid21_part526_checked

  · exact kid21_part437_checked

  · exact kid21_part443_checked

  · exact kid21_part497_checked

  · exact kid21_part527_checked

  · exact kid21_part438_checked

  · exact kid21_part444_checked

  · exact kid21_part498_checked

  · exact kid21_part528_checked

def kid21 : Audit := .split 11 (4,false) (byMove [(kid21_part1),(kid21_part2),(kid21_part3),(kid21_part4),(kid21_part5),(kid21_part6),(kid21_part103),(kid21_part104),(kid21_part105),(kid21_part106),(kid21_part107),(kid21_part108),(kid21_part157),(kid21_part206),(kid21_part279),(kid21_part280),(kid21_part281),(kid21_part282),(kid21_part427),(kid21_part428),(kid21_part429),(kid21_part430),(kid21_part431),(kid21_part432)])

theorem check21 : zipCheck 944 (child ⟨true,true,3⟩) (kid21) = true := by

  change (zipQueryOK 944 (child ⟨true,true,3⟩) 11 (4,false) && allMoves (fun mv => zipCheck 944 (refine (child ⟨true,true,3⟩) (4,false) (some mv)) (byMove [(kid21_part1),(kid21_part2),(kid21_part3),(kid21_part4),(kid21_part5),(kid21_part6),(kid21_part103),(kid21_part104),(kid21_part105),(kid21_part106),(kid21_part107),(kid21_part108),(kid21_part157),(kid21_part206),(kid21_part279),(kid21_part280),(kid21_part281),(kid21_part282),(kid21_part427),(kid21_part428),(kid21_part429),(kid21_part430),(kid21_part431),(kid21_part432)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid21_part1_checked

  · exact kid21_part103_checked

  · exact kid21_part157_checked

  · exact kid21_part427_checked

  · exact kid21_part2_checked

  · exact kid21_part104_checked

  · exact kid21_part206_checked

  · exact kid21_part428_checked

  · exact kid21_part3_checked

  · exact kid21_part105_checked

  · exact kid21_part279_checked

  · exact kid21_part429_checked

  · exact kid21_part4_checked

  · exact kid21_part106_checked

  · exact kid21_part280_checked

  · exact kid21_part430_checked

  · exact kid21_part5_checked

  · exact kid21_part107_checked

  · exact kid21_part281_checked

  · exact kid21_part431_checked

  · exact kid21_part6_checked

  · exact kid21_part108_checked

  · exact kid21_part282_checked

  · exact kid21_part432_checked

end BB6.Agent11Raw39B0RE
