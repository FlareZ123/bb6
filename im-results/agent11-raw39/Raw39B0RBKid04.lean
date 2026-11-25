import Raw39B0RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid04_part1 : Audit := .cycle 0 9 true (0)
theorem kid04_part1_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,0⟩)) (kid04_part1) = true := by rfl

def kid04_part2 : Audit := .cycle 1 8 true (1)
theorem kid04_part2_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,1⟩)) (kid04_part2) = true := by rfl

def kid04_part3 : Audit := .cycle 17 1 false (1)
theorem kid04_part3_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,2⟩)) (kid04_part3) = true := by rfl

def kid04_part4 : Audit := .cycle 20 1 false (2)
theorem kid04_part4_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,3⟩)) (kid04_part4) = true := by rfl

def kid04_part6 : Audit := .cycle 0 11 false (3)
theorem kid04_part6_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part6) = true := by rfl

def kid04_part7 : Audit := .cycle 18 1 false (0)
theorem kid04_part7_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part7) = true := by rfl

def kid04_part8 : Audit := .cycle 12 1 false (0)
theorem kid04_part8_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part8) = true := by rfl

def kid04_part9 : Audit := .cycle 11 1 false (-1)
theorem kid04_part9_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part9) = true := by rfl

def kid04_part10 : Audit := .cycle 11 1 false (-1)
theorem kid04_part10_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part10) = true := by rfl

def kid04_part11 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 12 true (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 10 4 false (0),
.split 13 (2,true) (byMove [
.cycle 22 1 false (0),
.cycle 15 1 false (-3),
.cycle 16 1 false (-2),
.cycle 0 15 false (3),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 27 1 false (-3),
.cycle 8 14 false (2),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 8 6 false (2),
.cycle 11 3 true (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 25 (5,true),
.last 24 (5,true),
.cycle 2 12 false (3),
.cycle 8 18 false (3),
.last 16 (5,true),
.cycle 10 6 false (0)
]),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.split 23 (5,true) (byMove [
.cycle 0 24 false (3),
.cycle 31 1 false (-1),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.cycle 24 1 false (-2),
.cycle 11 13 false (3),
.cycle 0 24 true (-1),
.cycle 31 1 false (1),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 24 1 false (0),
.cycle 11 13 true (-1),
.cycle 10 16 false (3),
.last 25 (2,true),
.cycle 0 26 true (-2),
.cycle 24 1 false (-2),
.cycle 24 1 false (-2),
.cycle 8 26 false (3),
.cycle 12 12 true (-1),
.cycle 1 23 false (3),
.cycle 30 1 false (0),
.cycle 34 1 false (2),
.cycle 9 15 false (3),
.cycle 11 13 true (-1)
]),
.cycle 1 11 false (3),
.cycle 18 1 false (0),
.cycle 22 1 false (2),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
])
theorem kid04_part11_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part11) = true := by rfl

def kid04_part12 : Audit := .cycle 0 11 true (0)
theorem kid04_part12_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part12) = true := by rfl

def kid04_part13 : Audit := .cycle 18 1 false (2)
theorem kid04_part13_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part13) = true := by rfl

def kid04_part14 : Audit := .cycle 12 1 false (2)
theorem kid04_part14_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part14) = true := by rfl

def kid04_part15 : Audit := .cycle 11 1 false (1)
theorem kid04_part15_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part15) = true := by rfl

def kid04_part16 : Audit := .cycle 11 1 false (1)
theorem kid04_part16_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part16) = true := by rfl

def kid04_part17 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 19 1 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 19 1 false (3),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 10 4 true (0),
.split 13 (2,true) (byMove [
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 10 4 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 8 14 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 6 true (0),
.cycle 11 3 true (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 8 18 true (0),
.cycle 9 5 true (0),
.last 20 (5,true)
]),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 1 false (2),
.cycle 22 1 false (4),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid04_part17_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part17) = true := by rfl

def kid04_part18 : Audit := .cycle 10 3 false (0)
theorem kid04_part18_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part18) = true := by rfl

def kid04_part19 : Audit := .split 12 (2,true) (byMove [
.cycle 21 1 false (1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 0 14 false (3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 0 14 true (-1),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 26 1 false (-2),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.cycle 24 1 false (2),
.cycle 9 5 false (1),
.last 14 (5,false)
]),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 5 false (2),
.split 13 (5,false) (byMove [
.cycle 26 1 false (-2),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.cycle 24 1 false (2),
.cycle 9 5 false (1),
.last 15 (5,true),
.cycle 0 14 true (-1),
.cycle 8 15 false (4),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 8 7 false (2),
.cycle 13 1 true (1),
.cycle 18 1 false (-2),
.cycle 11 3 true (-1),
.cycle 0 16 true (-1),
.cycle 18 1 false (0),
.cycle 9 5 false (1),
.last 15 (5,true),
.cycle 24 9 false (2),
.cycle 1 13 true (-1),
.cycle 8 13 false (3),
.cycle 8 19 false (5),
.cycle 9 5 true (-1),
.cycle 13 1 true (1)
]),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 11 8 true (-2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 15 true (-1),
.cycle 10 4 true (-1),
.last 15 (5,false),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 8 15 false (3),
.cycle 10 5 false (0),
.cycle 12 2 true (-1),
.cycle 0 15 true (-1),
.cycle 16 1 false (-2),
.last 15 (5,false)
]),
.cycle 23 7 false (1),
.cycle 24 1 false (-2),
.cycle 2 11 false (3),
.cycle 8 17 false (4),
.cycle 16 1 false (-2),
.split 13 (5,false) (byMove [
.cycle 8 15 false (3),
.cycle 10 5 false (1),
.cycle 12 2 true (0),
.cycle 0 15 true (-1),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 26 1 false (-2),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 18 1 false (-2),
.cycle 13 1 true (1),
.cycle 9 7 false (1),
.cycle 10 5 false (1),
.last 15 (5,true),
.cycle 8 17 false (4),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 28 1 false (-2),
.cycle 23 7 false (1),
.cycle 24 1 false (-2),
.cycle 30 1 false (-2),
.cycle 25 1 false (-3),
.cycle 13 1 true (1)
])
])
theorem kid04_part19_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part19) = true := by rfl

def kid04_part20 : Audit := .cycle 0 13 true (-1)
theorem kid04_part20_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part20) = true := by rfl

def kid04_part21 : Audit := .cycle 11 1 false (-1)
theorem kid04_part21_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part21) = true := by rfl

def kid04_part22 : Audit := .cycle 11 1 false (-1)
theorem kid04_part22_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part22) = true := by rfl

def kid04_part24 : Audit := .split 14 (2,true) (byMove [
.cycle 8 16 false (2),
.cycle 10 6 false (0),
.cycle 18 1 false (-2),
.cycle 0 32 true (-2),
.last 16 (5,true),
.last 15 (5,true),
.cycle 13 15 true (-1),
.last 26 (5,true),
.cycle 3 14 false (3),
.cycle 3 12 false (3),
.last 18 (5,true),
.last 27 (5,true),
.cycle 9 8 false (1),
.cycle 10 6 false (0),
.cycle 21 1 false (-1),
.cycle 8 18 false (3),
.last 16 (5,true),
.last 15 (5,true),
.last 26 (5,true),
.last 25 (5,true),
.last 24 (5,true),
.last 30 (5,true),
.last 17 (5,true),
.last 28 (5,true)
])
theorem kid04_part24_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part24) = true := by rfl

def kid04_part25 : Audit := .cycle 0 15 true (-2)
theorem kid04_part25_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part25) = true := by rfl

def kid04_part26 : Audit := .cycle 13 1 false (-1)
theorem kid04_part26_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part26) = true := by rfl

def kid04_part27 : Audit := .cycle 12 1 false (-2)
theorem kid04_part27_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part27) = true := by rfl

def kid04_part28 : Audit := .cycle 12 1 false (-2)
theorem kid04_part28_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part28) = true := by rfl

def kid04_part29 : Audit := .cycle 11 1 false (-1)
theorem kid04_part29_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part29) = true := by rfl

def kid04_part30 : Audit := .cycle 20 1 false (2)
theorem kid04_part30_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part30) = true := by rfl

def kid04_part31 : Audit := .cycle 13 1 false (-1)
theorem kid04_part31_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part31) = true := by rfl

def kid04_part32 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (-1),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (3),
.cycle 10 5 false (0),
.cycle 16 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.last 24 (5,true),
.cycle 1 12 true (-1),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 9 4 true (-1),
.cycle 21 1 false (1)
])
theorem kid04_part32_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part32) = true := by rfl

def kid04_part33 : Audit := .cycle 0 13 true (-1)
theorem kid04_part33_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part33) = true := by rfl

def kid04_part34 : Audit := .cycle 10 2 true (-1)
theorem kid04_part34_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part34) = true := by rfl

def kid04_part35 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 true (-1),
.cycle 0 13 true (-1),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 true (1),
.cycle 10 5 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 8 26 true (-1),
.cycle 1 12 true (-1),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 9 4 true (-1),
.cycle 13 1 true (1)
])
theorem kid04_part35_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part35) = true := by rfl

def kid04_part36 : Audit := .cycle 10 4 false (0)
theorem kid04_part36_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part36) = true := by rfl

def kid04_part37 : Audit := .split 13 (2,true) (byMove [
.cycle 25 1 false (1),
.cycle 15 1 false (-3),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 8 16 false (3),
.cycle 9 6 false (1),
.cycle 23 1 false (-1),
.cycle 0 15 true (-2),
.cycle 17 1 false (-3),
.last 14 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 26 (5,true),
.last 16 (5,true),
.last 24 (5,true),
.cycle 25 10 false (1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part37_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part37) = true := by rfl

def kid04_part38 : Audit := .cycle 22 1 false (2)
theorem kid04_part38_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part38) = true := by rfl

def kid04_part39 : Audit := .cycle 12 1 false (-2)
theorem kid04_part39_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part39) = true := by rfl

def kid04_part40 : Audit := .cycle 12 1 false (-2)
theorem kid04_part40_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part40) = true := by rfl

def kid04_part41 : Audit := .cycle 11 1 false (-1)
theorem kid04_part41_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part41) = true := by rfl

def kid04_part42 : Audit := .cycle 8 13 false (3)
theorem kid04_part42_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part42) = true := by rfl

def kid04_part43 : Audit := .cycle 10 3 false (0)
theorem kid04_part43_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part43) = true := by rfl

def kid04_part44 : Audit := .split 12 (2,true) (byMove [
.cycle 21 1 false (1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 5 false (2),
.cycle 8 13 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 24 (5,true),
.last 23 (5,true),
.cycle 2 11 false (3),
.cycle 8 17 false (4),
.last 15 (5,true),
.last 23 (5,true)
])
theorem kid04_part44_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part44) = true := by rfl

def kid04_part45 : Audit := .cycle 0 13 true (-1)
theorem kid04_part45_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part45) = true := by rfl

def kid04_part46 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 9 6 false (1),
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 10 4 true (-1),
.cycle 9 7 true (-1),
.cycle 10 6 false (0),
.last 15 (2,true),
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (0),
.cycle 8 15 false (3),
.cycle 10 5 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.cycle 12 5 true (-1)
])
theorem kid04_part46_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part46) = true := by rfl

def kid04_part47 : Audit := .split 12 (5,true) (byMove [
.cycle 21 1 false (1),
.cycle 14 1 false (-2),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 true (-2),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 5 false (2),
.cycle 13 1 true (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 13 (2,true),
.cycle 22 1 false (2),
.cycle 10 3 false (0),
.cycle 11 3 false (0),
.cycle 8 39 false (4),
.cycle 10 15 false (3),
.cycle 2 11 false (3),
.cycle 8 17 false (4),
.cycle 14 2 true (-1),
.cycle 13 1 true (1)
])
theorem kid04_part47_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part47) = true := by rfl

def kid04_part23 : Audit := .split 11 (5,false) (byMove [(kid04_part24),(kid04_part25),(kid04_part26),(kid04_part27),(kid04_part28),(kid04_part29),(kid04_part30),(kid04_part31),(kid04_part32),(kid04_part33),(kid04_part34),(kid04_part35),(kid04_part36),(kid04_part37),(kid04_part38),(kid04_part39),(kid04_part40),(kid04_part41),(kid04_part42),(kid04_part43),(kid04_part44),(kid04_part45),(kid04_part46),(kid04_part47)])

theorem kid04_part23_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part23) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part24),(kid04_part25),(kid04_part26),(kid04_part27),(kid04_part28),(kid04_part29),(kid04_part30),(kid04_part31),(kid04_part32),(kid04_part33),(kid04_part34),(kid04_part35),(kid04_part36),(kid04_part37),(kid04_part38),(kid04_part39),(kid04_part40),(kid04_part41),(kid04_part42),(kid04_part43),(kid04_part44),(kid04_part45),(kid04_part46),(kid04_part47)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part24_checked

  · exact kid04_part30_checked

  · exact kid04_part36_checked

  · exact kid04_part42_checked

  · exact kid04_part25_checked

  · exact kid04_part31_checked

  · exact kid04_part37_checked

  · exact kid04_part43_checked

  · exact kid04_part26_checked

  · exact kid04_part32_checked

  · exact kid04_part38_checked

  · exact kid04_part44_checked

  · exact kid04_part27_checked

  · exact kid04_part33_checked

  · exact kid04_part39_checked

  · exact kid04_part45_checked

  · exact kid04_part28_checked

  · exact kid04_part34_checked

  · exact kid04_part40_checked

  · exact kid04_part46_checked

  · exact kid04_part29_checked

  · exact kid04_part35_checked

  · exact kid04_part41_checked

  · exact kid04_part47_checked

def kid04_part48 : Audit := .cycle 0 11 true (0)
theorem kid04_part48_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part48) = true := by rfl

def kid04_part49 : Audit := .cycle 1 10 true (0)
theorem kid04_part49_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part49) = true := by rfl

def kid04_part50 : Audit := .cycle 17 1 false (1)
theorem kid04_part50_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part50) = true := by rfl

def kid04_part51 : Audit := .cycle 21 1 false (3)
theorem kid04_part51_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part51) = true := by rfl

def kid04_part52 : Audit := .cycle 9 2 true (0)
theorem kid04_part52_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part52) = true := by rfl

def kid04_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 20 1 false (2),
.cycle 13 1 false (-1),
.split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 10 5 false (1),
.cycle 16 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 9 4 true (0),
.cycle 11 2 true (0)
]),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 10 5 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 9 4 true (0),
.cycle 11 2 true (0)
]),
.cycle 0 12 true (0),
.cycle 8 12 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 8 4 true (0),
.cycle 11 1 true (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 12 (2,true) (byMove [
.cycle 8 17 false (3),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.last 13 (5,true),
.cycle 10 5 false (1),
.cycle 16 1 false (-2),
.cycle 23 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.cycle 8 14 true (0),
.cycle 10 4 true (0),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.last 13 (5,true)
]),
.cycle 21 1 false (3),
.split 13 (5,true) (byMove [
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (0),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 8 14 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 6 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 23 1 false (3),
.cycle 12 2 true (0),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 8 18 true (0),
.cycle 9 5 true (0),
.cycle 11 3 true (0)
]),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.cycle 14 1 false (2),
.cycle 10 5 false (1),
.last 14 (2,true),
.cycle 23 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 8 14 true (0),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.cycle 11 3 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 8 16 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid04_part53_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part53) = true := by rfl

def kid04_part5 : Audit := .split 10 (4,true) (byMove [(kid04_part6),(kid04_part7),(kid04_part8),(kid04_part9),(kid04_part10),(kid04_part11),(kid04_part12),(kid04_part13),(kid04_part14),(kid04_part15),(kid04_part16),(kid04_part17),(kid04_part18),(kid04_part19),(kid04_part20),(kid04_part21),(kid04_part22),(kid04_part23),(kid04_part48),(kid04_part49),(kid04_part50),(kid04_part51),(kid04_part52),(kid04_part53)])

theorem kid04_part5_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (kid04_part5) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part6),(kid04_part7),(kid04_part8),(kid04_part9),(kid04_part10),(kid04_part11),(kid04_part12),(kid04_part13),(kid04_part14),(kid04_part15),(kid04_part16),(kid04_part17),(kid04_part18),(kid04_part19),(kid04_part20),(kid04_part21),(kid04_part22),(kid04_part23),(kid04_part48),(kid04_part49),(kid04_part50),(kid04_part51),(kid04_part52),(kid04_part53)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part6_checked

  · exact kid04_part12_checked

  · exact kid04_part18_checked

  · exact kid04_part48_checked

  · exact kid04_part7_checked

  · exact kid04_part13_checked

  · exact kid04_part19_checked

  · exact kid04_part49_checked

  · exact kid04_part8_checked

  · exact kid04_part14_checked

  · exact kid04_part20_checked

  · exact kid04_part50_checked

  · exact kid04_part9_checked

  · exact kid04_part15_checked

  · exact kid04_part21_checked

  · exact kid04_part51_checked

  · exact kid04_part10_checked

  · exact kid04_part16_checked

  · exact kid04_part22_checked

  · exact kid04_part52_checked

  · exact kid04_part11_checked

  · exact kid04_part17_checked

  · exact kid04_part23_checked

  · exact kid04_part53_checked

def kid04_part55 : Audit := .cycle 0 20 true (0)
theorem kid04_part55_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part55) = true := by rfl

def kid04_part56 : Audit := .cycle 10 9 false (0)
theorem kid04_part56_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part56) = true := by rfl

def kid04_part57 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 false (3),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 21 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 0 14 true (-1),
.cycle 24 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 11 3 false (0),
.cycle 21 1 false (-3),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 30 1 false (-2),
.cycle 1 13 false (3),
.cycle 23 1 false (-1),
.cycle 27 1 false (1),
.last 15 (5,true),
.cycle 9 5 false (1)
]),
.cycle 17 1 false (-3),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 20 1 false (0),
.cycle 24 1 false (2),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 23 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 15 (4,true),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 1 false (0),
.cycle 26 1 false (2),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid04_part57_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part57) = true := by rfl

def kid04_part58 : Audit := .cycle 0 11 true (0)
theorem kid04_part58_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part58) = true := by rfl

def kid04_part59 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 false (3),
.cycle 18 2 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 11 true (0),
.cycle 18 2 false (2),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 11 2 false (1),
.cycle 10 3 false (0),
.split 12 (2,true) (byMove [
.cycle 21 2 false (1),
.cycle 14 2 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (-1),
.last 23 (5,true),
.cycle 20 2 false (0),
.cycle 18 2 false (0),
.cycle 8 5 false (2),
.last 15 (5,true),
.cycle 15 2 false (-1),
.cycle 14 2 false (-2),
.cycle 24 2 false (2),
.cycle 22 2 false (2),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 23 7 false (1),
.cycle 24 2 false (-2),
.cycle 2 11 false (3),
.cycle 8 17 false (4),
.last 14 (5,true),
.cycle 16 2 false (-2)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 17 2 false (1),
.cycle 21 2 false (3),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 2 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 20 2 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 10 5 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 2 false (1),
.cycle 23 2 false (3),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid04_part59_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part59) = true := by rfl

def kid04_part60 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 false (3),
.cycle 19 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 19 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 22 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 28 1 false (-2),
.cycle 1 13 false (3),
.cycle 21 1 false (-1),
.cycle 25 1 false (1),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
]),
.split 12 (2,true) (byMove [
.cycle 22 1 false (0),
.cycle 15 1 false (-3),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 9 13 false (3),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 8 5 false (2),
.cycle 9 5 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 25 (4,true),
.cycle 25 1 false (-3),
.cycle 2 11 false (3),
.cycle 9 17 false (4),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 22 1 false (2),
.cycle 10 2 true (0),
.cycle 9 2 true (0)
])
theorem kid04_part60_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part60) = true := by rfl

def kid04_part61 : Audit := .cycle 0 10 true (0)
theorem kid04_part61_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part61) = true := by rfl

def kid04_part62 : Audit := .cycle 1 9 true (1)
theorem kid04_part62_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part62) = true := by rfl

def kid04_part63 : Audit := .cycle 20 1 false (2)
theorem kid04_part63_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part63) = true := by rfl

def kid04_part64 : Audit := .cycle 17 1 false (1)
theorem kid04_part64_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part64) = true := by rfl

def kid04_part65 : Audit := .cycle 8 2 true (1)
theorem kid04_part65_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part65) = true := by rfl

def kid04_part66 : Audit := .cycle 9 1 true (1)
theorem kid04_part66_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part66) = true := by rfl

def kid04_part67 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 12 5 false (0),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.split 18 (2,true) (byMove [
.cycle 10 15 false (1),
.cycle 11 8 false (1),
.cycle 21 1 false (-3),
.cycle 0 20 false (3),
.cycle 16 3 false (-2),
.last 19 (5,true),
.cycle 6 23 false (3),
.cycle 11 20 false (1),
.cycle 10 14 false (1),
.cycle 10 12 false (1),
.cycle 8 11 false (2),
.cycle 11 12 false (1),
.cycle 10 9 false (1),
.cycle 11 8 false (1),
.cycle 10 18 true (-4),
.cycle 10 16 true (-3),
.cycle 16 3 false (-2),
.last 19 (5,true),
.last 32 (5,true),
.last 31 (5,true),
.cycle 2 17 false (3),
.cycle 10 17 true (-3),
.last 20 (5,true),
.last 23 (5,true)
]),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.split 30 (5,true) (byMove [
.cycle 0 31 false (3),
.cycle 10 26 false (2),
.cycle 32 1 false (-2),
.cycle 31 1 false (-3),
.cycle 12 19 false (2),
.cycle 13 18 false (2),
.cycle 0 31 false (3),
.cycle 10 26 true (-2),
.cycle 32 1 false (0),
.cycle 31 1 false (-1),
.cycle 12 19 false (2),
.cycle 13 18 true (-2),
.cycle 14 17 false (2),
.last 32 (2,true),
.cycle 0 33 false (3),
.cycle 31 1 false (-3),
.last 38 (2,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 256, 128, 128, 256, 32768, 524290, 256, 32768, 33554432, 67108864, 2097152, 32768, 32768, 128, 33554432, 67108864, 134217728, 262144, 256, 1325694976, 33554432, 67108864, 134217728, 1325694976, 1325695232, 1325694976, 1073741824],[2, 32768, 1073741824, 1, 64, 128, 8192, 128, 1073741824, 4096, 64, 128, 524288, 32768, 1073741824, 262144, 16777216, 262144, 33554432, 32768, 1073741824, 16777216, 16777216, 128, 33554432, 1325694976, 1073741824, 16777216, 16777216, 1325695104, 1073741824],2143056384⟩,
.cycle 17 14 true (-2),
.cycle 1 30 false (3),
.cycle 10 25 false (2),
.cycle 10 29 true (-2),
.cycle 29 2 true (-2),
.cycle 9 22 false (2)
]),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 15 true (-2),
.split 18 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 10 14 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 12 7 false (0),
.cycle 13 6 false (-1),
.cycle 0 19 false (3),
.cycle 10 14 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 12 7 false (0),
.cycle 13 6 true (-2),
.cycle 14 5 false (-1),
.last 20 (2,true),
.cycle 0 21 false (3),
.cycle 19 1 false (-3),
.cycle 12 7 false (0),
.cycle 13 6 false (-1),
.cycle 17 14 true (-2),
.cycle 1 18 false (3),
.cycle 10 13 false (1),
.cycle 10 17 true (-2),
.cycle 17 2 true (-2),
.cycle 9 10 false (1)
]),
.cycle 9 8 false (1)
])
theorem kid04_part67_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part67) = true := by rfl

def kid04_part69 : Audit := .cycle 10 12 true (-3)
theorem kid04_part69_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part69) = true := by rfl

def kid04_part70 : Audit := .cycle 10 5 false (0)
theorem kid04_part70_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part70) = true := by rfl

def kid04_part71 : Audit := .cycle 17 1 false (-3)
theorem kid04_part71_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part71) = true := by rfl

def kid04_part72 : Audit := .split 34 (4,true) (byMove [
.last 55 (5,true),
.last 67 (5,true),
.cycle 36 1 false (-2),
.cycle 35 1 false (-3),
.last 84 (5,true),
.last 59 (5,true),
.cycle 16 22 true (-2),
.cycle 13 22 true (-3),
.last 53 (5,true),
.cycle 35 1 false (-1),
.cycle 13 28 true (-3),
.cycle 12 30 true (-3),
.cycle 33 3 false (-1),
.cycle 13 26 true (-3),
.cycle 15 26 true (-3),
.cycle 35 1 false (-3),
.last 68 (5,true),
.cycle 33 7 false (-1),
.cycle 16 22 true (-2),
.cycle 13 22 true (-3),
.last 53 (5,true),
.proven (BB6.Agent11Raw39B0RBPumps.M2.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M2.never m hm),
.last 36 (5,true),
.last 89 (5,true)
])
theorem kid04_part72_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part72) = true := by rfl

def kid04_part73 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.cycle 10 12 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 15 22 true (-3),
.cycle 10 12 true (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 5 false (-1),
.cycle 12 4 true (-3),
.cycle 15 3 false (-3),
.cycle 13 3 false (-2),
.cycle 15 26 true (-4),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 15 22 true (-3),
.cycle 1 15 false (3),
.cycle 10 11 false (0),
.cycle 48 15 true (2),
.last 17 (5,true),
.cycle 9 7 false (1)
])
theorem kid04_part73_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part73) = true := by rfl

def kid04_part74 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 false (3),
.cycle 10 12 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 34 (4,true),
.cycle 10 12 true (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 5 false (-1),
.cycle 12 4 true (-3),
.last 18 (4,true),
.cycle 13 3 false (-2),
.last 36 (4,true),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 34 (4,true),
.cycle 1 15 false (3),
.cycle 10 11 false (0),
.cycle 48 15 true (2),
.cycle 15 2 true (-3),
.cycle 9 7 false (1)
])
theorem kid04_part74_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part74) = true := by rfl

def kid04_part75 : Audit := .split 30 (5,true) (byMove [
.cycle 10 28 true (-3),
.last 87 (4,true),
.last 50 (4,true),
.last 50 (4,true),
.last 31 (4,true),
.cycle 9 23 false (5),
.cycle 15 16 true (-1),
.cycle 15 38 true (-1),
.cycle 186 1 false (-2),
.last 58 (4,true),
.proven (BB6.Agent11Raw39B0RBPumps.M3.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M3.never m hm),
.last 36 (4,true),
.cycle 6 25 false (5),
.proven (BB6.Agent11Raw39B0RBPumps.M4.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M4.never m hm),
.cycle 13 42 true (-3),
.cycle 13 42 true (-3),
.last 31 (4,true),
.last 46 (4,true),
.cycle 15 16 true (-1),
.last 48 (4,true),
.proven (BB6.Agent11Raw39B0RBPumps.M5.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M5.never m hm),
.cycle 16 18 true (0),
.cycle 29 2 true (0),
.last 33 (4,true)
])
theorem kid04_part75_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part75) = true := by rfl

def kid04_part76 : Audit := .split 33 (5,true) (byMove [
.cycle 90 11 true (4),
.cycle 60 11 true (2),
.cycle 35 1 false (-3),
.cycle 34 1 false (-4),
.cycle 64 11 true (2),
.cycle 52 11 true (2),
.cycle 13 22 true (-3),
.cycle 38 11 true (2),
.cycle 35 1 false (-1),
.cycle 34 1 false (-2),
.cycle 42 11 true (2),
.cycle 13 24 true (-3),
.last 36 (4,true),
.cycle 40 11 true (2),
.cycle 90 11 true (4),
.cycle 34 1 false (-4),
.cycle 44 11 true (2),
.cycle 31 6 false (-1),
.cycle 13 22 true (-3),
.cycle 38 11 true (2),
.cycle 48 11 true (2),
.cycle 13 24 true (-3),
.cycle 32 2 true (-3),
.last 45 (4,true)
])
theorem kid04_part76_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part76) = true := by rfl

def kid04_part77 : Audit := .cycle 10 11 false (0)
theorem kid04_part77_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part77) = true := by rfl

def kid04_part78 : Audit := .cycle 10 9 false (0)
theorem kid04_part78_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part78) = true := by rfl

def kid04_part79 : Audit := .cycle 8 7 false (2)
theorem kid04_part79_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part79) = true := by rfl

def kid04_part80 : Audit := .split 21 (5,true) (byMove [
.last 33 (4,true),
.last 32 (4,true),
.last 31 (4,true),
.cycle 33 3 true (0),
.last 24 (4,true),
.last 24 (4,true),
.last 36 (4,true),
.cycle 30 3 true (1),
.last 33 (4,true),
.last 31 (4,true),
.cycle 23 3 true (0),
.cycle 22 3 true (1),
.last 24 (4,true),
.cycle 22 3 true (0),
.last 38 (4,true),
.last 29 (4,true),
.last 24 (4,true),
.last 24 (4,true),
.last 33 (4,true),
.last 51 (4,true),
.cycle 29 3 true (0),
.cycle 33 3 true (2),
.cycle 21 2 true (1),
.last 28 (4,true)
])
theorem kid04_part80_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part80) = true := by rfl

def kid04_part81 : Audit := .cycle 10 6 false (0)
theorem kid04_part81_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part81) = true := by rfl

def kid04_part82 : Audit := .cycle 10 5 false (0)
theorem kid04_part82_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part82) = true := by rfl

def kid04_part83 : Audit := .cycle 53 15 true (-1)
theorem kid04_part83_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part83) = true := by rfl

def kid04_part84 : Audit := .cycle 44 13 true (2)
theorem kid04_part84_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part84) = true := by rfl

def kid04_part85 : Audit := .split 15 (4,true) (byMove [
.cycle 13 8 true (-4),
.cycle 7 16 false (3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 44 13 true (2),
.cycle 10 6 false (0),
.cycle 11 6 false (-1),
.far true 2 ⟨0,[0, 1, 0, 1],[656, 656, 512, 512, 32, 128, 512, 640, 640, 512, 32, 128, 4096],[672, 16, 1024, 672, 512, 4096, 32, 16, 1024, 640, 640, 4096, 4096],4096⟩,
.cycle 11 6 true (-3),
.last 16 (5,true),
.cycle 15 3 false (-3),
.cycle 13 3 false (-2),
.far true 2 ⟨0,[0, 1, 0, 1],[1296, 1424, 512, 512, 32, 128, 256, 256, 384, 512, 32, 128, 4096],[416, 16, 1024, 416, 256, 4096, 32, 16, 1024, 384, 256, 4096, 4096],4096⟩,
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 35 (5,true),
.cycle 1 17 false (3),
.cycle 14 2 true (-3),
.last 34 (5,true),
.last 18 (5,true),
.last 16 (5,true)
])
theorem kid04_part85_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part85) = true := by rfl

def kid04_part86 : Audit := .split 15 (5,true) (byMove [
.cycle 13 8 true (-4),
.cycle 7 16 false (3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 44 13 true (2),
.cycle 10 6 false (0),
.cycle 12 5 false (-2),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 128, 16777217, 524288, 1048576, 32768, 33554434, 51380224, 16777216, 524288, 1048576, 134217728, 1048576, 128, 16777216, 137438953472, 274877906944, 8589934592, 33554432, 51380224, 281543712964609, 128, 256, 134217728, 51380224, 128, 16777217, 137438953472, 274877906944, 549755813888, 1048576, 281612415664256, 330343166017923, 137438953472, 274877906944, 35184372088832, 330343166017923, 330343166017923, 330343166017923, 137438953472, 274877906944, 549755813888, 330343166017923, 330343166017923, 330343166017923, 281474976710656],[2, 1048576, 33554434, 1, 281474976710656, 8, 8192, 281474976710656, 16777217, 4096, 281474976710656, 32768, 33554432, 8589934976, 33554432, 16777216, 281474976710656, 134217728, 2147483648, 281474976710656, 16777216, 1073741824, 281474976710656, 8589934592, 33554432, 1048576, 33554434, 16777216, 281474976710656, 134217728, 137438953472, 8589934976, 290271103287298, 68719476736, 281474976710656, 549755813888, 8796093022208, 330343166017923, 330343166017923, 4398046511104, 281474976710656, 35184372088832, 137438953472, 330343166017923, 330343166017923, 68719476736, 281474976710656, 549755813888, 281474976710656],562940298924096⟩,
.last 16 (4,true),
.cycle 26 5 true (0),
.last 18 (4,true),
.cycle 13 3 false (-2),
.cycle 105 15 true (1),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 13 24 true (-3),
.last 17 (4,true),
.cycle 14 2 true (-3),
.cycle 18 20 true (0),
.last 16 (4,true),
.last 19 (4,true)
])
theorem kid04_part86_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part86) = true := by rfl

def kid04_part87 : Audit := .split 29 (4,true) (byMove [
.last 49 (5,true),
.cycle 40 17 false (0),
.cycle 14 16 true (-2),
.cycle 15 16 true (-1),
.cycle 32 17 false (-1),
.last 30 (5,true),
.cycle 33 22 true (-1),
.cycle 16 14 true (0),
.cycle 0 32 true (-3),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 64, 128, 256, 32768, 524290, 1073741824, 64, 33554432, 67108864, 2097152, 256, 128, 64, 33554432, 67108864, 134217728, 64, 128, 16777216, 33554432, 67108864, 134217728, 1325703616, 1325703616, 1325703616, 1073741824],[2, 256, 64, 1, 8, 1073741824, 8192, 256, 64, 4096, 32768, 1073741824, 524288, 1073741824, 16777216, 262144, 2097152, 1073741824, 33554432, 256, 16777216, 16777216, 134217728, 1073741824, 33554432, 1325703616, 16777216, 16777216, 134217728, 1073741824, 1073741824],2140943872⟩,
.cycle 32 11 false (0),
.cycle 16 27 true (0),
.last 33 (5,true),
.cycle 30 7 false (0),
.cycle 16 16 true (0),
.cycle 16 16 true (0),
.cycle 31 9 false (-1),
.last 30 (5,true),
.cycle 18 15 true (1),
.cycle 16 14 true (0),
.cycle 15 34 true (-1),
.cycle 4 62 false (5),
.last 31 (5,true),
.last 54 (5,true)
])
theorem kid04_part87_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part87) = true := by rfl

def kid04_part88 : Audit := .split 32 (4,true) (byMove [
.cycle 34 39 true (-2),
.cycle 10 137 false (6),
.cycle 83 75 true (-5),
.cycle 13 22 true (-3),
.cycle 33 15 false (-2),
.last 33 (5,true),
.cycle 15 22 true (-2),
.cycle 13 20 true (-3),
.cycle 0 51 true (-3),
.cycle 10 53 true (-4),
.last 1270 (5,true),
.cycle 12 26 true (-3),
.cycle 48 3 false (-4),
.last 958 (5,true),
.cycle 69 19 true (1),
.cycle 13 22 true (-3),
.cycle 32 11 false (-2),
.last 33 (5,true),
.cycle 15 22 true (-2),
.cycle 13 20 true (-3),
.cycle 16 33 true (-2),
.cycle 4 29 false (5),
.last 34 (5,true),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[4194320, 144, 32768, 512, 32, 128, 4194320, 4194320, 128, 32768, 32, 8192, 4194320, 4194320, 4194448, 32768, 8388608, 8192, 4194320, 4194320, 32768, 512, 32, 128, 16777216],[4194352, 16, 4194320, 32, 4194320, 16777216, 32, 16, 4194320, 160, 16777216, 16777216, 32, 4194304, 4194320, 128, 16777216, 16777216, 32, 16, 4194320, 32, 4194304, 16777216, 16777216],16777216⟩
])
theorem kid04_part88_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part88) = true := by rfl

def kid04_part89 : Audit := .cycle 2 13 false (3)
theorem kid04_part89_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part89) = true := by rfl

def kid04_part90 : Audit := .cycle 18 14 true (0)
theorem kid04_part90_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part90) = true := by rfl

def kid04_part91 : Audit := .split 16 (5,true) (byMove [
.cycle 10 14 true (-3),
.cycle 10 7 false (0),
.cycle 21 1 false (-3),
.last 36 (4,true),
.last 17 (4,true),
.cycle 12 6 false (-1),
.cycle 15 18 true (-2),
.cycle 40 13 true (2),
.cycle 10 13 false (0),
.cycle 10 11 false (0),
.cycle 8 9 false (2),
.last 25 (4,true),
.cycle 10 8 false (0),
.cycle 10 7 false (0),
.last 18 (4,true),
.cycle 48 15 true (2),
.last 17 (4,true),
.last 21 (4,true),
.last 33 (4,true),
.last 34 (4,true),
.cycle 2 15 false (3),
.cycle 20 16 true (0),
.cycle 15 2 true (-2),
.last 19 (4,true)
])
theorem kid04_part91_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part91) = true := by rfl

def kid04_part92 : Audit := .split 17 (4,true) (byMove [
.last 37 (5,true),
.cycle 10 14 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.cycle 12 6 false (-1),
.proven (BB6.Agent11Raw39B0RBPumps.M12.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M12.never m hm),
.last 25 (5,true),
.cycle 24 1 false (2),
.cycle 18 1 false (-2),
.cycle 11 7 false (-1),
.last 21 (5,true),
.cycle 16 3 false (-2),
.cycle 13 5 false (-1),
.last 32 (5,true),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.last 21 (5,true),
.cycle 24 15 true (0),
.last 25 (5,true),
.last 53 (5,true),
.cycle 10 11 false (0),
.last 19 (5,true),
.cycle 9 9 false (1)
])
theorem kid04_part92_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part92) = true := by rfl

def kid04_part68 : Audit := .split 14 (2,true) (byMove [(kid04_part69),(kid04_part70),(kid04_part71),(kid04_part72),(kid04_part73),(kid04_part74),(kid04_part75),(kid04_part76),(kid04_part77),(kid04_part78),(kid04_part79),(kid04_part80),(kid04_part81),(kid04_part82),(kid04_part83),(kid04_part84),(kid04_part85),(kid04_part86),(kid04_part87),(kid04_part88),(kid04_part89),(kid04_part90),(kid04_part91),(kid04_part92)])

theorem kid04_part68_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part68) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid04_part69),(kid04_part70),(kid04_part71),(kid04_part72),(kid04_part73),(kid04_part74),(kid04_part75),(kid04_part76),(kid04_part77),(kid04_part78),(kid04_part79),(kid04_part80),(kid04_part81),(kid04_part82),(kid04_part83),(kid04_part84),(kid04_part85),(kid04_part86),(kid04_part87),(kid04_part88),(kid04_part89),(kid04_part90),(kid04_part91),(kid04_part92)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part69_checked

  · exact kid04_part75_checked

  · exact kid04_part81_checked

  · exact kid04_part87_checked

  · exact kid04_part70_checked

  · exact kid04_part76_checked

  · exact kid04_part82_checked

  · exact kid04_part88_checked

  · exact kid04_part71_checked

  · exact kid04_part77_checked

  · exact kid04_part83_checked

  · exact kid04_part89_checked

  · exact kid04_part72_checked

  · exact kid04_part78_checked

  · exact kid04_part84_checked

  · exact kid04_part90_checked

  · exact kid04_part73_checked

  · exact kid04_part79_checked

  · exact kid04_part85_checked

  · exact kid04_part91_checked

  · exact kid04_part74_checked

  · exact kid04_part80_checked

  · exact kid04_part86_checked

  · exact kid04_part92_checked

def kid04_part94 : Audit := .cycle 0 26 true (-1)
theorem kid04_part94_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part94) = true := by rfl

def kid04_part95 : Audit := .cycle 0 14 true (-1)
theorem kid04_part95_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part95) = true := by rfl

def kid04_part96 : Audit := .cycle 12 1 false (0)
theorem kid04_part96_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part96) = true := by rfl

def kid04_part97 : Audit := .cycle 11 1 false (-1)
theorem kid04_part97_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part97) = true := by rfl

def kid04_part98 : Audit := .split 18 (4,true) (byMove [
.cycle 0 31 true (-3),
.cycle 0 24 false (3),
.cycle 0 24 false (3),
.cycle 0 20 true (-3),
.cycle 0 24 false (3),
.last 19 (5,true),
.last 31 (5,true),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 128, 1, 524288, 1048576, 32768, 33554434, 281474976710656, 1048832, 524288, 1048576, 134217728, 1048576, 8589967360, 16777216, 137438953472, 274877906944, 8589934592, 33554432, 281474976710656, 281474976710912, 128, 256, 134217728, 1048832, 128, 16777216, 137438953472, 274877906944, 549755813888, 1048576, 281474976743424, 68719476736, 137438953472, 274877906944, 35184372088832, 290683387642112, 281612415664128, 286147902177536, 137438953472, 274877906944, 549755813888, 281749855666432, 316805377720320, 68719476736, 281474976710656],[2, 1048576, 1048576, 1, 2, 281474976710656, 8192, 256, 256, 4096, 8192, 281474976710656, 33554432, 281474976710656, 281474976710656, 16777216, 33554432, 281474976710656, 2147483648, 1048832, 1048832, 1073741824, 2147483648, 281474976710656, 33554432, 1048576, 1048576, 16777216, 33554432, 281474976710656, 137438953472, 281474976710656, 281474976710656, 68719476736, 137438953472, 281474976710656, 8796093022208, 281749855666432, 281749855666432, 4398046511104, 8796093022208, 281474976710656, 137438953472, 281749854617600, 281749854617600, 68719476736, 137438953472, 281474976710656, 281474976710656],562940303119424⟩,
.cycle 11 15 true (-3),
.cycle 0 28 true (-3),
.cycle 8 11 false (2),
.far true 2 ⟨0,[0, 1, 0, 1],[272, 272, 512, 512, 32, 256, 256, 256, 256, 512, 32, 256, 4096],[288, 16, 16, 288, 256, 4096, 32, 16, 16, 256, 4096, 4096, 4096],4096⟩,
.cycle 0 25 false (3),
.cycle 11 9 false (1),
.cycle 10 9 false (1),
.cycle 0 32 true (-3),
.cycle 19 7 false (-1),
.last 19 (5,true),
.cycle 18 15 true (0),
.cycle 16 14 true (-1),
.cycle 2 17 false (3),
.cycle 0 33 true (-3),
.last 20 (5,true),
.cycle 9 13 false (1)
])
theorem kid04_part98_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part98) = true := by rfl

def kid04_part99 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 0 28 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 21 false (3),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.cycle 0 28 true (-2),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 0 21 true (-2),
.cycle 0 20 true (-2),
.cycle 14 3 false (1),
.last 19 (5,true),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 11 7 false (1),
.cycle 0 32 true (-2),
.last 28 (5,true),
.cycle 1 16 true (-2),
.cycle 0 27 true (-2),
.cycle 0 31 true (-2),
.last 18 (5,true),
.cycle 9 8 true (-2)
])
theorem kid04_part99_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part99) = true := by rfl

def kid04_part100 : Audit := .cycle 0 23 true (0)
theorem kid04_part100_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part100) = true := by rfl

def kid04_part101 : Audit := .cycle 0 16 true (-2)
theorem kid04_part101_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part101) = true := by rfl

def kid04_part102 : Audit := .cycle 13 1 false (3)
theorem kid04_part102_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part102) = true := by rfl

def kid04_part103 : Audit := .cycle 0 12 true (0)
theorem kid04_part103_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part103) = true := by rfl

def kid04_part104 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 0 23 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 16 true (-2),
.cycle 0 15 true (-1),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 11 3 false (1),
.cycle 8 6 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 7 false (1),
.cycle 0 27 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 0 22 true (0),
.cycle 0 26 true (0),
.last 13 (5,true),
.cycle 9 3 true (0)
])
theorem kid04_part104_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part104) = true := by rfl

def kid04_part105 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 0 23 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 16 true (-2),
.cycle 0 15 true (-1),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 18 (4,true),
.cycle 0 27 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 0 22 true (0),
.cycle 0 26 true (0),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part105_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part105) = true := by rfl

def kid04_part106 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.last 31 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 37 (5,true),
.last 23 (5,true),
.cycle 0 17 true (-1),
.cycle 0 22 true (-2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 0 25 true (-2),
.cycle 0 29 true (-1),
.cycle 11 3 false (0),
.last 45 (5,true),
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.cycle 11 7 false (0),
.cycle 0 26 true (-3),
.last 31 (5,true),
.last 19 (5,true),
.cycle 0 16 true (-1),
.cycle 0 22 true (-2),
.last 15 (5,true),
.cycle 9 5 false (1)
])
theorem kid04_part106_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part106) = true := by rfl

def kid04_part107 : Audit := .split 22 (4,true) (byMove [
.cycle 0 39 true (-4),
.cycle 13 16 true (-4),
.cycle 24 1 false (-2),
.cycle 23 1 false (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M15.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M15.never m hm),
.cycle 15 8 true (-4),
.cycle 0 29 true (-4),
.cycle 11 12 true (-4),
.cycle 0 37 true (-4),
.cycle 23 1 false (-1),
.cycle 0 41 true (-4),
.cycle 0 32 true (-4),
.cycle 21 3 false (-1),
.cycle 11 12 false (0),
.cycle 0 35 true (-4),
.cycle 23 1 false (-3),
.cycle 21 7 false (-1),
.cycle 11 16 true (-4),
.cycle 20 19 true (-2),
.cycle 19 4 true (-2),
.cycle 0 37 true (-4),
.cycle 0 44 true (-4),
.last 24 (5,true),
.cycle 9 14 false (1)
])
theorem kid04_part107_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part107) = true := by rfl

def kid04_part108 : Audit := .cycle 0 25 true (-1)
theorem kid04_part108_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part108) = true := by rfl

def kid04_part109 : Audit := .cycle 11 1 false (-1)
theorem kid04_part109_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part109) = true := by rfl

def kid04_part110 : Audit := .split 17 (4,true) (byMove [
.cycle 35 8 true (-3),
.cycle 0 79 true (-4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.far true 2 ⟨0,[0, 1, 0, 1],[1040, 1280, 512, 512, 32, 256, 16, 16, 256, 512, 32, 256, 4096],[288, 16, 1024, 32, 16, 4096, 32, 16, 1024, 256, 16, 4096, 4096],4096⟩,
.last 25 (5,true),
.cycle 0 21 true (-3),
.cycle 0 26 true (-3),
.cycle 0 20 true (-3),
.cycle 18 1 false (0),
.cycle 0 29 true (-3),
.cycle 0 33 true (-3),
.cycle 15 3 false (0),
.cycle 17 3 false (-1),
.cycle 0 25 true (-3),
.cycle 18 1 false (-2),
.cycle 11 7 false (0),
.cycle 0 34 true (-3),
.last 36 (5,true),
.cycle 16 18 true (-1),
.far true 2 ⟨0,[0, 1, 0, 1],[1024, 1280, 512, 512, 32, 256, 1280, 0, 256, 512, 32, 256, 4096],[288, 16, 1024, 288, 1280, 4096, 32, 16, 1024, 256, 0, 4096, 4096],4096⟩,
.cycle 0 26 true (-3),
.last 19 (5,true),
.cycle 9 9 false (1)
])
theorem kid04_part110_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part110) = true := by rfl

def kid04_part111 : Audit := .cycle 0 20 true (-2)
theorem kid04_part111_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part111) = true := by rfl

def kid04_part112 : Audit := .cycle 0 23 true (0)
theorem kid04_part112_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part112) = true := by rfl

def kid04_part113 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 0 24 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 false (3),
.cycle 0 16 true (-2),
.cycle 0 13 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 17 true (-1),
.cycle 0 16 true (0),
.cycle 11 3 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 128, 1, 128, 256, 32768, 524290, 1073741824, 256, 524288, 1048576, 2097152, 256, 32768, 262144, 33554432, 67108864, 134217728, 33554560, 1107296256, 16777472, 33554432, 67108864, 134217728, 1325695360, 1325695360, 1325695360, 1073741824],[2, 256, 128, 1, 128, 1073741824, 8192, 256, 128, 4096, 128, 1073741824, 524288, 1073741824, 524288, 262144, 128, 1073741824, 33554432, 256, 33554432, 16777216, 1107296256, 1073741824, 33554432, 1325695360, 33554432, 16777216, 1325695360, 1073741824, 1073741824],2147382784⟩,
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 0 28 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 0 23 true (-1),
.cycle 0 27 true (0),
.last 14 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part113_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part113) = true := by rfl

def kid04_part114 : Audit := .cycle 2 10 true (0)
theorem kid04_part114_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part114) = true := by rfl

def kid04_part115 : Audit := .cycle 0 12 true (0)
theorem kid04_part115_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part115) = true := by rfl

def kid04_part116 : Audit := .split 11 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 17 false (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 0 17 false (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.last 27 (5,true),
.cycle 0 21 true (-1),
.cycle 8 4 true (0),
.cycle 0 15 true (0),
.cycle 0 18 true (-2),
.last 21 (5,true),
.cycle 10 2 true (0),
.cycle 0 25 true (0),
.cycle 12 7 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 26 true (0),
.last 13 (5,true),
.cycle 9 3 true (0)
])
theorem kid04_part116_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part116) = true := by rfl

def kid04_part117 : Audit := .split 11 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 17 false (3),
.cycle 9 4 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 16 true (-2),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 9 58 true (-1),
.cycle 0 21 true (-1),
.cycle 8 4 true (0),
.cycle 0 15 true (0),
.cycle 0 18 true (-2),
.last 24 (4,true),
.cycle 10 2 true (0),
.cycle 0 25 true (0),
.last 12 (4,true),
.cycle 0 22 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 26 true (0),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part117_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part117) = true := by rfl

def kid04_part93 : Audit := .split 10 (2,true) (byMove [(kid04_part94),(kid04_part95),(kid04_part96),(kid04_part97),(kid04_part98),(kid04_part99),(kid04_part100),(kid04_part101),(kid04_part102),(kid04_part103),(kid04_part104),(kid04_part105),(kid04_part106),(kid04_part107),(kid04_part108),(kid04_part109),(kid04_part110),(kid04_part111),(kid04_part112),(kid04_part113),(kid04_part114),(kid04_part115),(kid04_part116),(kid04_part117)])

theorem kid04_part93_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part93) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid04_part94),(kid04_part95),(kid04_part96),(kid04_part97),(kid04_part98),(kid04_part99),(kid04_part100),(kid04_part101),(kid04_part102),(kid04_part103),(kid04_part104),(kid04_part105),(kid04_part106),(kid04_part107),(kid04_part108),(kid04_part109),(kid04_part110),(kid04_part111),(kid04_part112),(kid04_part113),(kid04_part114),(kid04_part115),(kid04_part116),(kid04_part117)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part94_checked

  · exact kid04_part100_checked

  · exact kid04_part106_checked

  · exact kid04_part112_checked

  · exact kid04_part95_checked

  · exact kid04_part101_checked

  · exact kid04_part107_checked

  · exact kid04_part113_checked

  · exact kid04_part96_checked

  · exact kid04_part102_checked

  · exact kid04_part108_checked

  · exact kid04_part114_checked

  · exact kid04_part97_checked

  · exact kid04_part103_checked

  · exact kid04_part109_checked

  · exact kid04_part115_checked

  · exact kid04_part98_checked

  · exact kid04_part104_checked

  · exact kid04_part110_checked

  · exact kid04_part116_checked

  · exact kid04_part99_checked

  · exact kid04_part105_checked

  · exact kid04_part111_checked

  · exact kid04_part117_checked

def kid04_part118 : Audit := .cycle 21 1 false (1)
theorem kid04_part118_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part118) = true := by rfl

def kid04_part120 : Audit := .split 13 (2,true) (byMove [
.last 25 (5,true),
.cycle 0 16 false (3),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 23 2 false (1),
.last 14 (5,true),
.cycle 0 14 true (-1),
.last 24 (5,true),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 8 12 true (-1),
.last 16 (5,true),
.last 17 (5,true),
.cycle 0 20 true (-2),
.cycle 20 2 false (0),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[68719476736, 65536, 35184372088832, 32768, 32, 65536, 283778979204160, 283778979204160, 283779113422400, 134217728, 2048, 268435456, 1, 4194304, 1073741824, 35184372088832, 2199023255552, 70368744177664, 16777280, 4194304, 283778979204160, 134217728, 34359738368, 268435456, 283778979204160, 283778979204160, 283779113422400, 512, 536870912, 1024, 1073741824, 283778979204160, 512, 2097152, 2048, 4194304, 1073741824, 34359738368, 134217728, 2097152, 536870912, 4194304, 16777216, 65536, 34359738368, 134217728, 536870912, 268435456, 281474976710656],[2199023255552, 16, 32768, 1073741824, 1, 281474976710656, 283778979204160, 1024, 134217728, 283778979204160, 64, 281474976710656, 32, 1099511627776, 35184372088832, 4194304, 68719476736, 281474976710656, 536872960, 17179869184, 134217728, 4194304, 1073741824, 281474976710656, 283778979204160, 268435456, 512, 283778979204160, 16777216, 281474976710656, 34359738368, 1024, 2097152, 283778979204160, 64, 281474976710656, 34359738368, 268435456, 2097152, 68719476736, 16777216, 281474976710656, 536870912, 268435456, 134217728, 65536, 16777216, 281474976710656, 281474976710656],285875289457088⟩,
.cycle 10 8 true (-1),
.last 14 (5,true),
.cycle 12 14 true (0),
.cycle 12 13 true (0),
.cycle 2 24 true (-1),
.cycle 4 28 true (-1),
.last 15 (5,true),
.cycle 12 5 true (0)
])
theorem kid04_part120_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part120) = true := by rfl

def kid04_part121 : Audit := .cycle 0 14 true (-1)
theorem kid04_part121_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part121) = true := by rfl

def kid04_part122 : Audit := .cycle 12 1 false (0)
theorem kid04_part122_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part122) = true := by rfl

def kid04_part123 : Audit := .cycle 11 1 false (-1)
theorem kid04_part123_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part123) = true := by rfl

def kid04_part124 : Audit := .cycle 11 2 false (-1)
theorem kid04_part124_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part124) = true := by rfl

def kid04_part125 : Audit := .cycle 11 2 false (-1)
theorem kid04_part125_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part125) = true := by rfl

def kid04_part126 : Audit := .cycle 19 2 false (3)
theorem kid04_part126_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part126) = true := by rfl

def kid04_part127 : Audit := .cycle 12 2 false (0)
theorem kid04_part127_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part127) = true := by rfl

def kid04_part128 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 19 2 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 19 2 false (3),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 12 2 false (2),
.cycle 16 1 false (2),
.cycle 15 2 false (-1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 2 false (2),
.cycle 22 2 false (4),
.last 13 (5,true),
.cycle 9 3 true (0)
])
theorem kid04_part128_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part128) = true := by rfl

def kid04_part129 : Audit := .cycle 0 12 true (0)
theorem kid04_part129_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part129) = true := by rfl

def kid04_part130 : Audit := .cycle 12 2 false (2)
theorem kid04_part130_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part130) = true := by rfl

def kid04_part131 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 19 2 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 19 2 false (3),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 12 2 false (2),
.cycle 15 2 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 2 false (2),
.cycle 22 2 false (4),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part131_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part131) = true := by rfl

def kid04_part132 : Audit := .cycle 10 3 false (0)
theorem kid04_part132_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part132) = true := by rfl

def kid04_part133 : Audit := .split 12 (2,true) (byMove [
.cycle 24 2 false (2),
.cycle 14 2 false (-2),
.cycle 15 1 false (-1),
.cycle 0 20 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 100 (5,true),
.last 15 (5,true),
.cycle 22 2 false (0),
.cycle 0 14 true (-1),
.cycle 20 2 false (-2),
.last 13 (5,true),
.cycle 15 2 false (-1),
.cycle 14 2 false (-2),
.cycle 18 2 false (0),
.cycle 16 2 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 24 (5,true),
.cycle 16 2 false (-2),
.cycle 24 2 false (-2),
.cycle 0 14 true (-1),
.last 19 (5,true),
.last 13 (5,true)
])
theorem kid04_part133_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part133) = true := by rfl

def kid04_part134 : Audit := .cycle 21 2 false (3)
theorem kid04_part134_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part134) = true := by rfl

def kid04_part135 : Audit := .cycle 11 1 false (-1)
theorem kid04_part135_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part135) = true := by rfl

def kid04_part136 : Audit := .cycle 11 2 false (-1)
theorem kid04_part136_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part136) = true := by rfl

def kid04_part137 : Audit := .cycle 11 2 false (-1)
theorem kid04_part137_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part137) = true := by rfl

def kid04_part138 : Audit := .split 22 (5,true) (byMove [
.cycle 0 27 true (-1),
.cycle 30 2 false (0),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 23 2 false (-1),
.cycle 23 2 false (-1),
.cycle 0 26 true (0),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.cycle 23 2 false (1),
.cycle 23 2 false (1),
.last 28 (2,true),
.last 24 (2,true),
.last 51 (2,true),
.cycle 23 1 false (-1),
.cycle 23 2 false (-1),
.cycle 23 2 false (-1),
.cycle 0 26 true (0),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 27 2 false (1),
.cycle 21 2 true (0),
.cycle 9 20 true (0)
])
theorem kid04_part138_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part138) = true := by rfl

def kid04_part139 : Audit := .cycle 1 12 true (0)
theorem kid04_part139_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part139) = true := by rfl

def kid04_part140 : Audit := .split 11 (2,true) (byMove [
.cycle 20 2 false (2),
.cycle 13 2 false (-1),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 19 2 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.last 22 (5,true),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 8 4 true (0),
.last 14 (5,true),
.cycle 14 2 false (0),
.cycle 13 2 false (-1),
.cycle 23 2 false (3),
.cycle 21 2 false (3),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 4 24 true (0),
.last 13 (5,true),
.cycle 9 3 true (0)
])
theorem kid04_part140_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part140) = true := by rfl

def kid04_part141 : Audit := .cycle 0 12 true (0)
theorem kid04_part141_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part141) = true := by rfl

def kid04_part142 : Audit := .split 13 (5,true) (byMove [
.cycle 22 2 false (2),
.cycle 15 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 14 true (0),
.last 26 (2,true),
.cycle 21 2 false (1),
.cycle 19 2 false (1),
.cycle 8 6 true (0),
.cycle 17 2 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.last 14 (2,true),
.cycle 23 2 false (3),
.cycle 10 4 true (0),
.cycle 15 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 4 28 true (0),
.cycle 12 2 true (1),
.cycle 9 5 true (0)
])
theorem kid04_part142_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part142) = true := by rfl

def kid04_part143 : Audit := .split 11 (5,true) (byMove [
.cycle 20 2 false (2),
.cycle 13 2 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.last 24 (2,true),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 8 4 true (0),
.cycle 15 2 false (1),
.cycle 14 2 false (0),
.cycle 13 2 false (-1),
.last 12 (2,true),
.cycle 21 2 false (3),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 4 24 true (0),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part143_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part143) = true := by rfl

def kid04_part119 : Audit := .split 10 (4,true) (byMove [(kid04_part120),(kid04_part121),(kid04_part122),(kid04_part123),(kid04_part124),(kid04_part125),(kid04_part126),(kid04_part127),(kid04_part128),(kid04_part129),(kid04_part130),(kid04_part131),(kid04_part132),(kid04_part133),(kid04_part134),(kid04_part135),(kid04_part136),(kid04_part137),(kid04_part138),(kid04_part139),(kid04_part140),(kid04_part141),(kid04_part142),(kid04_part143)])

theorem kid04_part119_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part119) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part120),(kid04_part121),(kid04_part122),(kid04_part123),(kid04_part124),(kid04_part125),(kid04_part126),(kid04_part127),(kid04_part128),(kid04_part129),(kid04_part130),(kid04_part131),(kid04_part132),(kid04_part133),(kid04_part134),(kid04_part135),(kid04_part136),(kid04_part137),(kid04_part138),(kid04_part139),(kid04_part140),(kid04_part141),(kid04_part142),(kid04_part143)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part120_checked

  · exact kid04_part126_checked

  · exact kid04_part132_checked

  · exact kid04_part138_checked

  · exact kid04_part121_checked

  · exact kid04_part127_checked

  · exact kid04_part133_checked

  · exact kid04_part139_checked

  · exact kid04_part122_checked

  · exact kid04_part128_checked

  · exact kid04_part134_checked

  · exact kid04_part140_checked

  · exact kid04_part123_checked

  · exact kid04_part129_checked

  · exact kid04_part135_checked

  · exact kid04_part141_checked

  · exact kid04_part124_checked

  · exact kid04_part130_checked

  · exact kid04_part136_checked

  · exact kid04_part142_checked

  · exact kid04_part125_checked

  · exact kid04_part131_checked

  · exact kid04_part137_checked

  · exact kid04_part143_checked

def kid04_part145 : Audit := .split 13 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 0, 8, 256, 128, 256, 8, 2, 8, 256, 4096],[2, 0, 256, 1, 4096, 256, 2, 4096, 256, 1, 4096, 256, 4096],4096⟩,
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 24 1 false (0),
.cycle 0 14 true (-1),
.cycle 0 31 false (4),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 8 12 true (-1),
.cycle 18 21 true (0),
.cycle 0 18 false (3),
.last 15 (4,true),
.cycle 21 1 false (-1),
.cycle 38 45 true (-2),
.last 14 (4,true),
.cycle 10 8 true (-1),
.cycle 12 14 true (0),
.cycle 12 13 true (0),
.cycle 2 24 true (-1),
.cycle 15 17 true (-1),
.last 31 (4,true),
.cycle 12 5 true (0)
])
theorem kid04_part145_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part145) = true := by rfl

def kid04_part146 : Audit := .cycle 0 14 true (-1)
theorem kid04_part146_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part146) = true := by rfl

def kid04_part147 : Audit := .cycle 12 1 false (0)
theorem kid04_part147_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part147) = true := by rfl

def kid04_part148 : Audit := .cycle 11 1 false (-1)
theorem kid04_part148_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part148) = true := by rfl

def kid04_part149 : Audit := .cycle 12 1 false (-2)
theorem kid04_part149_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part149) = true := by rfl

def kid04_part150 : Audit := .cycle 11 1 false (-1)
theorem kid04_part150_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part150) = true := by rfl

def kid04_part151 : Audit := .cycle 20 1 false (2)
theorem kid04_part151_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part151) = true := by rfl

def kid04_part152 : Audit := .cycle 13 1 false (-1)
theorem kid04_part152_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part152) = true := by rfl

def kid04_part153 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 15 1 false (3),
.cycle 9 3 true (0)
])
theorem kid04_part153_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part153) = true := by rfl

def kid04_part154 : Audit := .cycle 0 12 true (0)
theorem kid04_part154_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part154) = true := by rfl

def kid04_part155 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 11 3 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 15 1 false (1),
.cycle 9 3 true (0)
])
theorem kid04_part155_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part155) = true := by rfl

def kid04_part156 : Audit := .cycle 12 1 false (2)
theorem kid04_part156_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part156) = true := by rfl

def kid04_part157 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 0 17 true (-1),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.last 15 (2,true),
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 0 39 true (-2),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 19 1 false (-1),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
])
theorem kid04_part157_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part157) = true := by rfl

def kid04_part158 : Audit := .split 12 (2,true) (byMove [
.cycle 25 1 false (1),
.cycle 15 1 false (-3),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 148 1 false (-6),
.cycle 89 1 false (-7),
.cycle 23 1 false (-1),
.cycle 0 14 true (-1),
.last 13 (4,true),
.cycle 21 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 27 1 false (-3),
.last 14 (4,true),
.cycle 25 1 false (-3),
.cycle 0 14 true (-1),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid04_part158_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part158) = true := by rfl

def kid04_part159 : Audit := .cycle 22 1 false (2)
theorem kid04_part159_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part159) = true := by rfl

def kid04_part160 : Audit := .cycle 11 1 false (-1)
theorem kid04_part160_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part160) = true := by rfl

def kid04_part161 : Audit := .cycle 12 1 false (-2)
theorem kid04_part161_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part161) = true := by rfl

def kid04_part162 : Audit := .cycle 11 1 false (-1)
theorem kid04_part162_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part162) = true := by rfl

def kid04_part163 : Audit := .cycle 0 27 true (0)
theorem kid04_part163_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part163) = true := by rfl

def kid04_part164 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 21 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 11 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 24 1 false (2),
.cycle 1 14 true (0),
.cycle 9 4 true (0)
])
theorem kid04_part164_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part164) = true := by rfl

def kid04_part165 : Audit := .split 11 (2,true) (byMove [
.cycle 21 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 34 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 4 true (0),
.cycle 12 12 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 13 15 true (0),
.cycle 2 12 true (0),
.cycle 9 3 true (0)
])
theorem kid04_part165_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part165) = true := by rfl

def kid04_part166 : Audit := .cycle 0 12 true (0)
theorem kid04_part166_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part166) = true := by rfl

def kid04_part167 : Audit := .split 11 (4,true) (byMove [
.cycle 21 1 false (1),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.cycle 12 2 true (0),
.cycle 0 12 true (0),
.cycle 25 2 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 4 true (0),
.cycle 16 2 true (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 22 1 false (2),
.cycle 14 1 false (-2),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 13 15 true (0),
.cycle 12 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part167_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part167) = true := by rfl

def kid04_part168 : Audit := .cycle 9 3 true (0)
theorem kid04_part168_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part168) = true := by rfl

def kid04_part144 : Audit := .split 10 (5,true) (byMove [(kid04_part145),(kid04_part146),(kid04_part147),(kid04_part148),(kid04_part149),(kid04_part150),(kid04_part151),(kid04_part152),(kid04_part153),(kid04_part154),(kid04_part155),(kid04_part156),(kid04_part157),(kid04_part158),(kid04_part159),(kid04_part160),(kid04_part161),(kid04_part162),(kid04_part163),(kid04_part164),(kid04_part165),(kid04_part166),(kid04_part167),(kid04_part168)])

theorem kid04_part144_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part144) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part145),(kid04_part146),(kid04_part147),(kid04_part148),(kid04_part149),(kid04_part150),(kid04_part151),(kid04_part152),(kid04_part153),(kid04_part154),(kid04_part155),(kid04_part156),(kid04_part157),(kid04_part158),(kid04_part159),(kid04_part160),(kid04_part161),(kid04_part162),(kid04_part163),(kid04_part164),(kid04_part165),(kid04_part166),(kid04_part167),(kid04_part168)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part145_checked

  · exact kid04_part151_checked

  · exact kid04_part157_checked

  · exact kid04_part163_checked

  · exact kid04_part146_checked

  · exact kid04_part152_checked

  · exact kid04_part158_checked

  · exact kid04_part164_checked

  · exact kid04_part147_checked

  · exact kid04_part153_checked

  · exact kid04_part159_checked

  · exact kid04_part165_checked

  · exact kid04_part148_checked

  · exact kid04_part154_checked

  · exact kid04_part160_checked

  · exact kid04_part166_checked

  · exact kid04_part149_checked

  · exact kid04_part155_checked

  · exact kid04_part161_checked

  · exact kid04_part167_checked

  · exact kid04_part150_checked

  · exact kid04_part156_checked

  · exact kid04_part162_checked

  · exact kid04_part168_checked

def kid04_part169 : Audit := .cycle 0 10 true (0)
theorem kid04_part169_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part169) = true := by rfl

def kid04_part170 : Audit := .cycle 1 9 true (1)
theorem kid04_part170_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part170) = true := by rfl

def kid04_part171 : Audit := .cycle 2 8 true (1)
theorem kid04_part171_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part171) = true := by rfl

def kid04_part172 : Audit := .cycle 1 12 true (1)
theorem kid04_part172_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part172) = true := by rfl

def kid04_part174 : Audit := .cycle 0 24 true (0)
theorem kid04_part174_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part174) = true := by rfl

def kid04_part175 : Audit := .cycle 12 11 false (0)
theorem kid04_part175_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part175) = true := by rfl

def kid04_part176 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.last 15 (4,true),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 28 1 false (2),
.cycle 16 1 false (0),
.cycle 9 4 true (0)
])
theorem kid04_part176_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part176) = true := by rfl

def kid04_part177 : Audit := .cycle 0 13 true (0)
theorem kid04_part177_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part177) = true := by rfl

def kid04_part178 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 13 true (0),
.cycle 20 4 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 13 4 false (2),
.cycle 12 3 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 15 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 4 false (1),
.cycle 23 4 false (3),
.cycle 13 4 false (1),
.cycle 9 4 true (0)
])
theorem kid04_part178_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part178) = true := by rfl

def kid04_part179 : Audit := .cycle 12 3 false (0)
theorem kid04_part179_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part179) = true := by rfl

def kid04_part180 : Audit := .cycle 0 12 true (0)
theorem kid04_part180_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part180) = true := by rfl

def kid04_part181 : Audit := .cycle 1 11 true (1)
theorem kid04_part181_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part181) = true := by rfl

def kid04_part182 : Audit := .cycle 24 1 false (2)
theorem kid04_part182_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part182) = true := by rfl

def kid04_part183 : Audit := .cycle 21 1 false (1)
theorem kid04_part183_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part183) = true := by rfl

def kid04_part184 : Audit := .cycle 8 4 true (1)
theorem kid04_part184_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part184) = true := by rfl

def kid04_part185 : Audit := .cycle 9 3 true (1)
theorem kid04_part185_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part185) = true := by rfl

def kid04_part186 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 false (3),
.cycle 12 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.cycle 15 6 false (0),
.cycle 0 21 false (3),
.cycle 12 14 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 14 7 false (0),
.cycle 15 6 true (-2),
.cycle 18 3 false (-1),
.last 22 (2,true),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.cycle 17 6 false (-1),
.cycle 16 19 false (2),
.cycle 1 20 false (3),
.cycle 12 13 false (1),
.cycle 12 17 true (-2),
.cycle 16 5 false (0),
.cycle 9 12 false (2)
])
theorem kid04_part186_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part186) = true := by rfl

def kid04_part187 : Audit := .split 18 (2,true) (byMove [
.cycle 12 14 true (-3),
.cycle 12 7 false (0),
.cycle 21 1 false (-3),
.last 42 (4,true),
.last 19 (4,true),
.cycle 16 3 false (-2),
.proven (BB6.Agent11Raw39B0RBPumps.M21.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M21.never m hm),
.cycle 48 13 true (2),
.cycle 12 13 false (0),
.cycle 12 11 false (0),
.cycle 8 11 false (2),
.last 25 (4,true),
.cycle 12 8 false (0),
.cycle 12 7 false (0),
.cycle 63 17 true (-1),
.cycle 54 15 true (2),
.last 19 (4,true),
.cycle 16 3 false (-2),
.last 35 (4,true),
.last 40 (4,true),
.cycle 2 17 false (3),
.cycle 22 16 true (0),
.cycle 10 9 false (2),
.last 23 (4,true)
])
theorem kid04_part187_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part187) = true := by rfl

def kid04_part188 : Audit := .split 12 (2,true) (byMove [
.cycle 0 30 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 22 (4,true),
.last 20 (4,true),
.cycle 0 27 true (0),
.cycle 0 20 true (-2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 26 (4,true),
.cycle 0 29 true (-1),
.cycle 13 1 false (-1),
.last 21 (4,true),
.last 14 (4,true),
.cycle 0 27 true (0),
.last 14 (4,true),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (0)
])
theorem kid04_part188_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part188) = true := by rfl

def kid04_part189 : Audit := .cycle 25 1 false (1)
theorem kid04_part189_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part189) = true := by rfl

def kid04_part190 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 21 4 false (3),
.cycle 14 4 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 4 false (2),
.cycle 13 4 false (1),
.cycle 12 3 false (0),
.last 14 (2,true),
.cycle 23 4 false (3),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 15 4 false (-1),
.cycle 25 4 false (1),
.cycle 1 14 true (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 4 true (0),
.cycle 11 2 true (0)
])
theorem kid04_part190_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part190) = true := by rfl

def kid04_part191 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 12 7 false (0),
.last 15 (2,true),
.cycle 19 1 false (-1),
.cycle 12 7 false (0),
.cycle 12 3 false (0),
.cycle 0 29 true (-1),
.cycle 16 13 true (-2),
.last 15 (2,true),
.cycle 0 16 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 0, 16, 64],[2, 0, 64, 1, 16, 16, 64],64⟩,
.cycle 15 5 true (0),
.cycle 12 8 false (0),
.cycle 12 7 false (0),
.last 15 (2,true),
.cycle 15 15 true (-2),
.cycle 12 7 false (0),
.cycle 12 3 false (0),
.last 107 (2,true),
.last 35 (2,true),
.last 15 (2,true),
.cycle 0 16 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 0, 16, 64],[2, 0, 64, 1, 16, 16, 64],64⟩,
.cycle 11 5 false (1)
])
theorem kid04_part191_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part191) = true := by rfl

def kid04_part192 : Audit := .cycle 0 12 true (0)
theorem kid04_part192_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part192) = true := by rfl

def kid04_part193 : Audit := .cycle 1 11 true (1)
theorem kid04_part193_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part193) = true := by rfl

def kid04_part194 : Audit := .cycle 2 10 true (1)
theorem kid04_part194_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part194) = true := by rfl

def kid04_part195 : Audit := .cycle 1 14 true (1)
theorem kid04_part195_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part195) = true := by rfl

def kid04_part196 : Audit := .cycle 10 2 true (1)
theorem kid04_part196_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part196) = true := by rfl

def kid04_part197 : Audit := .cycle 9 3 true (1)
theorem kid04_part197_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part197) = true := by rfl

def kid04_part173 : Audit := .split 11 (5,true) (byMove [(kid04_part174),(kid04_part175),(kid04_part176),(kid04_part177),(kid04_part178),(kid04_part179),(kid04_part180),(kid04_part181),(kid04_part182),(kid04_part183),(kid04_part184),(kid04_part185),(kid04_part186),(kid04_part187),(kid04_part188),(kid04_part189),(kid04_part190),(kid04_part191),(kid04_part192),(kid04_part193),(kid04_part194),(kid04_part195),(kid04_part196),(kid04_part197)])

theorem kid04_part173_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part173) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some mv)) (byMove [(kid04_part174),(kid04_part175),(kid04_part176),(kid04_part177),(kid04_part178),(kid04_part179),(kid04_part180),(kid04_part181),(kid04_part182),(kid04_part183),(kid04_part184),(kid04_part185),(kid04_part186),(kid04_part187),(kid04_part188),(kid04_part189),(kid04_part190),(kid04_part191),(kid04_part192),(kid04_part193),(kid04_part194),(kid04_part195),(kid04_part196),(kid04_part197)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part174_checked

  · exact kid04_part180_checked

  · exact kid04_part186_checked

  · exact kid04_part192_checked

  · exact kid04_part175_checked

  · exact kid04_part181_checked

  · exact kid04_part187_checked

  · exact kid04_part193_checked

  · exact kid04_part176_checked

  · exact kid04_part182_checked

  · exact kid04_part188_checked

  · exact kid04_part194_checked

  · exact kid04_part177_checked

  · exact kid04_part183_checked

  · exact kid04_part189_checked

  · exact kid04_part195_checked

  · exact kid04_part178_checked

  · exact kid04_part184_checked

  · exact kid04_part190_checked

  · exact kid04_part196_checked

  · exact kid04_part179_checked

  · exact kid04_part185_checked

  · exact kid04_part191_checked

  · exact kid04_part197_checked

def kid04_part198 : Audit := .cycle 9 1 true (1)
theorem kid04_part198_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part198) = true := by rfl

def kid04_part54 : Audit := .split 9 (5,false) (byMove [(kid04_part55),(kid04_part56),(kid04_part57),(kid04_part58),(kid04_part59),(kid04_part60),(kid04_part61),(kid04_part62),(kid04_part63),(kid04_part64),(kid04_part65),(kid04_part66),(kid04_part67),(kid04_part68),(kid04_part93),(kid04_part118),(kid04_part119),(kid04_part144),(kid04_part169),(kid04_part170),(kid04_part171),(kid04_part172),(kid04_part173),(kid04_part198)])

theorem kid04_part54_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (kid04_part54) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part55),(kid04_part56),(kid04_part57),(kid04_part58),(kid04_part59),(kid04_part60),(kid04_part61),(kid04_part62),(kid04_part63),(kid04_part64),(kid04_part65),(kid04_part66),(kid04_part67),(kid04_part68),(kid04_part93),(kid04_part118),(kid04_part119),(kid04_part144),(kid04_part169),(kid04_part170),(kid04_part171),(kid04_part172),(kid04_part173),(kid04_part198)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part55_checked

  · exact kid04_part61_checked

  · exact kid04_part67_checked

  · exact kid04_part169_checked

  · exact kid04_part56_checked

  · exact kid04_part62_checked

  · exact kid04_part68_checked

  · exact kid04_part170_checked

  · exact kid04_part57_checked

  · exact kid04_part63_checked

  · exact kid04_part93_checked

  · exact kid04_part171_checked

  · exact kid04_part58_checked

  · exact kid04_part64_checked

  · exact kid04_part118_checked

  · exact kid04_part172_checked

  · exact kid04_part59_checked

  · exact kid04_part65_checked

  · exact kid04_part119_checked

  · exact kid04_part173_checked

  · exact kid04_part60_checked

  · exact kid04_part66_checked

  · exact kid04_part144_checked

  · exact kid04_part198_checked

def kid04_part199 : Audit := .cycle 0 9 true (0)
theorem kid04_part199_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,0⟩)) (kid04_part199) = true := by rfl

def kid04_part200 : Audit := .cycle 1 8 true (1)
theorem kid04_part200_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,1⟩)) (kid04_part200) = true := by rfl

def kid04_part201 : Audit := .cycle 30 1 false (8)
theorem kid04_part201_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,2⟩)) (kid04_part201) = true := by rfl

def kid04_part202 : Audit := .cycle 16 1 false (2)
theorem kid04_part202_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,3⟩)) (kid04_part202) = true := by rfl

def kid04_part203 : Audit := .cycle 8 1 true (2)
theorem kid04_part203_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,4⟩)) (kid04_part203) = true := by rfl

def kid04_part205 : Audit := .cycle 0 10 true (0)
theorem kid04_part205_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part205) = true := by rfl

def kid04_part206 : Audit := .cycle 1 9 true (1)
theorem kid04_part206_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part206) = true := by rfl

def kid04_part207 : Audit := .cycle 20 1 false (2)
theorem kid04_part207_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part207) = true := by rfl

def kid04_part208 : Audit := .cycle 17 1 false (1)
theorem kid04_part208_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part208) = true := by rfl

def kid04_part209 : Audit := .cycle 8 2 true (2)
theorem kid04_part209_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part209) = true := by rfl

def kid04_part210 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 21 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 16 true (-1),
.cycle 24 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 13 3 false (0),
.last 17 (2,true),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 12 5 false (0),
.cycle 16 1 false (-2),
.cycle 32 1 false (0),
.cycle 1 15 false (3),
.cycle 23 1 false (1),
.cycle 27 1 false (3),
.cycle 10 7 false (2),
.cycle 11 5 false (1)
]),
.split 14 (2,true) (byMove [
.cycle 24 1 false (2),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 9 15 false (3),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 8 7 false (3),
.cycle 10 5 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 27 1 false (3),
.cycle 25 1 false (3),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 29 (4,true),
.cycle 29 1 false (-1),
.cycle 2 13 false (3),
.cycle 9 19 false (4),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 10 4 true (0),
.cycle 11 2 true (0)
])
theorem kid04_part210_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part210) = true := by rfl

def kid04_part211 : Audit := .cycle 0 10 true (0)
theorem kid04_part211_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part211) = true := by rfl

def kid04_part212 : Audit := .cycle 1 9 true (1)
theorem kid04_part212_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part212) = true := by rfl

def kid04_part214 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 260, 32, 4, 128, 256, 8, 2, 32, 4, 4096],[2, 4, 256, 1, 4096, 4096, 2, 4096, 256, 1, 4096, 4096, 4096],4096⟩
theorem kid04_part214_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part214) = true := by rfl

def kid04_part215 : Audit := .cycle 0 61 true (0)
theorem kid04_part215_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part215) = true := by rfl

def kid04_part216 : Audit := .cycle 23 1 false (3)
theorem kid04_part216_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part216) = true := by rfl

def kid04_part217 : Audit := .cycle 22 1 false (2)
theorem kid04_part217_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part217) = true := by rfl

def kid04_part218 : Audit := .cycle 31 1 false (7)
theorem kid04_part218_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part218) = true := by rfl

def kid04_part219 : Audit := .cycle 36 1 false (10)
theorem kid04_part219_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part219) = true := by rfl

def kid04_part220 : Audit := .cycle 27 1 false (7)
theorem kid04_part220_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part220) = true := by rfl

def kid04_part221 : Audit := .cycle 36 1 false (10)
theorem kid04_part221_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part221) = true := by rfl

def kid04_part222 : Audit := .cycle 25 1 false (7)
theorem kid04_part222_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part222) = true := by rfl

def kid04_part223 : Audit := .cycle 34 1 false (10)
theorem kid04_part223_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part223) = true := by rfl

def kid04_part224 : Audit := .split 22 (4,true) (byMove [
.cycle 8 18 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 29 1 false (9),
.cycle 0 26 true (0),
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 27 1 false (9),
.cycle 0 24 true (0),
.cycle 27 1 false (9),
.last 23 (5,true),
.cycle 22 3 false (4),
.cycle 8 20 true (0),
.cycle 36 1 false (10),
.cycle 23 1 false (3),
.last 24 (5,true),
.cycle 31 1 false (9),
.cycle 0 63 true (0),
.cycle 1 24 true (0),
.cycle 8 16 true (0),
.cycle 0 24 true (0),
.cycle 23 14 true (5),
.last 23 (5,true)
])
theorem kid04_part224_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part224) = true := by rfl

def kid04_part225 : Audit := .split 22 (5,true) (byMove [
.cycle 0 39 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 28 1 false (8),
.cycle 0 26 true (0),
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (8),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 26 1 false (8),
.last 25 (4,true),
.cycle 24 15 true (4),
.cycle 36 1 false (10),
.cycle 23 1 false (3),
.cycle 22 2 true (3),
.cycle 30 1 false (8),
.cycle 0 63 true (0),
.last 24 (4,true),
.cycle 46 1 false (12),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 22 30 true (4)
])
theorem kid04_part225_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part225) = true := by rfl

def kid04_part226 : Audit := .split 24 (4,true) (byMove [
.cycle 0 73 true (0),
.cycle 61 1 false (7),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 40 1 false (10),
.cycle 27 1 false (3),
.cycle 0 31 true (0),
.cycle 45 1 false (9),
.cycle 38 1 false (10),
.cycle 25 1 false (3),
.last 26 (5,true),
.cycle 37 1 false (7),
.cycle 22 3 false (3),
.cycle 44 1 false (10),
.cycle 0 37 true (0),
.cycle 25 1 false (1),
.last 26 (5,true),
.cycle 20 5 false (3),
.cycle 0 31 true (0),
.cycle 1 34 true (0),
.cycle 0 67 true (0),
.cycle 48 1 false (10),
.last 26 (5,true),
.cycle 30 14 true (4)
])
theorem kid04_part226_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part226) = true := by rfl

def kid04_part227 : Audit := .cycle 18 6 true (1)
theorem kid04_part227_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part227) = true := by rfl

def kid04_part228 : Audit := .cycle 29 1 false (7)
theorem kid04_part228_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part228) = true := by rfl

def kid04_part229 : Audit := .cycle 22 1 false (2)
theorem kid04_part229_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part229) = true := by rfl

def kid04_part230 : Audit := .split 23 (5,true) (byMove [
.last 27 (4,true),
.cycle 0 67 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 37 1 false (7),
.cycle 38 1 false (10),
.cycle 29 1 false (7),
.cycle 40 1 false (10),
.cycle 31 1 false (7),
.cycle 36 1 false (10),
.last 24 (4,true),
.cycle 28 1 false (8),
.last 26 (4,true),
.last 26 (4,true),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 22 2 true (2),
.cycle 20 4 true (2),
.cycle 0 73 true (0),
.last 25 (4,true),
.last 25 (4,true),
.cycle 5 93 true (0),
.last 24 (4,true),
.cycle 25 13 true (5)
])
theorem kid04_part230_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part230) = true := by rfl

def kid04_part231 : Audit := .cycle 20 2 true (2)
theorem kid04_part231_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part231) = true := by rfl

def kid04_part232 : Audit := .cycle 0 65 true (0)
theorem kid04_part232_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part232) = true := by rfl

def kid04_part233 : Audit := .split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 33 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 27 true (0),
.cycle 1 25 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 25 (5,true),
.cycle 1 25 true (0),
.cycle 22 3 false (4),
.cycle 1 27 true (0),
.cycle 0 31 true (0),
.cycle 24 1 false (2),
.last 25 (5,true),
.cycle 1 27 true (0),
.cycle 0 27 true (0),
.cycle 1 25 true (0),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.last 25 (5,true),
.cycle 1 25 true (0)
])
theorem kid04_part233_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part233) = true := by rfl

def kid04_part234 : Audit := .cycle 2 22 true (0)
theorem kid04_part234_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part234) = true := by rfl

def kid04_part235 : Audit := .cycle 5 83 true (0)
theorem kid04_part235_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part235) = true := by rfl

def kid04_part236 : Audit := .split 22 (4,true) (byMove [
.cycle 21 52 true (3),
.cycle 0 28 true (0),
.last 25 (5,true),
.cycle 27 1 false (3),
.cycle 0 28 true (0),
.last 23 (5,true),
.cycle 0 67 true (0),
.cycle 24 41 true (3),
.cycle 23 24 true (5),
.cycle 0 24 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1044, 32, 4, 128, 256, 8, 2, 32, 4, 4096],[2, 4, 1024, 1, 16, 4096, 2, 32, 1024, 1, 16, 4096, 4096],4096⟩,
.last 23 (5,true),
.cycle 47 1 false (11),
.cycle 23 18 true (2),
.cycle 21 2 true (3),
.cycle 29 1 false (7),
.last 25 (5,true),
.last 23 (5,true),
.cycle 0 63 true (0),
.cycle 1 24 true (0),
.cycle 2 36 true (0),
.cycle 0 24 true (0),
.cycle 23 14 true (5),
.last 23 (5,true)
])
theorem kid04_part236_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part236) = true := by rfl

def kid04_part237 : Audit := .split 22 (5,true) (byMove [
.cycle 25 11 true (5),
.cycle 0 28 true (0),
.cycle 24 11 true (4),
.last 26 (4,true),
.last 23 (4,true),
.cycle 26 1 false (4),
.cycle 48 11 true (8),
.cycle 61 11 true (10),
.cycle 23 11 true (5),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 9 15 true (0),
.cycle 23 11 true (3),
.cycle 28 11 true (3),
.cycle 21 2 true (3),
.cycle 29 1 false (7),
.last 23 (4,true),
.cycle 20 4 true (2),
.cycle 0 63 true (0),
.last 24 (4,true),
.cycle 23 11 true (5),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 24 11 true (5)
])
theorem kid04_part237_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part237) = true := by rfl

def kid04_part213 : Audit := .split 21 (2,true) (byMove [(kid04_part214),(kid04_part215),(kid04_part216),(kid04_part217),(kid04_part218),(kid04_part219),(kid04_part220),(kid04_part221),(kid04_part222),(kid04_part223),(kid04_part224),(kid04_part225),(kid04_part226),(kid04_part227),(kid04_part228),(kid04_part229),(kid04_part230),(kid04_part231),(kid04_part232),(kid04_part233),(kid04_part234),(kid04_part235),(kid04_part236),(kid04_part237)])

theorem kid04_part213_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part213) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) 21 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid04_part214),(kid04_part215),(kid04_part216),(kid04_part217),(kid04_part218),(kid04_part219),(kid04_part220),(kid04_part221),(kid04_part222),(kid04_part223),(kid04_part224),(kid04_part225),(kid04_part226),(kid04_part227),(kid04_part228),(kid04_part229),(kid04_part230),(kid04_part231),(kid04_part232),(kid04_part233),(kid04_part234),(kid04_part235),(kid04_part236),(kid04_part237)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part214_checked

  · exact kid04_part220_checked

  · exact kid04_part226_checked

  · exact kid04_part232_checked

  · exact kid04_part215_checked

  · exact kid04_part221_checked

  · exact kid04_part227_checked

  · exact kid04_part233_checked

  · exact kid04_part216_checked

  · exact kid04_part222_checked

  · exact kid04_part228_checked

  · exact kid04_part234_checked

  · exact kid04_part217_checked

  · exact kid04_part223_checked

  · exact kid04_part229_checked

  · exact kid04_part235_checked

  · exact kid04_part218_checked

  · exact kid04_part224_checked

  · exact kid04_part230_checked

  · exact kid04_part236_checked

  · exact kid04_part219_checked

  · exact kid04_part225_checked

  · exact kid04_part231_checked

  · exact kid04_part237_checked

def kid04_part238 : Audit := .cycle 30 1 false (8)
theorem kid04_part238_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part238) = true := by rfl

def kid04_part239 : Audit := .cycle 8 2 true (2)
theorem kid04_part239_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part239) = true := by rfl

def kid04_part240 : Audit := .cycle 9 1 true (3)
theorem kid04_part240_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part240) = true := by rfl

def kid04_part241 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 5 false (0),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 15 8 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 21 3 false (-1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 19 12 false (1),
.cycle 22 9 false (0),
.cycle 15 8 false (1),
.cycle 18 18 true (-1),
.cycle 1 16 true (1),
.cycle 21 3 false (-1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 31 (5,true),
.cycle 23 16 false (1)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 32 1 false (2),
.cycle 20 7 false (0),
.cycle 19 6 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 48 1 false (8),
.cycle 28 1 false (2),
.cycle 8 7 true (1),
.cycle 9 6 true (1),
.cycle 18 5 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 13 2 true (1),
.cycle 19 6 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 19 4 true (1),
.cycle 6 10 true (1)
]),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 6 8 true (2)
])
theorem kid04_part241_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part241) = true := by rfl

def kid04_part243 : Audit := .cycle 1 12 true (1)
theorem kid04_part243_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part243) = true := by rfl

def kid04_part244 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 false (3),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (0),
.cycle 19 5 false (-1),
.cycle 0 19 true (0),
.cycle 25 5 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 5 false (2),
.cycle 19 5 false (1),
.cycle 17 3 false (1),
.cycle 19 5 false (0),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.last 20 (5,true),
.cycle 19 5 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 24 5 false (2),
.cycle 28 5 false (4),
.cycle 13 6 true (0),
.cycle 20 5 false (0)
])
theorem kid04_part244_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part244) = true := by rfl

def kid04_part245 : Audit := .cycle 25 1 false (1)
theorem kid04_part245_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part245) = true := by rfl

def kid04_part246 : Audit := .cycle 0 13 true (0)
theorem kid04_part246_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part246) = true := by rfl

def kid04_part247 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 5 false (0),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 9 4 true (2),
.cycle 22 3 false (0),
.cycle 19 3 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 22 7 false (1)
])
theorem kid04_part247_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part247) = true := by rfl

def kid04_part248 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 18 (4,true),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 9 4 true (2),
.last 15 (4,true),
.cycle 19 3 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.last 22 (4,true)
])
theorem kid04_part248_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part248) = true := by rfl

def kid04_part249 : Audit := .cycle 0 12 true (0)
theorem kid04_part249_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part249) = true := by rfl

def kid04_part250 : Audit := .cycle 1 11 true (1)
theorem kid04_part250_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part250) = true := by rfl

def kid04_part251 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 32, 4, 128, 256, 8, 2, 32, 4100, 4096],[2, 4, 4, 1, 4096, 4096, 2, 4096, 4, 1, 4096, 4096, 4096],6144⟩
theorem kid04_part251_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part251) = true := by rfl

def kid04_part252 : Audit := .cycle 3 9 true (1)
theorem kid04_part252_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part252) = true := by rfl

def kid04_part253 : Audit := .cycle 8 4 true (2)
theorem kid04_part253_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part253) = true := by rfl

def kid04_part254 : Audit := .cycle 9 3 true (2)
theorem kid04_part254_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part254) = true := by rfl

def kid04_part255 : Audit := .cycle 6 6 true (2)
theorem kid04_part255_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part255) = true := by rfl

def kid04_part256 : Audit := .split 18 (4,true) (byMove [
.cycle 40 44 true (-1),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (0),
.cycle 19 5 false (-1),
.cycle 0 25 true (0),
.cycle 19 5 false (2),
.cycle 28 5 false (6),
.cycle 19 1 false (1),
.last 20 (5,true),
.cycle 19 5 false (1),
.cycle 17 3 false (1),
.cycle 19 5 false (0),
.cycle 0 31 true (-1),
.cycle 19 1 false (-1),
.last 20 (5,true),
.cycle 19 5 false (-1),
.cycle 0 25 true (0),
.cycle 15 4 true (0),
.cycle 38 20 true (0),
.cycle 22 5 false (2),
.last 20 (5,true),
.cycle 20 5 false (0)
])
theorem kid04_part256_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part256) = true := by rfl

def kid04_part257 : Audit := .cycle 1 15 true (1)
theorem kid04_part257_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part257) = true := by rfl

def kid04_part258 : Audit := .cycle 1 13 true (1)
theorem kid04_part258_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part258) = true := by rfl

def kid04_part259 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 19 1 false (1),
.cycle 18 5 false (0),
.cycle 16 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.last 13 (5,true),
.cycle 22 3 false (0),
.cycle 19 3 false (0),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 16 4 false (0),
.cycle 1 13 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.last 13 (5,true)
])
theorem kid04_part259_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part259) = true := by rfl

def kid04_part260 : Audit := .split 12 (5,true) (byMove [
.cycle 10 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 19 1 false (1),
.last 18 (4,true),
.cycle 16 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 22 5 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 5 true (2),
.last 15 (4,true),
.cycle 19 3 false (0),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 16 4 false (0),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid04_part260_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part260) = true := by rfl

def kid04_part261 : Audit := .cycle 0 12 true (0)
theorem kid04_part261_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part261) = true := by rfl

def kid04_part262 : Audit := .cycle 1 11 true (1)
theorem kid04_part262_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part262) = true := by rfl

def kid04_part263 : Audit := .cycle 2 10 true (1)
theorem kid04_part263_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part263) = true := by rfl

def kid04_part264 : Audit := .cycle 1 14 true (1)
theorem kid04_part264_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part264) = true := by rfl

def kid04_part265 : Audit := .cycle 8 4 true (2)
theorem kid04_part265_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part265) = true := by rfl

def kid04_part266 : Audit := .split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.last 26 (5,true),
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.cycle 22 7 false (1),
.last 21 (5,true),
.cycle 0 18 true (0),
.cycle 10 5 true (2),
.cycle 0 17 true (0),
.last 25 (5,true),
.last 16 (5,true),
.last 18 (5,true),
.cycle 25 3 false (1),
.last 25 (5,true),
.cycle 0 22 true (0),
.cycle 26 1 false (0),
.last 16 (5,true),
.last 21 (5,true),
.cycle 0 18 true (0),
.cycle 10 5 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.last 21 (5,true)
])
theorem kid04_part266_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part266) = true := by rfl

def kid04_part242 : Audit := .split 11 (2,true) (byMove [(kid04_part243),(kid04_part244),(kid04_part245),(kid04_part246),(kid04_part247),(kid04_part248),(kid04_part249),(kid04_part250),(kid04_part251),(kid04_part252),(kid04_part253),(kid04_part254),(kid04_part255),(kid04_part256),(kid04_part257),(kid04_part258),(kid04_part259),(kid04_part260),(kid04_part261),(kid04_part262),(kid04_part263),(kid04_part264),(kid04_part265),(kid04_part266)])

theorem kid04_part242_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part242) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid04_part243),(kid04_part244),(kid04_part245),(kid04_part246),(kid04_part247),(kid04_part248),(kid04_part249),(kid04_part250),(kid04_part251),(kid04_part252),(kid04_part253),(kid04_part254),(kid04_part255),(kid04_part256),(kid04_part257),(kid04_part258),(kid04_part259),(kid04_part260),(kid04_part261),(kid04_part262),(kid04_part263),(kid04_part264),(kid04_part265),(kid04_part266)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part243_checked

  · exact kid04_part249_checked

  · exact kid04_part255_checked

  · exact kid04_part261_checked

  · exact kid04_part244_checked

  · exact kid04_part250_checked

  · exact kid04_part256_checked

  · exact kid04_part262_checked

  · exact kid04_part245_checked

  · exact kid04_part251_checked

  · exact kid04_part257_checked

  · exact kid04_part263_checked

  · exact kid04_part246_checked

  · exact kid04_part252_checked

  · exact kid04_part258_checked

  · exact kid04_part264_checked

  · exact kid04_part247_checked

  · exact kid04_part253_checked

  · exact kid04_part259_checked

  · exact kid04_part265_checked

  · exact kid04_part248_checked

  · exact kid04_part254_checked

  · exact kid04_part260_checked

  · exact kid04_part266_checked

def kid04_part267 : Audit := .cycle 0 12 true (0)
theorem kid04_part267_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part267) = true := by rfl

def kid04_part268 : Audit := .cycle 17 1 false (1)
theorem kid04_part268_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part268) = true := by rfl

def kid04_part269 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.cycle 26 3 false (4),
.cycle 19 3 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 19 3 false (3),
.cycle 17 3 false (1),
.cycle 16 3 false (0),
.last 18 (2,true),
.cycle 28 3 false (4),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 17 3 false (-1),
.cycle 9 20 true (0),
.cycle 1 18 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 12 7 true (0),
.cycle 18 3 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 25 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 260, 32, 4, 128, 256, 8, 2, 32, 4096, 4096],[2, 4, 256, 1, 4096, 4, 2, 4096, 256, 1, 4096, 4, 4096],6144⟩,
.cycle 0 71 true (0),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 41 1 false (7),
.cycle 44 1 false (10),
.cycle 33 1 false (7),
.cycle 44 1 false (10),
.cycle 29 1 false (7),
.cycle 40 1 false (10),
.last 26 (4,true),
.cycle 32 1 false (8),
.last 28 (4,true),
.cycle 20 8 true (1),
.cycle 35 1 false (7),
.cycle 26 1 false (2),
.cycle 35 1 false (7),
.cycle 22 4 true (1),
.cycle 0 79 true (0),
.last 27 (4,true),
.cycle 2 26 true (0),
.cycle 5 99 true (0),
.last 26 (4,true),
.last 29 (4,true)
]),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.cycle 9 3 true (2),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 32 1 false (2),
.cycle 22 7 false (0),
.cycle 16 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 48 1 false (8),
.cycle 28 1 false (2),
.cycle 8 7 true (2),
.cycle 9 6 true (2),
.cycle 24 3 false (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 20 5 false (0),
.cycle 16 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (2),
.cycle 6 12 true (2)
]),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 22 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 32, 4, 128, 256, 8, 2, 32, 4096, 4096],[2, 4, 4, 1, 4096, 4, 2, 4096, 4, 1, 4096, 4100, 4096],6144⟩,
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 9 5 true (2),
.cycle 6 8 true (2),
.last 22 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 22 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (2),
.last 15 (4,true)
]),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 9 17 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.cycle 20 3 false (2),
.cycle 19 3 false (1),
.last 17 (2,true),
.cycle 21 3 false (3),
.cycle 21 3 false (5),
.cycle 17 3 false (1),
.cycle 16 3 false (0),
.last 18 (2,true),
.cycle 22 3 false (2),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 17 3 false (-1),
.cycle 12 8 true (0),
.last 20 (2,true),
.last 17 (2,true),
.cycle 5 12 true (0),
.cycle 17 8 true (1),
.cycle 18 3 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.last 29 (2,true),
.cycle 25 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 19 5 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (2),
.cycle 11 3 true (3),
.cycle 27 3 false (1),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 5 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 16 5 true (2),
.cycle 1 14 true (1),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (2),
.cycle 11 3 true (3)
])
])
theorem kid04_part269_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part269) = true := by rfl

def kid04_part271 : Audit := .split 15 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 256, 32, 256, 128, 256, 8, 2, 32, 256, 4096],[2, 256, 256, 1, 4096, 256, 2, 4096, 256, 1, 4096, 256, 4096],4096⟩,
.last 17 (4,true),
.cycle 19 1 false (-1),
.last 19 (4,true),
.last 16 (4,true),
.cycle 32 16 true (-1),
.cycle 6 20 true (-1),
.cycle 10 16 true (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 32, 4, 128, 256, 8, 2, 32, 4, 4096],[2, 4, 4, 1, 4096, 256, 2, 4096, 4, 1, 4096, 256, 4096],4096⟩,
.cycle 28 24 true (-1),
.last 16 (4,true),
.cycle 14 27 true (0),
.cycle 10 9 false (2),
.last 17 (4,true),
.cycle 23 1 false (1),
.cycle 5 11 false (3),
.last 16 (4,true),
.cycle 12 8 true (-1),
.cycle 14 35 true (0),
.last 17 (4,true),
.cycle 14 16 true (0),
.cycle 14 41 true (0),
.last 16 (4,true),
.cycle 16 5 true (1)
])
theorem kid04_part271_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part271) = true := by rfl

def kid04_part272 : Audit := .cycle 9 11 false (3)
theorem kid04_part272_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part272) = true := by rfl

def kid04_part273 : Audit := .cycle 14 1 false (0)
theorem kid04_part273_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part273) = true := by rfl

def kid04_part274 : Audit := .cycle 13 1 false (-1)
theorem kid04_part274_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part274) = true := by rfl

def kid04_part275 : Audit := .cycle 14 1 false (0)
theorem kid04_part275_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part275) = true := by rfl

def kid04_part276 : Audit := .cycle 13 1 false (-1)
theorem kid04_part276_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part276) = true := by rfl

def kid04_part277 : Audit := .cycle 16 1 false (2)
theorem kid04_part277_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part277) = true := by rfl

def kid04_part278 : Audit := .cycle 15 1 false (1)
theorem kid04_part278_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part278) = true := by rfl

def kid04_part279 : Audit := .split 13 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 256, 32, 256, 128, 256, 8, 2, 32, 256, 4096],[2, 256, 256, 1, 4096, 4, 2, 4096, 256, 1, 4096, 4, 4096],4096⟩,
.cycle 28 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 17 1 false (5),
.cycle 24 1 false (6),
.last 14 (4,true),
.cycle 16 1 false (4),
.last 16 (4,true),
.cycle 18 1 false (0),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 23 1 false (5),
.cycle 14 1 false (0),
.cycle 10 29 true (0),
.last 15 (4,true),
.cycle 2 14 true (0),
.cycle 5 35 true (0),
.last 14 (4,true),
.cycle 14 3 true (2)
])
theorem kid04_part279_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part279) = true := by rfl

def kid04_part280 : Audit := .cycle 17 1 false (3)
theorem kid04_part280_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part280) = true := by rfl

def kid04_part281 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 28 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 14 (2,true),
.cycle 24 1 false (6),
.cycle 17 1 false (5),
.cycle 16 1 false (4),
.cycle 13 3 false (1),
.last 15 (2,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 23 1 false (5),
.cycle 14 1 false (0),
.cycle 10 29 true (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 35 true (0),
.cycle 14 6 true (2),
.cycle 14 3 true (2)
])
theorem kid04_part281_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part281) = true := by rfl

def kid04_part282 : Audit := .cycle 16 1 false (4)
theorem kid04_part282_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part282) = true := by rfl

def kid04_part283 : Audit := .split 15 (4,true) (byMove [
.cycle 31 1 false (-1),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 25 true (-1),
.last 17 (2,true),
.cycle 21 1 false (3),
.cycle 16 1 false (0),
.cycle 32 1 false (4),
.cycle 16 1 false (0),
.cycle 13 3 false (0),
.last 17 (2,true),
.cycle 0 33 true (-2),
.cycle 16 1 false (-2),
.cycle 12 5 false (0),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 32, 2, 64],[2, 2, 64, 1, 1, 2, 64],64⟩,
.last 17 (2,true),
.cycle 9 13 false (3),
.cycle 21 1 false (1),
.cycle 44 1 false (0),
.cycle 11 5 false (1)
])
theorem kid04_part283_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part283) = true := by rfl

def kid04_part284 : Audit := .split 14 (2,true) (byMove [
.cycle 33 1 false (5),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 6 9 false (3),
.cycle 10 7 false (2),
.cycle 29 1 false (1),
.cycle 9 11 false (3),
.last 15 (4,true),
.last 28 (4,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 23 1 false (-1),
.last 16 (4,true),
.last 30 (4,true),
.cycle 25 1 false (-1),
.last 15 (4,true),
.last 17 (4,true)
])
theorem kid04_part284_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part284) = true := by rfl

def kid04_part285 : Audit := .cycle 18 1 false (2)
theorem kid04_part285_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part285) = true := by rfl

def kid04_part286 : Audit := .cycle 13 1 false (-1)
theorem kid04_part286_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part286) = true := by rfl

def kid04_part287 : Audit := .cycle 12 2 true (-1)
theorem kid04_part287_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part287) = true := by rfl

def kid04_part288 : Audit := .cycle 13 1 false (-1)
theorem kid04_part288_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part288) = true := by rfl

def kid04_part289 : Audit := .cycle 10 6 true (0)
theorem kid04_part289_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part289) = true := by rfl

def kid04_part290 : Audit := .split 14 (4,true) (byMove [
.cycle 30 28 true (-1),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 21 true (0),
.last 16 (2,true),
.cycle 26 1 false (6),
.cycle 15 1 false (1),
.cycle 20 1 false (4),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 15 1 false (-1),
.cycle 0 21 true (0),
.last 16 (2,true),
.cycle 28 12 true (0),
.cycle 20 1 false (2),
.cycle 1 26 true (0),
.cycle 11 4 true (0)
])
theorem kid04_part290_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part290) = true := by rfl

def kid04_part291 : Audit := .split 13 (2,true) (byMove [
.cycle 29 1 false (5),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.last 17 (4,true),
.last 14 (4,true),
.cycle 28 12 true (0),
.cycle 6 8 true (0),
.cycle 10 6 true (0),
.cycle 26 1 false (2),
.cycle 26 10 true (0),
.last 14 (4,true),
.cycle 18 16 true (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 10 29 true (0),
.last 15 (4,true),
.cycle 2 14 true (0),
.cycle 5 35 true (0),
.last 14 (4,true),
.cycle 14 3 true (2)
])
theorem kid04_part291_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part291) = true := by rfl

def kid04_part292 : Audit := .cycle 5 8 true (0)
theorem kid04_part292_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part292) = true := by rfl

def kid04_part293 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 18 8 true (2),
.cycle 6 8 true (0),
.cycle 10 6 true (0),
.last 14 (2,true),
.cycle 26 10 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 48, 64, 1, 16, 16, 64],64⟩,
.cycle 16 6 true (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 18 1 false (2),
.cycle 12 4 true (-1),
.cycle 12 2 true (0),
.cycle 10 29 true (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 35 true (0),
.cycle 14 6 true (2),
.cycle 14 3 true (2)
])
theorem kid04_part293_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part293) = true := by rfl

def kid04_part294 : Audit := .cycle 14 3 true (2)
theorem kid04_part294_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part294) = true := by rfl

def kid04_part270 : Audit := .split 12 (5,true) (byMove [(kid04_part271),(kid04_part272),(kid04_part273),(kid04_part274),(kid04_part275),(kid04_part276),(kid04_part277),(kid04_part278),(kid04_part279),(kid04_part280),(kid04_part281),(kid04_part282),(kid04_part283),(kid04_part284),(kid04_part285),(kid04_part286),(kid04_part287),(kid04_part288),(kid04_part289),(kid04_part290),(kid04_part291),(kid04_part292),(kid04_part293),(kid04_part294)])

theorem kid04_part270_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part270) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part271),(kid04_part272),(kid04_part273),(kid04_part274),(kid04_part275),(kid04_part276),(kid04_part277),(kid04_part278),(kid04_part279),(kid04_part280),(kid04_part281),(kid04_part282),(kid04_part283),(kid04_part284),(kid04_part285),(kid04_part286),(kid04_part287),(kid04_part288),(kid04_part289),(kid04_part290),(kid04_part291),(kid04_part292),(kid04_part293),(kid04_part294)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part271_checked

  · exact kid04_part277_checked

  · exact kid04_part283_checked

  · exact kid04_part289_checked

  · exact kid04_part272_checked

  · exact kid04_part278_checked

  · exact kid04_part284_checked

  · exact kid04_part290_checked

  · exact kid04_part273_checked

  · exact kid04_part279_checked

  · exact kid04_part285_checked

  · exact kid04_part291_checked

  · exact kid04_part274_checked

  · exact kid04_part280_checked

  · exact kid04_part286_checked

  · exact kid04_part292_checked

  · exact kid04_part275_checked

  · exact kid04_part281_checked

  · exact kid04_part287_checked

  · exact kid04_part293_checked

  · exact kid04_part276_checked

  · exact kid04_part282_checked

  · exact kid04_part288_checked

  · exact kid04_part294_checked

def kid04_part295 : Audit := .cycle 0 10 true (0)
theorem kid04_part295_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part295) = true := by rfl

def kid04_part296 : Audit := .cycle 1 9 true (1)
theorem kid04_part296_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part296) = true := by rfl

def kid04_part297 : Audit := .cycle 2 8 true (1)
theorem kid04_part297_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part297) = true := by rfl

def kid04_part298 : Audit := .cycle 1 12 true (1)
theorem kid04_part298_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part298) = true := by rfl

def kid04_part299 : Audit := .cycle 8 2 true (2)
theorem kid04_part299_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part299) = true := by rfl

def kid04_part300 : Audit := .cycle 9 1 true (3)
theorem kid04_part300_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part300) = true := by rfl

def kid04_part204 : Audit := .split 9 (5,false) (byMove [(kid04_part205),(kid04_part206),(kid04_part207),(kid04_part208),(kid04_part209),(kid04_part210),(kid04_part211),(kid04_part212),(kid04_part213),(kid04_part238),(kid04_part239),(kid04_part240),(kid04_part241),(kid04_part242),(kid04_part267),(kid04_part268),(kid04_part269),(kid04_part270),(kid04_part295),(kid04_part296),(kid04_part297),(kid04_part298),(kid04_part299),(kid04_part300)])

theorem kid04_part204_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (kid04_part204) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part205),(kid04_part206),(kid04_part207),(kid04_part208),(kid04_part209),(kid04_part210),(kid04_part211),(kid04_part212),(kid04_part213),(kid04_part238),(kid04_part239),(kid04_part240),(kid04_part241),(kid04_part242),(kid04_part267),(kid04_part268),(kid04_part269),(kid04_part270),(kid04_part295),(kid04_part296),(kid04_part297),(kid04_part298),(kid04_part299),(kid04_part300)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part205_checked

  · exact kid04_part211_checked

  · exact kid04_part241_checked

  · exact kid04_part295_checked

  · exact kid04_part206_checked

  · exact kid04_part212_checked

  · exact kid04_part242_checked

  · exact kid04_part296_checked

  · exact kid04_part207_checked

  · exact kid04_part213_checked

  · exact kid04_part267_checked

  · exact kid04_part297_checked

  · exact kid04_part208_checked

  · exact kid04_part238_checked

  · exact kid04_part268_checked

  · exact kid04_part298_checked

  · exact kid04_part209_checked

  · exact kid04_part239_checked

  · exact kid04_part269_checked

  · exact kid04_part299_checked

  · exact kid04_part210_checked

  · exact kid04_part240_checked

  · exact kid04_part270_checked

  · exact kid04_part300_checked

def kid04_part302 : Audit := .cycle 0 24 true (0)
theorem kid04_part302_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part302) = true := by rfl

def kid04_part303 : Audit := .cycle 12 11 false (0)
theorem kid04_part303_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part303) = true := by rfl

def kid04_part304 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 1 true (-1),
.cycle 18 1 false (-2),
.last 16 (5,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 1 13 false (3),
.cycle 25 1 false (-1),
.cycle 29 1 false (1),
.cycle 22 1 false (-2),
.cycle 13 1 true (-1)
]),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 18 1 false (0),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 19 1 false (1),
.cycle 13 1 true (1),
.cycle 18 1 false (0),
.cycle 12 3 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 25 1 false (1),
.cycle 29 1 false (3),
.cycle 22 1 false (0),
.cycle 13 1 true (1)
]),
.cycle 17 1 false (-1),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.split 13 (5,false) (byMove [
.last 17 (5,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 27 1 false (1),
.cycle 20 1 false (-2),
.cycle 12 2 true (-1),
.cycle 0 15 true (-1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 18 1 false (-2),
.last 16 (5,true),
.cycle 29 1 false (1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 37 1 false (-1),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 28 1 false (2),
.cycle 21 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 27 1 false (1),
.cycle 20 1 false (-2),
.cycle 12 2 true (0),
.cycle 0 15 true (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 36 1 false (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 8 6 true (0),
.cycle 13 1 true (1),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.last 15 (5,true),
.cycle 28 1 false (2),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 40 1 false (0),
.cycle 25 1 false (-1),
.cycle 13 1 true (1)
])
])
theorem kid04_part304_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part304) = true := by rfl

def kid04_part305 : Audit := .cycle 0 13 true (0)
theorem kid04_part305_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part305) = true := by rfl

def kid04_part306 : Audit := .cycle 12 4 false (0)
theorem kid04_part306_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part306) = true := by rfl

def kid04_part308 : Audit := .cycle 0 13 false (3)
theorem kid04_part308_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part308) = true := by rfl

def kid04_part309 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 false (3),
.cycle 13 12 false (1),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.cycle 20 5 false (0),
.cycle 24 1 false (-2),
.cycle 0 25 false (3),
.cycle 13 12 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 20 5 false (0),
.cycle 24 1 true (-2),
.cycle 21 4 false (0),
.last 26 (2,true),
.cycle 0 27 false (3),
.cycle 25 1 false (-3),
.cycle 20 5 false (0),
.cycle 24 1 false (-2),
.cycle 19 19 false (2),
.cycle 1 24 false (3),
.cycle 14 11 false (1),
.cycle 13 15 true (-2),
.cycle 18 8 false (1),
.cycle 24 1 true (-2)
])
theorem kid04_part309_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part309) = true := by rfl

def kid04_part310 : Audit := .cycle 14 1 false (0)
theorem kid04_part310_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part310) = true := by rfl

def kid04_part311 : Audit := .cycle 13 1 false (-1)
theorem kid04_part311_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part311) = true := by rfl

def kid04_part312 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 13 12 false (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 0 18 false (3),
.cycle 13 12 true (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 17 1 true (-3),
.cycle 14 4 false (-1),
.last 19 (2,true),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 16 15 false (1),
.cycle 1 17 false (3),
.cycle 13 11 false (-1),
.cycle 13 15 true (-3),
.cycle 13 8 false (-1),
.cycle 17 1 true (-3)
])
theorem kid04_part312_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part312) = true := by rfl

def kid04_part313 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 13 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 13 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 5 false (0),
.cycle 13 1 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 12 15 false (3),
.cycle 1 13 false (3),
.cycle 13 11 false (1),
.cycle 13 15 true (-1),
.cycle 13 8 false (0),
.cycle 13 1 true (-1)
])
theorem kid04_part313_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part313) = true := by rfl

def kid04_part314 : Audit := .cycle 0 13 true (0)
theorem kid04_part314_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part314) = true := by rfl

def kid04_part315 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 false (3),
.cycle 13 12 false (3),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 20 5 false (2),
.cycle 24 1 false (0),
.cycle 0 25 true (0),
.cycle 13 12 true (0),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 20 5 false (2),
.cycle 24 1 true (0),
.cycle 21 4 false (2),
.last 26 (2,true),
.cycle 0 27 true (-1),
.cycle 25 1 false (-1),
.cycle 20 5 false (2),
.cycle 24 1 false (0),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 14 11 false (3),
.cycle 13 15 true (0),
.cycle 18 8 false (3),
.cycle 24 1 true (0)
])
theorem kid04_part315_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part315) = true := by rfl

def kid04_part316 : Audit := .cycle 14 1 false (2)
theorem kid04_part316_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part316) = true := by rfl

def kid04_part317 : Audit := .cycle 13 1 false (1)
theorem kid04_part317_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part317) = true := by rfl

def kid04_part318 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 13 12 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (1),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1),
.cycle 13 12 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 13 5 false (1),
.cycle 17 1 true (-1),
.cycle 14 4 false (1),
.last 19 (2,true),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.cycle 13 5 false (1),
.cycle 17 1 false (-1),
.cycle 8 23 false (3),
.cycle 1 17 false (3),
.cycle 13 11 false (1),
.cycle 13 15 true (-1),
.cycle 13 8 false (1),
.cycle 17 1 true (-1)
])
theorem kid04_part318_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part318) = true := by rfl

def kid04_part319 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 13 12 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 5 false (1),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 13 12 true (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 5 false (2),
.cycle 13 1 true (1),
.cycle 13 4 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 5 false (1),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 13 11 false (3),
.cycle 13 15 true (1),
.cycle 13 8 false (2),
.cycle 13 1 true (1)
])
theorem kid04_part319_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part319) = true := by rfl

def kid04_part320 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 13 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.cycle 0 17 false (3),
.cycle 13 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (0),
.cycle 16 1 true (-2),
.cycle 13 4 false (0),
.last 18 (2,true),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.cycle 13 20 false (2),
.cycle 1 16 false (3),
.cycle 13 11 false (0),
.cycle 13 15 true (-2),
.cycle 13 8 false (0),
.cycle 16 1 true (-2)
])
theorem kid04_part320_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part320) = true := by rfl

def kid04_part321 : Audit := .split 14 (2,true) (byMove [
.last 27 (5,false),
.last 20 (5,false),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.last 16 (5,false),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.last 26 (5,false),
.last 26 (5,false),
.last 24 (5,false),
.cycle 8 7 false (2),
.last 15 (5,false),
.last 21 (5,false),
.last 20 (5,false),
.last 30 (5,false),
.last 28 (5,false),
.last 16 (5,false),
.cycle 12 3 false (0),
.last 30 (5,false),
.last 32 (5,false),
.cycle 2 13 false (3),
.last 29 (5,false),
.last 25 (5,false),
.last 15 (5,false)
])
theorem kid04_part321_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part321) = true := by rfl

def kid04_part322 : Audit := .cycle 0 15 true (-1)
theorem kid04_part322_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part322) = true := by rfl

def kid04_part323 : Audit := .cycle 13 1 false (-1)
theorem kid04_part323_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part323) = true := by rfl

def kid04_part324 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 13 12 false (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 20 (2,true),
.last 49 (2,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 12 8 true (-3),
.cycle 14 4 false (-1),
.last 19 (2,true),
.last 22 (2,true),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 20 (2,true),
.last 42 (2,true),
.cycle 13 11 false (-1),
.last 22 (2,true),
.cycle 13 8 false (-1),
.cycle 11 16 false (1)
])
theorem kid04_part324_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part324) = true := by rfl

def kid04_part325 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 0 27 true (-1),
.cycle 14 12 true (-3),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 14 5 false (0),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 0 31 true (-2),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 40 25 false (0),
.cycle 1 16 false (3),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.cycle 12 3 false (0)
])
theorem kid04_part325_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part325) = true := by rfl

def kid04_part326 : Audit := .cycle 0 13 true (0)
theorem kid04_part326_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part326) = true := by rfl

def kid04_part327 : Audit := .cycle 1 12 true (0)
theorem kid04_part327_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part327) = true := by rfl

def kid04_part328 : Audit := .split 23 (5,false) (byMove [
.cycle 0 24 false (3),
.cycle 13 12 false (2),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.cycle 19 5 false (1),
.cycle 23 1 false (-1),
.cycle 0 24 true (-1),
.cycle 13 12 true (-1),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 19 5 false (1),
.cycle 23 1 true (-1),
.cycle 20 4 false (1),
.last 25 (2,true),
.cycle 0 26 true (-2),
.cycle 24 1 false (-2),
.cycle 19 5 false (1),
.cycle 23 1 false (-1),
.cycle 2 35 false (3),
.cycle 1 23 false (3),
.cycle 13 11 false (2),
.cycle 13 15 true (-1),
.cycle 17 8 false (2),
.cycle 23 1 true (-1)
])
theorem kid04_part328_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part328) = true := by rfl

def kid04_part329 : Audit := .split 27 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 16 12 false (4),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 23 5 false (3),
.cycle 27 1 false (1),
.cycle 0 28 true (0),
.cycle 16 12 true (1),
.cycle 29 1 false (3),
.cycle 28 1 false (2),
.cycle 23 5 false (3),
.cycle 27 1 true (1),
.cycle 24 4 false (3),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 28 1 false (0),
.cycle 23 5 false (3),
.cycle 27 1 false (1),
.cycle 0 28 true (0),
.cycle 1 27 true (0),
.cycle 17 11 false (4),
.cycle 13 15 true (0),
.cycle 21 8 false (4),
.cycle 27 1 true (1)
])
theorem kid04_part329_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part329) = true := by rfl

def kid04_part330 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 false (3),
.cycle 14 12 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 16 5 false (0),
.cycle 20 1 false (-2),
.cycle 0 21 false (3),
.cycle 14 12 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 16 5 false (0),
.cycle 20 1 true (-2),
.cycle 17 4 false (0),
.last 22 (2,true),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 16 5 false (0),
.cycle 20 1 false (-2),
.cycle 13 24 false (2),
.cycle 1 20 false (3),
.cycle 14 11 false (1),
.cycle 14 15 true (-2),
.cycle 13 8 false (1),
.cycle 20 1 true (-2)
])
theorem kid04_part330_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part330) = true := by rfl

def kid04_part331 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (3),
.cycle 14 12 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 5 false (0),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 13 12 true (1),
.cycle 27 1 false (1),
.cycle 24 1 false (0),
.cycle 8 6 true (0),
.cycle 13 1 true (1),
.cycle 17 4 false (0),
.last 21 (2,true),
.last 14 (2,true),
.cycle 28 1 false (0),
.cycle 14 5 false (0),
.cycle 12 3 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 13 15 true (1),
.cycle 17 8 false (1),
.cycle 13 1 true (1)
])
theorem kid04_part331_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part331) = true := by rfl

def kid04_part307 : Audit := .split 12 (5,true) (byMove [(kid04_part308),(kid04_part309),(kid04_part310),(kid04_part311),(kid04_part312),(kid04_part313),(kid04_part314),(kid04_part315),(kid04_part316),(kid04_part317),(kid04_part318),(kid04_part319),(kid04_part320),(kid04_part321),(kid04_part322),(kid04_part323),(kid04_part324),(kid04_part325),(kid04_part326),(kid04_part327),(kid04_part328),(kid04_part329),(kid04_part330),(kid04_part331)])

theorem kid04_part307_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part307) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part308),(kid04_part309),(kid04_part310),(kid04_part311),(kid04_part312),(kid04_part313),(kid04_part314),(kid04_part315),(kid04_part316),(kid04_part317),(kid04_part318),(kid04_part319),(kid04_part320),(kid04_part321),(kid04_part322),(kid04_part323),(kid04_part324),(kid04_part325),(kid04_part326),(kid04_part327),(kid04_part328),(kid04_part329),(kid04_part330),(kid04_part331)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part308_checked

  · exact kid04_part314_checked

  · exact kid04_part320_checked

  · exact kid04_part326_checked

  · exact kid04_part309_checked

  · exact kid04_part315_checked

  · exact kid04_part321_checked

  · exact kid04_part327_checked

  · exact kid04_part310_checked

  · exact kid04_part316_checked

  · exact kid04_part322_checked

  · exact kid04_part328_checked

  · exact kid04_part311_checked

  · exact kid04_part317_checked

  · exact kid04_part323_checked

  · exact kid04_part329_checked

  · exact kid04_part312_checked

  · exact kid04_part318_checked

  · exact kid04_part324_checked

  · exact kid04_part330_checked

  · exact kid04_part313_checked

  · exact kid04_part319_checked

  · exact kid04_part325_checked

  · exact kid04_part331_checked

def kid04_part332 : Audit := .cycle 0 12 true (0)
theorem kid04_part332_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part332) = true := by rfl

def kid04_part333 : Audit := .cycle 1 11 true (1)
theorem kid04_part333_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part333) = true := by rfl

def kid04_part334 : Audit := .cycle 24 1 false (2)
theorem kid04_part334_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part334) = true := by rfl

def kid04_part335 : Audit := .cycle 21 1 false (1)
theorem kid04_part335_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part335) = true := by rfl

def kid04_part336 : Audit := .cycle 8 4 true (1)
theorem kid04_part336_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part336) = true := by rfl

def kid04_part337 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 16 5 false (0),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 26 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 26 1 false (2),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 19 1 false (1),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 25 1 false (1),
.cycle 29 1 false (3),
.cycle 22 1 false (0),
.cycle 13 2 true (0)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (1),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 15 8 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 12 3 true (1),
.cycle 18 9 false (1),
.cycle 15 8 false (1),
.cycle 18 18 true (-1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 18 13 false (2),
.last 21 (5,true)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 5 false (0),
.split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 32 13 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.last 15 (2,true),
.cycle 28 1 false (4),
.cycle 21 1 false (3),
.cycle 17 1 false (3),
.cycle 18 1 false (0),
.last 16 (2,true),
.cycle 23 1 false (1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.last 15 (2,true),
.last 46 (2,true),
.cycle 6 12 true (0),
.cycle 15 3 true (1)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 6 8 true (1),
.cycle 12 1 true (2)
])
theorem kid04_part337_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part337) = true := by rfl

def kid04_part338 : Audit := .cycle 15 3 false (0)
theorem kid04_part338_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part338) = true := by rfl

def kid04_part339 : Audit := .split 18 (2,true) (byMove [
.cycle 12 14 true (-3),
.cycle 12 7 false (0),
.cycle 21 1 false (-3),
.cycle 17 30 true (-3),
.cycle 16 3 false (-2),
.split 19 (5,true) (byMove [
.cycle 0 20 false (3),
.cycle 12 14 false (0),
.cycle 21 1 false (-3),
.cycle 20 1 false (-4),
.cycle 13 7 false (-1),
.last 20 (5,false),
.cycle 17 30 true (-3),
.cycle 12 14 true (-3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 13 7 false (-1),
.last 20 (5,false),
.cycle 14 6 false (-1),
.cycle 17 3 false (-2),
.last 55 (5,false),
.cycle 20 1 false (-4),
.cycle 13 7 false (-1),
.last 20 (5,false),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 1, 64, 64],[19, 16, 32, 19, 2, 19, 64],96⟩,
.cycle 1 19 false (3),
.cycle 12 13 false (0),
.cycle 58 17 true (2),
.cycle 12 10 false (0),
.last 20 (5,false)
]),
.cycle 6 33 false (5),
.cycle 66 13 true (2),
.cycle 12 13 false (0),
.cycle 12 11 false (0),
.cycle 8 11 false (2),
.split 19 (5,false) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 426243, 33152, 256, 128, 256, 32768, 2, 33024, 260, 2, 4, 8, 33024, 33152, 256, 262144],[2, 33024, 32, 1, 131105, 262144, 8192, 33152, 131072, 4096, 164225, 262144, 2, 33024, 32, 1, 131072, 262144, 262144],288780⟩,
.cycle 1 19 false (3),
.cycle 12 13 false (0),
.cycle 58 17 true (2),
.cycle 12 10 false (0),
.last 21 (5,true),
.cycle 99 61 true (2),
.cycle 20 14 true (0),
.cycle 0 22 true (-3),
.cycle 12 13 false (0),
.cycle 27 7 true (0),
.last 21 (5,true),
.cycle 9 11 false (2),
.last 25 (5,true),
.cycle 109 69 true (1),
.cycle 12 11 false (0),
.cycle 12 10 false (0),
.last 21 (5,true),
.cycle 35 32 true (-1),
.cycle 6 33 false (5),
.cycle 66 13 true (2),
.cycle 20 17 true (-2),
.cycle 6 15 false (3),
.last 21 (5,true)
]),
.cycle 12 8 false (0),
.cycle 12 7 false (0),
.cycle 63 17 true (-1),
.cycle 54 15 true (2),
.cycle 16 3 false (-2),
.split 19 (5,true) (byMove [
.cycle 17 8 true (-4),
.cycle 7 20 false (3),
.cycle 21 1 false (-3),
.cycle 20 1 false (-4),
.cycle 13 7 false (-1),
.last 20 (5,false),
.cycle 54 15 true (2),
.cycle 12 8 false (0),
.last 21 (5,false),
.far true 1 ⟨0,[0, 0],[27, 27, 27, 8, 1, 64, 64],[27, 16, 32, 27, 2, 27, 64],96⟩,
.cycle 16 4 true (-3),
.last 21 (5,false),
.cycle 14 6 false (-1),
.cycle 17 3 false (-2),
.last 62 (5,false),
.cycle 20 1 false (-4),
.cycle 13 7 false (-1),
.last 20 (5,false),
.cycle 72 15 true (2),
.cycle 15 5 false (-1),
.cycle 18 2 true (-3),
.cycle 6 37 false (5),
.cycle 11 9 false (1),
.last 21 (5,false)
]),
.cycle 36 7 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 2, 1, 15, 64, 64],96⟩,
.cycle 2 17 false (3),
.cycle 22 16 true (0),
.cycle 12 12 false (0),
.split 19 (5,false) (byMove [
.cycle 72 15 true (2),
.cycle 15 5 false (-1),
.cycle 18 2 true (-2),
.cycle 6 37 false (5),
.cycle 11 9 false (1),
.last 20 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 301315, 37250, 1, 128, 256, 32768, 2, 37122, 4096, 2, 4, 8, 37122, 37250, 1, 262144],[2, 37122, 2048, 1, 39171, 262144, 8192, 37250, 2048, 4096, 39299, 262144, 2, 37122, 32, 1, 2048, 262144, 262144],286732⟩,
.cycle 20 14 true (0),
.cycle 0 22 true (-3),
.cycle 3 17 false (3),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 329730, 65536, 16, 128, 256, 32768, 2, 65536, 65536, 2, 4, 8, 65536, 65536, 16, 262144],[2, 65536, 2048, 1, 2048, 262144, 8192, 65536, 2048, 4096, 2048, 262144, 2, 65536, 32, 1, 2048, 262144, 262144],286732⟩,
.last 21 (5,true),
.cycle 12 12 false (0),
.cycle 15 5 false (-1),
.last 21 (5,true),
.cycle 22 16 true (0),
.cycle 11 9 false (1),
.last 20 (5,true),
.cycle 10 13 false (2),
.cycle 36 7 false (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 297219, 33152, 256, 128, 256, 32768, 2, 33024, 256, 2, 4, 8, 33024, 33152, 4, 262144],[2, 33024, 2048, 1, 2049, 262144, 8192, 33152, 2048, 4096, 35201, 262144, 2, 33024, 32, 1, 2048, 262144, 262144],417804⟩,
.cycle 240 17 true (-1),
.cycle 12 16 false (0),
.last 21 (5,true)
])
])
theorem kid04_part339_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part339) = true := by rfl

def kid04_part340 : Audit := .split 12 (2,true) (byMove [
.cycle 0 30 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 11 false (1),
.split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.last 30 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.proven (BB6.Agent11Raw39B0RBPumps.M43.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M43.never m hm),
.cycle 13 1 false (-1),
.cycle 0 19 true (-1),
.last 16 (5,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 0 25 true (-2),
.last 15 (5,true),
.last 22 (5,true),
.last 16 (5,true),
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.last 28 (5,true),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.last 16 (5,true),
.cycle 0 16 true (-1),
.cycle 0 24 true (-2),
.last 26 (5,true),
.last 15 (5,true)
]),
.cycle 0 27 true (0),
.cycle 0 20 true (-2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 0 27 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 0 20 true (-2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 0 27 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 0 20 true (0),
.last 14 (5,false),
.cycle 0 19 true (-1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 0 25 true (-2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 0 23 true (-1),
.last 14 (5,false)
]),
.cycle 0 23 true (-2),
.cycle 0 39 true (-4),
.cycle 0 29 true (-1),
.cycle 13 1 false (-1),
.cycle 0 29 true (-3),
.split 13 (5,false) (byMove [
.last 17 (5,true),
.cycle 0 31 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 23 (5,true),
.cycle 13 1 false (-1),
.cycle 0 22 true (-2),
.last 24 (5,true),
.cycle 12 2 true (-1),
.cycle 0 29 true (-1),
.cycle 0 31 true (-1),
.last 14 (5,true),
.cycle 0 29 true (-3),
.last 16 (5,true),
.cycle 0 24 true (-2),
.cycle 14 1 false (-2),
.cycle 0 35 true (-4),
.cycle 13 1 false (-1),
.cycle 0 25 false (3),
.cycle 0 23 true (-2),
.last 15 (5,true),
.cycle 0 29 true (-1),
.cycle 11 3 false (1),
.last 14 (5,true)
]),
.cycle 0 27 true (0),
.cycle 0 17 true (-1),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.split 13 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 21 false (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 0 17 true (-1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 0 27 true (0),
.last 30 (5,false),
.cycle 0 25 true (-1),
.cycle 8 6 true (0),
.last 14 (5,false),
.cycle 0 22 true (-2),
.last 24 (5,false),
.cycle 12 2 true (0),
.cycle 0 29 true (0),
.cycle 0 31 true (-1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 30 true (0),
.cycle 0 26 true (-2),
.last 14 (5,false)
])
])
theorem kid04_part340_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part340) = true := by rfl

def kid04_part341 : Audit := .cycle 25 1 false (1)
theorem kid04_part341_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part341) = true := by rfl

def kid04_part342 : Audit := .cycle 12 4 false (0)
theorem kid04_part342_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part342) = true := by rfl

def kid04_part344 : Audit := .split 15 (2,true) (byMove [
.last 28 (5,false),
.last 18 (5,false),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.cycle 11 5 false (1),
.last 29 (5,false),
.cycle 0 16 true (-1),
.last 27 (5,false),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 8 16 true (-1),
.last 16 (5,false),
.last 25 (5,false),
.last 18 (5,false),
.last 26 (5,false),
.last 29 (5,false),
.cycle 11 5 false (1),
.cycle 12 8 true (-1),
.cycle 14 16 true (0),
.cycle 14 15 true (0),
.cycle 2 28 true (-1),
.last 30 (5,false),
.last 29 (5,false),
.last 16 (5,false)
])
theorem kid04_part344_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part344) = true := by rfl

def kid04_part345 : Audit := .cycle 0 16 true (-1)
theorem kid04_part345_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part345) = true := by rfl

def kid04_part346 : Audit := .cycle 14 1 false (0)
theorem kid04_part346_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part346) = true := by rfl

def kid04_part347 : Audit := .cycle 13 1 false (-1)
theorem kid04_part347_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part347) = true := by rfl

def kid04_part348 : Audit := .split 17 (5,false) (byMove [
.last 20 (2,true),
.last 23 (2,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 51 (2,true),
.cycle 13 6 false (-1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 16 2 true (-3),
.cycle 12 6 false (0),
.cycle 14 4 false (-1),
.last 19 (2,true),
.last 55 (2,true),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 67 (2,true),
.cycle 15 3 false (-1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 11 7 false (1),
.cycle 16 3 false (-2)
])
theorem kid04_part348_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part348) = true := by rfl

def kid04_part349 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.last 31 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 14 13 true (-1),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 17 2 true (-2),
.cycle 16 1 true (0),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 16 15 true (-2),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 4 34 false (3),
.cycle 11 11 false (1),
.cycle 18 1 true (-2)
])
theorem kid04_part349_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part349) = true := by rfl

def kid04_part350 : Audit := .split 25 (5,false) (byMove [
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 27 1 false (1),
.cycle 26 1 false (0),
.cycle 21 5 false (3),
.cycle 25 1 false (1),
.cycle 13 13 true (1),
.cycle 20 6 false (4),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 24 2 true (1),
.cycle 0 27 true (0),
.cycle 22 4 false (3),
.last 27 (2,true),
.cycle 13 15 true (0),
.cycle 26 1 false (0),
.cycle 21 5 false (3),
.cycle 25 1 false (1),
.cycle 13 13 true (1),
.cycle 23 3 false (3),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 11 15 true (0),
.cycle 0 27 true (0)
])
theorem kid04_part350_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part350) = true := by rfl

def kid04_part351 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.last 81 (2,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 14 5 false (0),
.cycle 18 1 false (-2),
.cycle 13 13 true (-2),
.cycle 13 6 false (1),
.last 19 (2,true),
.cycle 0 20 true (-2),
.cycle 17 2 true (-2),
.cycle 13 13 true (-2),
.cycle 15 4 false (0),
.last 20 (2,true),
.cycle 13 15 true (-3),
.cycle 19 1 false (-3),
.cycle 14 5 false (0),
.cycle 18 1 false (-2),
.cycle 13 13 true (-2),
.cycle 16 3 false (0),
.last 19 (2,true),
.cycle 7 26 false (3),
.cycle 11 8 false (1),
.cycle 13 13 true (-2)
])
theorem kid04_part351_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part351) = true := by rfl

def kid04_part352 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.last 25 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 18 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 25 (5,false),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.last 18 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.last 18 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 24 (5,false),
.last 28 (5,false),
.last 21 (5,false),
.last 14 (5,false)
])
theorem kid04_part352_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part352) = true := by rfl

def kid04_part353 : Audit := .cycle 0 14 true (0)
theorem kid04_part353_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part353) = true := by rfl

def kid04_part354 : Audit := .split 14 (5,false) (byMove [
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.cycle 13 13 true (0),
.cycle 13 6 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 13 6 true (0),
.cycle 13 4 false (1),
.last 16 (2,true),
.cycle 13 15 true (-1),
.cycle 15 1 false (-1),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.cycle 13 13 true (0),
.cycle 13 3 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 8 8 true (0)
])
theorem kid04_part354_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part354) = true := by rfl

def kid04_part355 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 30 true (-1),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 5 false (2),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 21 6 false (5),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 18 2 true (1),
.cycle 14 1 true (2),
.cycle 14 4 false (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 5 false (2),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.last 26 (2,true),
.cycle 0 31 true (0),
.cycle 11 12 true (0),
.cycle 14 1 true (2)
])
theorem kid04_part355_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part355) = true := by rfl

def kid04_part356 : Audit := .split 16 (5,false) (byMove [
.last 19 (2,true),
.last 52 (2,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.last 19 (2,true),
.cycle 13 6 false (0),
.last 17 (2,true),
.cycle 0 23 true (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 13 4 false (0),
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.last 19 (2,true),
.cycle 14 3 false (0),
.last 17 (2,true),
.last 50 (2,true),
.cycle 11 6 false (1),
.cycle 13 8 false (0)
])
theorem kid04_part356_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part356) = true := by rfl

def kid04_part357 : Audit := .split 14 (2,true) (byMove [
.last 30 (5,false),
.last 20 (5,false),
.cycle 17 1 false (-1),
.last 19 (5,false),
.last 16 (5,false),
.cycle 12 3 false (0),
.last 27 (5,false),
.last 23 (5,false),
.last 28 (5,false),
.cycle 0 16 true (-1),
.last 16 (5,false),
.last 18 (5,false),
.last 21 (5,false),
.last 20 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.cycle 12 3 false (0),
.last 27 (5,false),
.cycle 10 5 false (2),
.last 32 (5,false),
.cycle 0 16 true (-1),
.last 22 (5,false),
.last 18 (5,false)
])
theorem kid04_part357_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part357) = true := by rfl

def kid04_part358 : Audit := .split 27 (5,false) (byMove [
.last 30 (2,true),
.cycle 0 31 true (-1),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 23 5 false (3),
.cycle 27 1 false (1),
.cycle 15 13 true (1),
.cycle 22 6 false (4),
.last 28 (2,true),
.cycle 0 29 true (-1),
.cycle 26 2 true (1),
.cycle 0 31 true (-1),
.cycle 24 4 false (3),
.last 29 (2,true),
.cycle 13 15 true (-1),
.cycle 28 1 false (0),
.cycle 23 5 false (3),
.cycle 27 1 false (1),
.cycle 15 13 true (1),
.cycle 25 3 false (3),
.last 28 (2,true),
.cycle 0 29 true (-1),
.cycle 11 17 true (-1),
.last 29 (2,true)
])
theorem kid04_part358_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part358) = true := by rfl

def kid04_part359 : Audit := .cycle 13 1 false (-1)
theorem kid04_part359_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part359) = true := by rfl

def kid04_part360 : Audit := .split 17 (5,false) (byMove [
.last 20 (2,true),
.last 93 (2,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 20 (2,true),
.cycle 13 6 false (-1),
.last 18 (2,true),
.cycle 0 29 true (-3),
.cycle 16 2 true (-3),
.cycle 12 6 false (0),
.cycle 14 4 false (-1),
.last 19 (2,true),
.last 22 (2,true),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 20 (2,true),
.cycle 15 3 false (-1),
.last 18 (2,true),
.last 81 (2,true),
.cycle 11 7 false (1),
.cycle 16 3 false (-2)
])
theorem kid04_part360_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part360) = true := by rfl

def kid04_part361 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 0 33 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 14 13 true (-2),
.cycle 13 6 false (0),
.last 14 (2,true),
.cycle 0 29 true (-1),
.cycle 13 2 true (-1),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 15 15 true (-3),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 17 13 true (-3),
.cycle 13 3 false (0),
.last 14 (2,true),
.cycle 0 29 true (-1),
.cycle 11 3 false (1),
.cycle 12 3 false (0)
])
theorem kid04_part361_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part361) = true := by rfl

def kid04_part362 : Audit := .split 25 (5,false) (byMove [
.last 28 (2,true),
.last 92 (2,true),
.last 26 (2,true),
.cycle 31 1 false (-1),
.cycle 26 5 false (0),
.cycle 9 18 true (0),
.cycle 13 13 true (1),
.cycle 29 6 false (1),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 24 2 true (1),
.cycle 0 27 true (0),
.cycle 29 4 false (0),
.last 33 (2,true),
.last 26 (2,true),
.cycle 34 1 false (-2),
.cycle 26 5 false (0),
.cycle 36 1 false (-2),
.cycle 13 13 true (1),
.cycle 10 16 true (0),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 11 15 true (0),
.cycle 0 27 true (0)
])
theorem kid04_part362_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part362) = true := by rfl

def kid04_part363 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 13 5 false (1),
.cycle 15 1 false (-1),
.cycle 13 13 true (-1),
.cycle 13 6 false (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 14 2 true (-1),
.cycle 1 16 true (-1),
.cycle 13 4 false (1),
.last 17 (2,true),
.cycle 13 15 true (-2),
.cycle 16 1 false (-2),
.cycle 13 5 false (1),
.cycle 15 1 false (-1),
.cycle 13 13 true (-1),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 11 5 false (1),
.cycle 10 19 false (3)
])
theorem kid04_part363_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part363) = true := by rfl

def kid04_part364 : Audit := .split 13 (2,true) (byMove [
.last 26 (5,false),
.last 19 (5,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 25 (5,false),
.cycle 0 14 true (0),
.last 25 (5,false),
.last 25 (5,false),
.last 23 (5,false),
.cycle 8 6 true (0),
.last 14 (5,false),
.last 20 (5,false),
.last 19 (5,false),
.last 29 (5,false),
.last 27 (5,false),
.last 15 (5,false),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.last 28 (5,false),
.last 24 (5,false),
.last 14 (5,false)
])
theorem kid04_part364_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part364) = true := by rfl

def kid04_part365 : Audit := .cycle 0 14 true (0)
theorem kid04_part365_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part365) = true := by rfl

def kid04_part366 : Audit := .cycle 11 2 true (0)
theorem kid04_part366_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part366) = true := by rfl

def kid04_part367 : Audit := .split 14 (5,false) (byMove [
.last 30 (2,true),
.cycle 0 21 true (-2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 33 6 false (1),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.cycle 14 1 true (2),
.cycle 21 4 false (0),
.last 19 (2,true),
.last 15 (2,true),
.cycle 38 1 false (-2),
.cycle 12 5 true (0),
.cycle 12 3 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 0 31 true (0),
.cycle 11 18 false (3),
.cycle 14 1 true (2)
])
theorem kid04_part367_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part367) = true := by rfl

def kid04_part343 : Audit := .split 12 (5,true) (byMove [(kid04_part344),(kid04_part345),(kid04_part346),(kid04_part347),(kid04_part348),(kid04_part349),(kid04_part350),(kid04_part351),(kid04_part352),(kid04_part353),(kid04_part354),(kid04_part355),(kid04_part356),(kid04_part357),(kid04_part358),(kid04_part359),(kid04_part360),(kid04_part361),(kid04_part362),(kid04_part363),(kid04_part364),(kid04_part365),(kid04_part366),(kid04_part367)])

theorem kid04_part343_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part343) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part344),(kid04_part345),(kid04_part346),(kid04_part347),(kid04_part348),(kid04_part349),(kid04_part350),(kid04_part351),(kid04_part352),(kid04_part353),(kid04_part354),(kid04_part355),(kid04_part356),(kid04_part357),(kid04_part358),(kid04_part359),(kid04_part360),(kid04_part361),(kid04_part362),(kid04_part363),(kid04_part364),(kid04_part365),(kid04_part366),(kid04_part367)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part344_checked

  · exact kid04_part350_checked

  · exact kid04_part356_checked

  · exact kid04_part362_checked

  · exact kid04_part345_checked

  · exact kid04_part351_checked

  · exact kid04_part357_checked

  · exact kid04_part363_checked

  · exact kid04_part346_checked

  · exact kid04_part352_checked

  · exact kid04_part358_checked

  · exact kid04_part364_checked

  · exact kid04_part347_checked

  · exact kid04_part353_checked

  · exact kid04_part359_checked

  · exact kid04_part365_checked

  · exact kid04_part348_checked

  · exact kid04_part354_checked

  · exact kid04_part360_checked

  · exact kid04_part366_checked

  · exact kid04_part349_checked

  · exact kid04_part355_checked

  · exact kid04_part361_checked

  · exact kid04_part367_checked

def kid04_part368 : Audit := .cycle 0 12 true (0)
theorem kid04_part368_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part368) = true := by rfl

def kid04_part369 : Audit := .cycle 1 11 true (1)
theorem kid04_part369_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part369) = true := by rfl

def kid04_part370 : Audit := .cycle 2 10 true (1)
theorem kid04_part370_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part370) = true := by rfl

def kid04_part371 : Audit := .cycle 1 14 true (1)
theorem kid04_part371_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part371) = true := by rfl

def kid04_part372 : Audit := .cycle 15 7 false (1)
theorem kid04_part372_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part372) = true := by rfl

def kid04_part373 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 13 6 false (1),
.split 13 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 14 6 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 29 1 false (1),
.cycle 17 5 false (0),
.cycle 13 9 false (1),
.cycle 0 33 true (-1),
.cycle 29 1 false (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 9 false (1),
.cycle 12 2 true (1)
]),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.split 13 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 6 false (1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 17 1 false (1),
.cycle 17 5 false (0),
.last 22 (2,true),
.last 14 (2,true),
.cycle 29 1 false (1),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 9 false (1),
.cycle 12 2 true (1)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.cycle 13 6 false (1),
.split 13 (2,true) (byMove [
.cycle 15 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 14 6 false (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 17 7 false (1),
.cycle 48 1 false (8),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.last 14 (5,true),
.cycle 17 5 false (0),
.cycle 13 9 false (1),
.cycle 16 16 true (-1),
.cycle 23 1 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.last 14 (5,true)
]),
.cycle 1 14 true (1),
.split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 15 8 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.cycle 15 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 19 11 false (1),
.cycle 18 9 false (1),
.cycle 15 8 false (1),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 13 2 true (1),
.cycle 15 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 18 13 false (2),
.cycle 12 3 true (1)
]),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.last 26 (2,true),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 14 6 false (1),
.cycle 15 1 false (-1),
.cycle 1 14 true (1),
.cycle 17 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 22 1 false (4),
.cycle 17 5 false (0),
.last 22 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 12 3 true (1)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 16 11 false (2),
.cycle 12 1 true (2)
])
theorem kid04_part373_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part373) = true := by rfl

def kid04_part301 : Audit := .split 11 (4,true) (byMove [(kid04_part302),(kid04_part303),(kid04_part304),(kid04_part305),(kid04_part306),(kid04_part307),(kid04_part332),(kid04_part333),(kid04_part334),(kid04_part335),(kid04_part336),(kid04_part337),(kid04_part338),(kid04_part339),(kid04_part340),(kid04_part341),(kid04_part342),(kid04_part343),(kid04_part368),(kid04_part369),(kid04_part370),(kid04_part371),(kid04_part372),(kid04_part373)])

theorem kid04_part301_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (kid04_part301) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (4,true) (some mv)) (byMove [(kid04_part302),(kid04_part303),(kid04_part304),(kid04_part305),(kid04_part306),(kid04_part307),(kid04_part332),(kid04_part333),(kid04_part334),(kid04_part335),(kid04_part336),(kid04_part337),(kid04_part338),(kid04_part339),(kid04_part340),(kid04_part341),(kid04_part342),(kid04_part343),(kid04_part368),(kid04_part369),(kid04_part370),(kid04_part371),(kid04_part372),(kid04_part373)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part302_checked

  · exact kid04_part332_checked

  · exact kid04_part338_checked

  · exact kid04_part368_checked

  · exact kid04_part303_checked

  · exact kid04_part333_checked

  · exact kid04_part339_checked

  · exact kid04_part369_checked

  · exact kid04_part304_checked

  · exact kid04_part334_checked

  · exact kid04_part340_checked

  · exact kid04_part370_checked

  · exact kid04_part305_checked

  · exact kid04_part335_checked

  · exact kid04_part341_checked

  · exact kid04_part371_checked

  · exact kid04_part306_checked

  · exact kid04_part336_checked

  · exact kid04_part342_checked

  · exact kid04_part372_checked

  · exact kid04_part307_checked

  · exact kid04_part337_checked

  · exact kid04_part343_checked

  · exact kid04_part373_checked

def kid04_part375 : Audit := .cycle 1 11 true (1)
theorem kid04_part375_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part375) = true := by rfl

def kid04_part376 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 20 4 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 20 4 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 true (-1),
.cycle 11 4 false (1),
.cycle 14 4 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 1 13 false (3),
.cycle 19 4 false (1),
.cycle 23 4 false (3),
.cycle 15 4 false (-1),
.cycle 13 1 true (-1)
]),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 20 4 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 20 4 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 4 false (2),
.cycle 13 1 true (1),
.cycle 11 4 true (0),
.cycle 14 4 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 4 false (3),
.cycle 23 4 false (5),
.cycle 15 4 false (1),
.cycle 13 1 true (1)
]),
.cycle 11 3 false (1),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 21 4 false (3),
.cycle 14 4 false (0),
.cycle 21 4 false (1),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 11 4 false (1),
.cycle 14 4 false (-1),
.cycle 23 4 false (3),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 27 4 false (-1),
.cycle 11 3 false (1),
.cycle 14 4 false (0),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 22 4 false (4),
.cycle 14 4 false (0),
.split 13 (5,false) (byMove [
.cycle 21 4 false (3),
.cycle 14 4 false (0),
.cycle 21 4 false (1),
.cycle 0 15 true (0),
.cycle 12 2 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 26 4 false (0),
.cycle 20 4 false (2),
.cycle 18 4 false (2),
.cycle 8 6 true (0),
.cycle 13 1 true (1),
.cycle 15 4 false (1),
.cycle 14 4 false (0),
.cycle 0 18 true (-1),
.cycle 22 4 false (4),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 20 true (0),
.cycle 12 6 true (0),
.cycle 13 1 true (1)
])
])
theorem kid04_part376_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part376) = true := by rfl

def kid04_part377 : Audit := .cycle 14 1 false (0)
theorem kid04_part377_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part377) = true := by rfl

def kid04_part378 : Audit := .cycle 0 12 true (0)
theorem kid04_part378_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part378) = true := by rfl

def kid04_part379 : Audit := .split 11 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.last 24 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 17 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (5,false),
.last 27 (5,false),
.last 19 (5,false),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 15 5 false (-1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 11 4 true (1),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 5 false (-1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 7 false (1),
.cycle 12 1 true (2)
]),
.cycle 17 3 false (-1),
.cycle 14 3 false (-1),
.cycle 9 11 false (2),
.cycle 25 1 false (1),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 25 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 27 (5,false),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 25 (5,false),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 14 6 false (1),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 14 6 false (1),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 16 7 false (0),
.cycle 14 6 false (1),
.cycle 13 6 false (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 6 true (1),
.cycle 12 1 true (2)
])
])
theorem kid04_part379_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part379) = true := by rfl

def kid04_part381 : Audit := .cycle 0 24 true (0)
theorem kid04_part381_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part381) = true := by rfl

def kid04_part382 : Audit := .cycle 12 11 false (0)
theorem kid04_part382_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part382) = true := by rfl

def kid04_part383 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 1 true (-1),
.last 16 (4,true),
.cycle 18 1 false (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 29 1 false (-1),
.cycle 1 13 false (3),
.cycle 25 1 false (-1),
.cycle 29 1 false (1),
.cycle 21 1 false (-3),
.cycle 13 1 true (-1)
])
theorem kid04_part383_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part383) = true := by rfl

def kid04_part384 : Audit := .cycle 0 13 true (0)
theorem kid04_part384_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part384) = true := by rfl

def kid04_part385 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 20 4 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.last 13 (5,false),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 4 false (1),
.cycle 23 4 false (3),
.cycle 15 4 false (-1),
.last 13 (5,false)
])
theorem kid04_part385_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part385) = true := by rfl

def kid04_part386 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 12 5 false (0),
.cycle 13 1 true (-1),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 11 15 false (3),
.cycle 1 13 false (3),
.cycle 12 11 false (1),
.cycle 12 15 true (-1),
.cycle 12 7 false (0),
.cycle 13 1 true (-1)
])
theorem kid04_part386_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part386) = true := by rfl

def kid04_part387 : Audit := .cycle 0 12 true (0)
theorem kid04_part387_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part387) = true := by rfl

def kid04_part388 : Audit := .cycle 1 11 true (1)
theorem kid04_part388_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part388) = true := by rfl

def kid04_part389 : Audit := .cycle 24 1 false (2)
theorem kid04_part389_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part389) = true := by rfl

def kid04_part390 : Audit := .cycle 21 1 false (1)
theorem kid04_part390_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part390) = true := by rfl

def kid04_part391 : Audit := .cycle 8 4 true (1)
theorem kid04_part391_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part391) = true := by rfl

def kid04_part392 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 15 5 false (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.last 15 (4,true),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 5 false (-1),
.cycle 17 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 7 false (1),
.cycle 12 1 true (2)
])
theorem kid04_part392_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part392) = true := by rfl

def kid04_part393 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 false (3),
.cycle 12 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 0 21 false (3),
.cycle 12 14 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 18 3 false (-1),
.cycle 15 6 false (0),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 66 20 true (-3),
.cycle 1 20 false (3),
.cycle 12 13 false (1),
.cycle 12 17 true (-2),
.cycle 13 9 false (1),
.last 21 (5,false)
])
theorem kid04_part393_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part393) = true := by rfl

def kid04_part394 : Audit := .cycle 14 3 false (-1)
theorem kid04_part394_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part394) = true := by rfl

def kid04_part395 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 9 19 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 40 (4,true),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 0 19 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 22 (4,true),
.cycle 0 18 true (-1),
.last 16 (4,true),
.cycle 9 11 false (2),
.last 18 (4,true),
.cycle 14 1 false (-2),
.last 22 (4,true),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 0 24 true (-2),
.cycle 9 14 false (2),
.last 22 (4,true)
])
theorem kid04_part395_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part395) = true := by rfl

def kid04_part396 : Audit := .cycle 25 1 false (1)
theorem kid04_part396_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part396) = true := by rfl

def kid04_part397 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 21 4 false (3),
.cycle 14 4 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 14 4 false (2),
.cycle 13 4 false (1),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 23 4 false (3),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 27 4 false (-1),
.cycle 1 14 true (0),
.cycle 13 4 false (1),
.cycle 0 14 true (0),
.cycle 19 4 false (-1),
.cycle 11 2 true (0)
])
theorem kid04_part397_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part397) = true := by rfl

def kid04_part398 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 0 33 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 14 13 true (-2),
.cycle 12 6 false (0),
.cycle 0 18 true (-1),
.cycle 0 29 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 15 15 true (-3),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.last 60 (4,true),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 29 true (-1),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part398_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part398) = true := by rfl

def kid04_part399 : Audit := .cycle 0 12 true (0)
theorem kid04_part399_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part399) = true := by rfl

def kid04_part400 : Audit := .cycle 1 11 true (1)
theorem kid04_part400_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part400) = true := by rfl

def kid04_part401 : Audit := .cycle 2 10 true (1)
theorem kid04_part401_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part401) = true := by rfl

def kid04_part402 : Audit := .cycle 1 14 true (1)
theorem kid04_part402_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part402) = true := by rfl

def kid04_part403 : Audit := .split 14 (4,true) (byMove [
.cycle 0 19 true (-1),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 6 false (-1),
.last 15 (5,false),
.cycle 0 18 true (0),
.cycle 15 6 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 15 6 false (1),
.last 15 (5,false),
.cycle 13 3 false (1),
.cycle 15 6 false (0),
.cycle 0 22 true (-1),
.cycle 15 1 false (-1),
.cycle 15 6 false (-1),
.last 15 (5,false),
.cycle 0 18 true (0),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 18 6 false (2),
.cycle 15 6 false (1),
.last 15 (5,false)
])
theorem kid04_part403_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part403) = true := by rfl

def kid04_part404 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 16 7 false (0),
.last 14 (4,true),
.last 22 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 11 3 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 12 1 true (2)
])
theorem kid04_part404_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part404) = true := by rfl

def kid04_part380 : Audit := .split 11 (5,true) (byMove [(kid04_part381),(kid04_part382),(kid04_part383),(kid04_part384),(kid04_part385),(kid04_part386),(kid04_part387),(kid04_part388),(kid04_part389),(kid04_part390),(kid04_part391),(kid04_part392),(kid04_part393),(kid04_part394),(kid04_part395),(kid04_part396),(kid04_part397),(kid04_part398),(kid04_part399),(kid04_part400),(kid04_part401),(kid04_part402),(kid04_part403),(kid04_part404)])

theorem kid04_part380_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part380) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part381),(kid04_part382),(kid04_part383),(kid04_part384),(kid04_part385),(kid04_part386),(kid04_part387),(kid04_part388),(kid04_part389),(kid04_part390),(kid04_part391),(kid04_part392),(kid04_part393),(kid04_part394),(kid04_part395),(kid04_part396),(kid04_part397),(kid04_part398),(kid04_part399),(kid04_part400),(kid04_part401),(kid04_part402),(kid04_part403),(kid04_part404)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part381_checked

  · exact kid04_part387_checked

  · exact kid04_part393_checked

  · exact kid04_part399_checked

  · exact kid04_part382_checked

  · exact kid04_part388_checked

  · exact kid04_part394_checked

  · exact kid04_part400_checked

  · exact kid04_part383_checked

  · exact kid04_part389_checked

  · exact kid04_part395_checked

  · exact kid04_part401_checked

  · exact kid04_part384_checked

  · exact kid04_part390_checked

  · exact kid04_part396_checked

  · exact kid04_part402_checked

  · exact kid04_part385_checked

  · exact kid04_part391_checked

  · exact kid04_part397_checked

  · exact kid04_part403_checked

  · exact kid04_part386_checked

  · exact kid04_part392_checked

  · exact kid04_part398_checked

  · exact kid04_part404_checked

def kid04_part405 : Audit := .cycle 0 11 true (0)
theorem kid04_part405_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part405) = true := by rfl

def kid04_part406 : Audit := .cycle 1 10 true (1)
theorem kid04_part406_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part406) = true := by rfl

def kid04_part407 : Audit := .cycle 0 23 true (0)
theorem kid04_part407_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part407) = true := by rfl

def kid04_part408 : Audit := .cycle 3 8 true (1)
theorem kid04_part408_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part408) = true := by rfl

def kid04_part409 : Audit := .cycle 8 3 true (1)
theorem kid04_part409_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part409) = true := by rfl

def kid04_part411 : Audit := .cycle 0 12 true (0)
theorem kid04_part411_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part411) = true := by rfl

def kid04_part412 : Audit := .cycle 1 11 true (1)
theorem kid04_part412_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part412) = true := by rfl

def kid04_part413 : Audit := .cycle 2 10 true (1)
theorem kid04_part413_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part413) = true := by rfl

def kid04_part414 : Audit := .cycle 1 14 true (1)
theorem kid04_part414_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part414) = true := by rfl

def kid04_part415 : Audit := .split 14 (4,true) (byMove [
.cycle 0 19 true (-1),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.cycle 16 6 false (-1),
.cycle 0 18 true (0),
.cycle 15 6 false (3),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.last 18 (5,true),
.cycle 16 6 false (1),
.cycle 13 3 false (1),
.cycle 15 6 false (1),
.cycle 0 22 true (-1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.cycle 16 6 false (-1),
.cycle 0 18 true (0),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 18 6 false (2),
.cycle 15 6 false (1),
.cycle 14 2 true (0)
])
theorem kid04_part415_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part415) = true := by rfl

def kid04_part416 : Audit := .split 13 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 17 1 false (1),
.last 24 (4,true),
.cycle 16 5 false (0),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 12 2 true (1)
])
theorem kid04_part416_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part416) = true := by rfl

def kid04_part417 : Audit := .cycle 0 12 true (0)
theorem kid04_part417_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part417) = true := by rfl

def kid04_part418 : Audit := .cycle 1 11 true (1)
theorem kid04_part418_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part418) = true := by rfl

def kid04_part419 : Audit := .split 25 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 12 14 true (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 131072, 4, 128, 256, 32768, 524290, 1073872896, 16384, 33554432, 67108864, 2097152, 1048832, 131072, 1048576, 128, 256, 32768, 131072, 536870912, 16384, 33554432, 67108864, 134217728, 1863754112, 1610743808, 67108864, 1073741824],[2, 1048576, 32, 1, 1073741824, 0, 8192, 1073741824, 131072, 4096, 1073741824, 33554560, 524288, 1141899264, 8388608, 262144, 1073741824, 1048832, 8192, 1048576, 131072, 4096, 1073741824, 32768, 33554432, 1141899264, 536870912, 16777216, 1073741824, 1863754112, 1073741824],2134914048⟩,
.cycle 8 18 true (1),
.cycle 0 45 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 36, 2080, 4, 8192, 16384, 8, 6, 2080, 4, 8192, 16384, 512, 2, 262144, 256, 262144],[2, 4, 32, 1, 262144, 4, 2, 262144, 32, 1, 262144, 4, 128, 262144, 2048, 64, 262144, 256, 262144],327680⟩,
.cycle 0 41 true (0),
.cycle 8 18 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 36, 2080, 4, 8192, 16384, 8, 6, 2080, 4, 8192, 16384, 512, 2, 262144, 256, 262144],[2, 4, 32, 1, 262144, 32, 2, 262144, 32, 1, 262144, 32, 128, 262144, 2048, 64, 262144, 2048, 262144],327680⟩,
.last 28 (4,true),
.cycle 9 17 true (1),
.cycle 0 28 true (0),
.cycle 14 12 true (1),
.last 34 (4,true),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 36, 2080, 4, 8192, 16384, 8, 6, 2080, 4, 8192, 16384, 512, 2, 262144, 256, 262144],[2, 4, 32, 1, 262144, 32, 2, 262144, 32, 1, 262144, 32, 128, 262144, 2048, 64, 262144, 32, 262144],327680⟩,
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.last 50 (4,true),
.cycle 25 32 true (5)
])
theorem kid04_part419_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part419) = true := by rfl

def kid04_part420 : Audit := .cycle 0 23 true (0)
theorem kid04_part420_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part420) = true := by rfl

def kid04_part421 : Audit := .cycle 8 4 true (1)
theorem kid04_part421_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part421) = true := by rfl

def kid04_part422 : Audit := .cycle 11 1 true (3)
theorem kid04_part422_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part422) = true := by rfl

def kid04_part423 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 23 8 false (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 15 8 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 11 4 true (2),
.cycle 18 9 false (0),
.cycle 17 8 false (1),
.last 16 (5,true),
.cycle 1 16 true (1),
.last 20 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 16 12 false (2),
.cycle 23 12 false (1)
])
theorem kid04_part423_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part423) = true := by rfl

def kid04_part424 : Audit := .cycle 9 3 true (1)
theorem kid04_part424_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part424) = true := by rfl

def kid04_part425 : Audit := .cycle 0 14 true (0)
theorem kid04_part425_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part425) = true := by rfl

def kid04_part426 : Audit := .cycle 4 8 true (1)
theorem kid04_part426_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part426) = true := by rfl

def kid04_part427 : Audit := .split 14 (4,true) (byMove [
.cycle 0 75 true (-2),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.last 19 (5,true),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 24 6 false (6),
.cycle 15 1 false (1),
.last 18 (5,true),
.last 19 (5,true),
.cycle 13 3 false (1),
.cycle 15 6 false (1),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.last 19 (5,true),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 37 6 false (1),
.cycle 18 6 false (2),
.cycle 15 6 false (1),
.last 17 (5,true)
])
theorem kid04_part427_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part427) = true := by rfl

def kid04_part428 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 27 true (-3),
.cycle 15 1 false (1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.cycle 16 7 false (0),
.cycle 36 1 false (6),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 25 1 false (5),
.last 24 (4,true),
.last 42 (4,true),
.cycle 15 10 true (0),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 3 true (2)
])
theorem kid04_part428_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part428) = true := by rfl

def kid04_part429 : Audit := .cycle 0 12 true (0)
theorem kid04_part429_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part429) = true := by rfl

def kid04_part430 : Audit := .cycle 1 11 true (1)
theorem kid04_part430_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part430) = true := by rfl

def kid04_part431 : Audit := .cycle 2 10 true (1)
theorem kid04_part431_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part431) = true := by rfl

def kid04_part432 : Audit := .cycle 1 14 true (1)
theorem kid04_part432_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part432) = true := by rfl

def kid04_part433 : Audit := .split 16 (4,true) (byMove [
.cycle 0 24 true (-1),
.cycle 23 8 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 23 8 false (-1),
.last 25 (5,true),
.cycle 9 12 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 402688, 131072, 1024, 128, 256, 32768, 2, 139264, 1024, 128, 256, 8, 1024, 131072, 1024, 262144],[2, 1024, 32, 1, 2, 262144, 8192, 256, 131072, 4096, 8192, 262144, 2, 1280, 32, 1, 2, 262144, 262144],278540⟩,
.cycle 23 1 false (5),
.cycle 17 1 false (1),
.last 20 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 394290, 131104, 1024, 128, 256, 32768, 2, 131104, 1024, 2, 4, 8, 1040, 131072, 16, 262144],[2, 1040, 32, 1, 32, 262144, 8192, 1040, 131072, 4096, 131072, 262144, 2, 1040, 32, 1, 32, 262144, 262144],286732⟩,
.cycle 15 3 false (1),
.cycle 17 8 false (2),
.cycle 9 16 true (-1),
.cycle 17 1 false (-1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 9 12 true (0),
.cycle 1 20 true (0),
.cycle 0 43 true (0),
.cycle 104 32 false (4),
.cycle 27 12 false (2),
.cycle 18 6 true (2)
])
theorem kid04_part433_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part433) = true := by rfl

def kid04_part434 : Audit := .cycle 11 1 true (3)
theorem kid04_part434_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part434) = true := by rfl

def kid04_part410 : Audit := .split 11 (5,false) (byMove [(kid04_part411),(kid04_part412),(kid04_part413),(kid04_part414),(kid04_part415),(kid04_part416),(kid04_part417),(kid04_part418),(kid04_part419),(kid04_part420),(kid04_part421),(kid04_part422),(kid04_part423),(kid04_part424),(kid04_part425),(kid04_part426),(kid04_part427),(kid04_part428),(kid04_part429),(kid04_part430),(kid04_part431),(kid04_part432),(kid04_part433),(kid04_part434)])

theorem kid04_part410_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part410) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part411),(kid04_part412),(kid04_part413),(kid04_part414),(kid04_part415),(kid04_part416),(kid04_part417),(kid04_part418),(kid04_part419),(kid04_part420),(kid04_part421),(kid04_part422),(kid04_part423),(kid04_part424),(kid04_part425),(kid04_part426),(kid04_part427),(kid04_part428),(kid04_part429),(kid04_part430),(kid04_part431),(kid04_part432),(kid04_part433),(kid04_part434)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part411_checked

  · exact kid04_part417_checked

  · exact kid04_part423_checked

  · exact kid04_part429_checked

  · exact kid04_part412_checked

  · exact kid04_part418_checked

  · exact kid04_part424_checked

  · exact kid04_part430_checked

  · exact kid04_part413_checked

  · exact kid04_part419_checked

  · exact kid04_part425_checked

  · exact kid04_part431_checked

  · exact kid04_part414_checked

  · exact kid04_part420_checked

  · exact kid04_part426_checked

  · exact kid04_part432_checked

  · exact kid04_part415_checked

  · exact kid04_part421_checked

  · exact kid04_part427_checked

  · exact kid04_part433_checked

  · exact kid04_part416_checked

  · exact kid04_part422_checked

  · exact kid04_part428_checked

  · exact kid04_part434_checked

def kid04_part435 : Audit := .cycle 14 5 false (0)
theorem kid04_part435_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part435) = true := by rfl

def kid04_part436 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 20 4 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 9 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.last 16 (5,true),
.cycle 11 4 false (1),
.cycle 14 4 false (-1),
.cycle 9 8 true (-2),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.last 19 (5,true),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 17 4 false (2),
.cycle 15 4 false (-1),
.last 16 (5,true)
]),
.cycle 0 16 true (0),
.cycle 13 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.split 13 (5,false) (byMove [
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 21 4 false (5),
.cycle 14 4 false (2),
.cycle 15 4 false (2),
.cycle 0 15 true (0),
.cycle 16 4 false (4),
.last 14 (5,true),
.cycle 11 4 true (0),
.cycle 14 4 false (1),
.cycle 23 4 false (5),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 27 4 false (1),
.cycle 1 16 true (0),
.cycle 14 4 false (2),
.cycle 0 15 true (0),
.cycle 19 4 false (1),
.last 14 (5,true)
]),
.cycle 11 3 false (1),
.cycle 13 4 false (0),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 0 24 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 15 4 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (0),
.cycle 0 20 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 11 4 false (1),
.cycle 14 4 false (-1),
.cycle 17 4 false (2),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 19 4 false (-1),
.cycle 11 3 false (1),
.cycle 14 4 false (0),
.cycle 0 20 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 16 true (0),
.cycle 9 4 true (0),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.cycle 14 4 false (0),
.split 13 (5,false) (byMove [
.cycle 15 4 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (0),
.cycle 0 20 true (0),
.cycle 12 2 true (0),
.last 14 (5,true),
.cycle 23 10 true (0),
.cycle 16 4 false (0),
.cycle 9 6 true (0),
.cycle 0 15 true (0),
.cycle 8 8 true (0),
.last 14 (5,true),
.cycle 15 4 false (1),
.cycle 14 4 false (0),
.cycle 15 4 false (0),
.cycle 16 4 false (2),
.last 15 (5,true),
.last 14 (5,true),
.cycle 23 8 true (0),
.cycle 1 16 true (0),
.cycle 10 4 true (0),
.cycle 0 15 true (0),
.cycle 11 6 true (0),
.last 14 (5,true)
])
])
theorem kid04_part436_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part436) = true := by rfl

def kid04_part437 : Audit := .cycle 14 14 true (-1)
theorem kid04_part437_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part437) = true := by rfl

def kid04_part438 : Audit := .cycle 1 12 true (1)
theorem kid04_part438_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part438) = true := by rfl

def kid04_part439 : Audit := .split 11 (4,true) (byMove [
.cycle 9 8 true (0),
.cycle 7 17 false (3),
.cycle 18 1 false (-2),
.cycle 16 1 false (0),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 17 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.cycle 9 4 true (0),
.cycle 0 15 true (0),
.last 21 (5,false),
.last 19 (5,false),
.last 13 (5,false)
]),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 15 5 false (-1),
.cycle 0 13 true (0),
.cycle 8 5 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 15 5 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.last 13 (5,false),
.last 16 (5,false),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 5 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 7 false (1),
.last 13 (5,false)
]),
.cycle 17 3 false (-1),
.cycle 14 3 false (-1),
.cycle 32 14 true (-1),
.cycle 19 1 false (-1),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 9 5 false (2),
.last 28 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.last 26 (5,false),
.last 14 (5,false),
.last 15 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 21 (5,false),
.last 15 (5,false),
.last 15 (5,false),
.last 26 (5,false),
.cycle 11 2 true (0),
.last 15 (5,false)
]),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.cycle 15 10 false (2),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.last 15 (5,false),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 16 7 false (0),
.last 15 (5,false),
.cycle 13 6 false (1),
.cycle 1 14 true (1),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid04_part439_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part439) = true := by rfl

def kid04_part441 : Audit := .cycle 9 8 true (0)
theorem kid04_part441_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part441) = true := by rfl

def kid04_part442 : Audit := .cycle 7 17 false (3)
theorem kid04_part442_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part442) = true := by rfl

def kid04_part443 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.last 19 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 19 1 false (1),
.cycle 20 1 false (-2),
.cycle 12 2 true (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 16 1 false (0),
.last 16 (4,true),
.cycle 18 1 false (-2),
.cycle 21 1 false (1),
.cycle 14 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 1 false (-1),
.cycle 29 1 false (-1),
.last 15 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part443_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part443) = true := by rfl

def kid04_part444 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 27 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 20 1 false (-2),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 27 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 20 1 false (0),
.last 16 (5,false),
.cycle 13 3 false (2),
.cycle 19 1 false (-1),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 20 1 false (-2),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 26 1 false (0),
.cycle 30 1 false (2),
.cycle 22 1 false (-2),
.last 16 (5,false)
])
theorem kid04_part444_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part444) = true := by rfl

def kid04_part445 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 13 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.last 13 (5,false),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 9 4 true (0),
.cycle 0 15 true (0),
.cycle 17 4 false (1),
.cycle 15 4 false (-1),
.last 13 (5,false)
])
theorem kid04_part445_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part445) = true := by rfl

def kid04_part446 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 9 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 12 5 false (0),
.cycle 17 1 true (1),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 9 8 true (-2),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 0 25 true (-2),
.cycle 0 17 true (-1),
.last 29 (4,true),
.cycle 17 9 false (2),
.cycle 12 7 false (0),
.cycle 20 1 true (-2)
])
theorem kid04_part446_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part446) = true := by rfl

def kid04_part447 : Audit := .cycle 1 12 true (1)
theorem kid04_part447_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part447) = true := by rfl

def kid04_part448 : Audit := .cycle 14 5 false (0)
theorem kid04_part448_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part448) = true := by rfl

def kid04_part449 : Audit := .split 13 (5,false) (byMove [
.cycle 9 12 true (0),
.cycle 7 23 false (3),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 1 14 true (1),
.cycle 16 7 false (0),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 48 1 false (8),
.last 24 (4,true),
.cycle 16 5 false (-1),
.cycle 29 16 true (0),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 1 14 true (1),
.last 15 (4,true),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 31 true (0)
])
theorem kid04_part449_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part449) = true := by rfl

def kid04_part450 : Audit := .cycle 0 13 true (0)
theorem kid04_part450_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part450) = true := by rfl

def kid04_part451 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 15 5 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 22 3 false (0),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 5 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 7 false (1),
.last 13 (5,false)
])
theorem kid04_part451_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part451) = true := by rfl

def kid04_part452 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 2 true (2),
.cycle 42 1 false (8),
.cycle 8 6 true (1),
.cycle 13 1 true (3),
.last 16 (4,true),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 11 7 true (1),
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 22 (4,true),
.cycle 13 1 true (3)
])
theorem kid04_part452_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part452) = true := by rfl

def kid04_part453 : Audit := .split 20 (4,true) (byMove [
.cycle 13 36 false (3),
.cycle 12 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 9 16 true (-2),
.cycle 15 6 true (-2),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 18 3 false (-1),
.cycle 15 6 false (0),
.cycle 9 20 true (-3),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 19 12 true (-2),
.cycle 9 12 false (2),
.cycle 0 41 true (-2),
.cycle 12 11 false (1),
.cycle 13 9 false (1),
.last 21 (5,false)
])
theorem kid04_part453_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part453) = true := by rfl

def kid04_part454 : Audit := .cycle 14 3 false (-1)
theorem kid04_part454_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part454) = true := by rfl

def kid04_part455 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 16 14 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 35 14 true (0),
.cycle 13 1 false (-1),
.cycle 23 14 true (0),
.cycle 26 14 true (-1),
.cycle 12 2 true (-1),
.cycle 14 14 true (-1),
.last 14 (4,true),
.cycle 16 14 true (-1),
.last 16 (4,true),
.cycle 32 14 true (-1),
.cycle 25 14 true (0),
.cycle 14 1 false (-2),
.cycle 43 14 true (0),
.cycle 13 1 false (-1),
.cycle 31 14 true (0),
.last 15 (4,true),
.cycle 27 14 true (0),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part455_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part455) = true := by rfl

def kid04_part456 : Audit := .cycle 19 1 false (-1)
theorem kid04_part456_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part456) = true := by rfl

def kid04_part457 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 false (2),
.cycle 34 4 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 15 4 false (1),
.cycle 14 4 false (0),
.last 14 (5,false),
.cycle 22 4 false (4),
.cycle 15 4 false (3),
.cycle 13 4 false (1),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 17 4 false (1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 17 4 false (-1),
.cycle 9 6 true (0),
.cycle 13 4 false (1),
.cycle 23 18 true (0),
.cycle 23 4 false (-1),
.cycle 11 2 true (0)
])
theorem kid04_part457_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part457) = true := by rfl

def kid04_part458 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 34 16 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 12 7 false (1),
.cycle 12 6 false (0),
.cycle 13 2 true (-1),
.cycle 14 14 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 12 9 false (1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 12 9 false (1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part458_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part458) = true := by rfl

def kid04_part459 : Audit := .cycle 1 12 true (1)
theorem kid04_part459_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part459) = true := by rfl

def kid04_part460 : Audit := .split 13 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.last 14 (5,false),
.cycle 20 3 false (0),
.cycle 16 5 false (-1),
.last 15 (5,false),
.cycle 29 1 false (1),
.cycle 14 6 false (0),
.last 17 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 15 8 false (1),
.last 14 (5,false)
])
theorem kid04_part460_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part460) = true := by rfl

def kid04_part461 : Audit := .cycle 10 2 true (1)
theorem kid04_part461_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part461) = true := by rfl

def kid04_part462 : Audit := .cycle 0 13 true (0)
theorem kid04_part462_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part462) = true := by rfl

def kid04_part463 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 21 6 false (1),
.last 17 (5,false),
.cycle 0 14 true (0),
.cycle 13 6 false (1),
.last 17 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 16 7 false (0),
.cycle 15 6 false (0),
.last 17 (5,false),
.cycle 1 14 true (1),
.cycle 13 6 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 10 false (2),
.last 13 (5,false)
])
theorem kid04_part463_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part463) = true := by rfl

def kid04_part464 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.last 15 (4,true),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 26 2 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 13 1 true (3),
.last 18 (4,true),
.last 15 (4,true),
.cycle 11 5 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 13 1 true (3)
])
theorem kid04_part464_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part464) = true := by rfl

def kid04_part440 : Audit := .split 11 (5,true) (byMove [(kid04_part441),(kid04_part442),(kid04_part443),(kid04_part444),(kid04_part445),(kid04_part446),(kid04_part447),(kid04_part448),(kid04_part449),(kid04_part450),(kid04_part451),(kid04_part452),(kid04_part453),(kid04_part454),(kid04_part455),(kid04_part456),(kid04_part457),(kid04_part458),(kid04_part459),(kid04_part460),(kid04_part461),(kid04_part462),(kid04_part463),(kid04_part464)])

theorem kid04_part440_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part440) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part441),(kid04_part442),(kid04_part443),(kid04_part444),(kid04_part445),(kid04_part446),(kid04_part447),(kid04_part448),(kid04_part449),(kid04_part450),(kid04_part451),(kid04_part452),(kid04_part453),(kid04_part454),(kid04_part455),(kid04_part456),(kid04_part457),(kid04_part458),(kid04_part459),(kid04_part460),(kid04_part461),(kid04_part462),(kid04_part463),(kid04_part464)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part441_checked

  · exact kid04_part447_checked

  · exact kid04_part453_checked

  · exact kid04_part459_checked

  · exact kid04_part442_checked

  · exact kid04_part448_checked

  · exact kid04_part454_checked

  · exact kid04_part460_checked

  · exact kid04_part443_checked

  · exact kid04_part449_checked

  · exact kid04_part455_checked

  · exact kid04_part461_checked

  · exact kid04_part444_checked

  · exact kid04_part450_checked

  · exact kid04_part456_checked

  · exact kid04_part462_checked

  · exact kid04_part445_checked

  · exact kid04_part451_checked

  · exact kid04_part457_checked

  · exact kid04_part463_checked

  · exact kid04_part446_checked

  · exact kid04_part452_checked

  · exact kid04_part458_checked

  · exact kid04_part464_checked

def kid04_part465 : Audit := .cycle 0 11 true (0)
theorem kid04_part465_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part465) = true := by rfl

def kid04_part466 : Audit := .cycle 1 10 true (1)
theorem kid04_part466_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part466) = true := by rfl

def kid04_part467 : Audit := .cycle 2 9 true (1)
theorem kid04_part467_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part467) = true := by rfl

def kid04_part468 : Audit := .cycle 1 13 true (1)
theorem kid04_part468_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part468) = true := by rfl

def kid04_part469 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 14 13 false (0),
.cycle 24 1 false (-2),
.cycle 9 7 true (0),
.cycle 14 6 false (0),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.last 28 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.cycle 9 7 true (0),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 21 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.last 20 (5,false),
.cycle 9 9 true (-1),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.cycle 9 7 true (0),
.cycle 0 18 true (0),
.last 27 (5,false),
.last 23 (5,false),
.last 23 (5,false),
.last 15 (5,false)
]),
.cycle 0 17 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 8 10 true (1),
.split 14 (5,false) (byMove [
.cycle 9 7 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 24 1 false (2),
.cycle 17 7 false (0),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.last 45 (5,true),
.cycle 0 16 true (0),
.cycle 8 9 true (1),
.last 15 (5,true),
.cycle 12 4 true (1),
.cycle 9 10 true (1),
.cycle 1 17 true (1),
.cycle 26 1 false (0),
.last 28 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 1 17 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.last 31 (5,true),
.last 15 (5,true)
]),
.cycle 20 3 false (0),
.cycle 16 5 false (0),
.cycle 13 2 true (0),
.cycle 21 1 false (1),
.cycle 13 6 false (1),
.split 14 (5,true) (byMove [
.cycle 9 7 false (3),
.last 21 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.last 21 (5,false),
.last 22 (5,false),
.last 24 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.last 26 (5,false),
.last 23 (5,false),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.last 21 (5,false),
.last 17 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 13 2 true (0),
.last 16 (5,false)
]),
.cycle 0 17 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 14 8 false (2),
.split 14 (5,false) (byMove [
.cycle 9 7 true (1),
.cycle 15 8 false (1),
.cycle 15 10 false (2),
.cycle 0 21 true (0),
.cycle 13 2 true (1),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 16 10 false (2),
.cycle 35 17 true (1),
.cycle 0 16 true (0),
.cycle 8 9 true (1),
.last 15 (5,true),
.cycle 18 9 false (0),
.cycle 15 8 false (1),
.last 17 (5,true),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 1 17 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.cycle 11 6 true (1),
.last 15 (5,true)
])
])
theorem kid04_part469_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part469) = true := by rfl

def kid04_part471 : Audit := .cycle 1 12 true (1)
theorem kid04_part471_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part471) = true := by rfl

def kid04_part472 : Audit := .split 13 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.cycle 24 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 20 3 false (0),
.cycle 16 5 false (0),
.last 15 (5,true),
.cycle 29 1 false (1),
.last 18 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 15 8 false (1),
.cycle 14 8 false (2)
])
theorem kid04_part472_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part472) = true := by rfl

def kid04_part473 : Audit := .cycle 10 2 true (2)
theorem kid04_part473_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part473) = true := by rfl

def kid04_part474 : Audit := .cycle 0 13 true (0)
theorem kid04_part474_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part474) = true := by rfl

def kid04_part475 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 21 6 false (1),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 18 8 false (1),
.cycle 16 7 false (0),
.cycle 15 6 false (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 10 false (2),
.cycle 11 2 true (2)
])
theorem kid04_part475_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part475) = true := by rfl

def kid04_part476 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 19 1 false (1),
.cycle 16 7 false (0),
.last 14 (4,true),
.cycle 12 2 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 11 2 true (2)
])
theorem kid04_part476_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part476) = true := by rfl

def kid04_part477 : Audit := .cycle 0 12 true (0)
theorem kid04_part477_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part477) = true := by rfl

def kid04_part478 : Audit := .cycle 1 11 true (1)
theorem kid04_part478_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part478) = true := by rfl

def kid04_part479 : Audit := .cycle 10 13 true (2)
theorem kid04_part479_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part479) = true := by rfl

def kid04_part480 : Audit := .cycle 3 9 true (1)
theorem kid04_part480_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part480) = true := by rfl

def kid04_part481 : Audit := .cycle 8 4 true (1)
theorem kid04_part481_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part481) = true := by rfl

def kid04_part482 : Audit := .cycle 11 1 true (3)
theorem kid04_part482_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part482) = true := by rfl

def kid04_part483 : Audit := .split 16 (4,true) (byMove [
.cycle 0 21 true (-1),
.cycle 23 8 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 8 false (0),
.cycle 15 4 false (1),
.cycle 0 20 true (0),
.cycle 17 8 false (3),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.last 20 (5,true),
.cycle 15 4 true (0),
.cycle 15 3 false (1),
.cycle 17 8 false (1),
.cycle 0 24 true (-1),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 15 4 false (1),
.cycle 0 20 true (0),
.cycle 9 8 true (0),
.cycle 0 19 true (0),
.cycle 20 8 false (2),
.cycle 17 8 false (1),
.cycle 19 8 false (1)
])
theorem kid04_part483_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part483) = true := by rfl

def kid04_part484 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 14 13 false (0),
.cycle 24 1 false (-2),
.cycle 9 7 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 17 (5,true),
.last 17 (5,true),
.cycle 20 3 false (0),
.cycle 16 5 false (0),
.last 15 (5,true),
.cycle 21 1 false (1),
.last 18 (5,true),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 15 8 false (1),
.cycle 14 8 false (2)
])
theorem kid04_part484_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part484) = true := by rfl

def kid04_part485 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.last 15 (4,true),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 20 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 17 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 0 17 true (0),
.last 18 (4,true),
.last 15 (4,true),
.cycle 12 2 true (2),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 13 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 11 3 true (2)
])
theorem kid04_part485_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part485) = true := by rfl

def kid04_part486 : Audit := .cycle 1 13 true (1)
theorem kid04_part486_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part486) = true := by rfl

def kid04_part487 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 true (1),
.cycle 21 6 false (1),
.cycle 20 1 false (0),
.cycle 36 1 false (2),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 17 8 false (3),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 8 6 true (1),
.last 13 (5,true),
.cycle 16 7 false (0),
.cycle 15 6 false (1),
.last 14 (5,true),
.cycle 5 8 true (1),
.last 18 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 2048, 5120, 128, 256, 8, 2, 1024, 1024, 4096],[2, 1024, 2048, 1, 1024, 4096, 2, 1024, 2048, 1, 1024, 4096, 4096],4128⟩,
.last 13 (5,true)
])
theorem kid04_part487_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part487) = true := by rfl

def kid04_part488 : Audit := .split 12 (5,true) (byMove [
.cycle 9 5 true (1),
.last 14 (4,true),
.cycle 20 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.last 16 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 32 1 false (6),
.cycle 16 7 false (0),
.last 14 (4,true),
.cycle 12 2 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (2)
])
theorem kid04_part488_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part488) = true := by rfl

def kid04_part489 : Audit := .cycle 0 12 true (0)
theorem kid04_part489_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part489) = true := by rfl

def kid04_part490 : Audit := .cycle 1 11 true (1)
theorem kid04_part490_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part490) = true := by rfl

def kid04_part491 : Audit := .cycle 2 10 true (1)
theorem kid04_part491_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part491) = true := by rfl

def kid04_part492 : Audit := .cycle 1 14 true (1)
theorem kid04_part492_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part492) = true := by rfl

def kid04_part493 : Audit := .split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 23 8 false (2),
.cycle 26 1 false (0),
.cycle 9 8 true (1),
.cycle 15 8 false (1),
.last 15 (5,true),
.cycle 0 18 true (0),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.cycle 3 22 true (1),
.last 18 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 394290, 133152, 1024, 128, 256, 32768, 2, 131104, 1024, 2, 4, 8, 1040, 2048, 16, 262144],[2, 1040, 2048, 1, 32, 262144, 8192, 1040, 2048, 4096, 131072, 262144, 2, 1040, 32, 1, 32, 262144, 262144],286732⟩,
.cycle 27 3 false (-1),
.cycle 17 8 false (2),
.last 16 (5,true),
.cycle 9 8 true (1),
.last 20 (5,true),
.last 15 (5,true),
.cycle 0 18 true (0),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 2048, 1024, 128, 256, 8, 2, 1024, 1024, 4096],[2, 1024, 2048, 1, 1024, 4096, 2, 1024, 2048, 1, 1024, 4096, 4096],4096⟩,
.cycle 11 6 true (2)
])
theorem kid04_part493_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part493) = true := by rfl

def kid04_part494 : Audit := .cycle 11 1 true (3)
theorem kid04_part494_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part494) = true := by rfl

def kid04_part470 : Audit := .split 11 (5,false) (byMove [(kid04_part471),(kid04_part472),(kid04_part473),(kid04_part474),(kid04_part475),(kid04_part476),(kid04_part477),(kid04_part478),(kid04_part479),(kid04_part480),(kid04_part481),(kid04_part482),(kid04_part483),(kid04_part484),(kid04_part485),(kid04_part486),(kid04_part487),(kid04_part488),(kid04_part489),(kid04_part490),(kid04_part491),(kid04_part492),(kid04_part493),(kid04_part494)])

theorem kid04_part470_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part470) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part471),(kid04_part472),(kid04_part473),(kid04_part474),(kid04_part475),(kid04_part476),(kid04_part477),(kid04_part478),(kid04_part479),(kid04_part480),(kid04_part481),(kid04_part482),(kid04_part483),(kid04_part484),(kid04_part485),(kid04_part486),(kid04_part487),(kid04_part488),(kid04_part489),(kid04_part490),(kid04_part491),(kid04_part492),(kid04_part493),(kid04_part494)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part471_checked

  · exact kid04_part477_checked

  · exact kid04_part483_checked

  · exact kid04_part489_checked

  · exact kid04_part472_checked

  · exact kid04_part478_checked

  · exact kid04_part484_checked

  · exact kid04_part490_checked

  · exact kid04_part473_checked

  · exact kid04_part479_checked

  · exact kid04_part485_checked

  · exact kid04_part491_checked

  · exact kid04_part474_checked

  · exact kid04_part480_checked

  · exact kid04_part486_checked

  · exact kid04_part492_checked

  · exact kid04_part475_checked

  · exact kid04_part481_checked

  · exact kid04_part487_checked

  · exact kid04_part493_checked

  · exact kid04_part476_checked

  · exact kid04_part482_checked

  · exact kid04_part488_checked

  · exact kid04_part494_checked

def kid04_part374 : Audit := .split 10 (2,true) (byMove [(kid04_part375),(kid04_part376),(kid04_part377),(kid04_part378),(kid04_part379),(kid04_part380),(kid04_part405),(kid04_part406),(kid04_part407),(kid04_part408),(kid04_part409),(kid04_part410),(kid04_part435),(kid04_part436),(kid04_part437),(kid04_part438),(kid04_part439),(kid04_part440),(kid04_part465),(kid04_part466),(kid04_part467),(kid04_part468),(kid04_part469),(kid04_part470)])

theorem kid04_part374_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (kid04_part374) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid04_part375),(kid04_part376),(kid04_part377),(kid04_part378),(kid04_part379),(kid04_part380),(kid04_part405),(kid04_part406),(kid04_part407),(kid04_part408),(kid04_part409),(kid04_part410),(kid04_part435),(kid04_part436),(kid04_part437),(kid04_part438),(kid04_part439),(kid04_part440),(kid04_part465),(kid04_part466),(kid04_part467),(kid04_part468),(kid04_part469),(kid04_part470)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part375_checked

  · exact kid04_part405_checked

  · exact kid04_part435_checked

  · exact kid04_part465_checked

  · exact kid04_part376_checked

  · exact kid04_part406_checked

  · exact kid04_part436_checked

  · exact kid04_part466_checked

  · exact kid04_part377_checked

  · exact kid04_part407_checked

  · exact kid04_part437_checked

  · exact kid04_part467_checked

  · exact kid04_part378_checked

  · exact kid04_part408_checked

  · exact kid04_part438_checked

  · exact kid04_part468_checked

  · exact kid04_part379_checked

  · exact kid04_part409_checked

  · exact kid04_part439_checked

  · exact kid04_part469_checked

  · exact kid04_part380_checked

  · exact kid04_part410_checked

  · exact kid04_part440_checked

  · exact kid04_part470_checked

def kid04_part495 : Audit := .cycle 0 11 true (0)
theorem kid04_part495_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,2⟩)) (kid04_part495) = true := by rfl

def kid04_part496 : Audit := .cycle 14 1 false (0)
theorem kid04_part496_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,3⟩)) (kid04_part496) = true := by rfl

def kid04_part498 : Audit := .split 13 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 11, 4, 64, 64],[2, 8, 4, 1, 4, 64, 64],96⟩,
.cycle 0 16 false (3),
.cycle 17 1 false (-1),
.cycle 0 36 true (-1),
.cycle 0 19 true (-1),
.split 14 (5,true) (byMove [
.cycle 0 19 true (-1),
.cycle 16 1 false (-2),
.last 16 (5,false),
.cycle 0 21 true (-1),
.cycle 0 16 false (3),
.last 16 (5,false),
.cycle 0 36 true (-1),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 16, 64, 64],[17, 16, 32, 17, 1, 17, 64],96⟩,
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 8 7 false (2),
.last 15 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (5,false),
.cycle 20 1 false (0),
.cycle 10 5 false (1),
.last 16 (5,false),
.cycle 0 41 true (-2),
.cycle 12 17 true (0),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.cycle 9 12 true (-1),
.last 15 (5,false)
]),
.cycle 0 41 true (-1),
.cycle 18 22 true (-1),
.cycle 70 1 false (0),
.cycle 0 15 true (-1),
.cycle 12 15 true (0),
.split 14 (5,true) (byMove [
.cycle 12 15 true (0),
.cycle 1 28 true (-1),
.cycle 2 13 false (3),
.proven (BB6.Agent11Raw39B0RBPumps.M56.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M56.never m hm),
.last 20 (5,false),
.last 15 (5,false),
.cycle 0 15 true (-1),
.last 41 (5,false),
.last 57 (5,false),
.cycle 3 13 false (3),
.cycle 0 24 true (-1),
.last 15 (5,false),
.cycle 0 41 true (-2),
.last 17 (5,false),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.cycle 9 12 true (-1),
.last 15 (5,false),
.cycle 12 15 true (0),
.cycle 1 14 true (-1),
.last 30 (5,false),
.cycle 5 30 true (-1),
.last 20 (5,false),
.last 15 (5,false)
]),
.cycle 9 7 false (1),
.cycle 38 1 false (-2),
.cycle 20 1 false (0),
.cycle 5 9 false (3),
.cycle 10 8 true (-1),
.split 14 (5,true) (byMove [
.cycle 11 8 true (-1),
.cycle 16 1 false (-2),
.last 16 (5,false),
.cycle 0 23 true (-1),
.cycle 38 1 false (-2),
.last 16 (5,false),
.cycle 6 9 false (3),
.cycle 9 7 false (1),
.last 16 (5,false),
.cycle 26 11 false (2),
.cycle 12 21 true (0),
.last 17 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (5,false),
.cycle 18 1 false (0),
.cycle 10 5 false (1),
.last 16 (5,false),
.cycle 19 28 true (-1),
.cycle 0 21 true (-1),
.cycle 13 2 true (0),
.cycle 0 49 true (-1),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 16, 64, 64],[17, 16, 32, 17, 1, 17, 64],96⟩,
.last 17 (5,false)
]),
.cycle 12 36 true (0),
.cycle 0 37 true (-2),
.cycle 12 13 true (0),
.cycle 0 15 true (-1),
.cycle 30 5 true (1),
.split 14 (5,true) (byMove [
.last 34 (5,false),
.cycle 25 1 false (1),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 0 37 true (-2),
.last 18 (5,false),
.cycle 0 15 true (-1),
.last 36 (5,false),
.cycle 0 31 true (-1),
.cycle 3 24 true (-1),
.cycle 12 7 true (0),
.last 15 (5,false),
.last 22 (5,false),
.cycle 0 21 true (-1),
.cycle 13 2 true (1),
.last 47 (5,false),
.last 19 (5,false),
.last 18 (5,false),
.cycle 12 15 true (0),
.cycle 12 14 true (0),
.cycle 12 13 true (0),
.cycle 16 18 true (0),
.last 20 (5,false),
.last 15 (5,false)
])
])
theorem kid04_part498_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part498) = true := by rfl

def kid04_part499 : Audit := .cycle 24 9 false (2)
theorem kid04_part499_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part499) = true := by rfl

def kid04_part500 : Audit := .cycle 12 1 false (0)
theorem kid04_part500_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part500) = true := by rfl

def kid04_part501 : Audit := .cycle 11 1 false (-1)
theorem kid04_part501_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part501) = true := by rfl

def kid04_part502 : Audit := .cycle 11 1 false (-1)
theorem kid04_part502_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part502) = true := by rfl

def kid04_part504 : Audit := .split 30 (5,true) (byMove [
.cycle 26 11 false (2),
.cycle 38 1 false (-2),
.cycle 32 1 false (-2),
.cycle 31 1 false (-3),
.cycle 31 1 false (-3),
.last 50 (2,true),
.last 53 (2,true),
.last 32 (2,true),
.cycle 35 1 false (1),
.cycle 31 1 false (-1),
.cycle 31 1 false (-1),
.last 34 (2,true),
.cycle 79 1 false (-7),
.last 32 (2,true),
.last 55 (2,true),
.cycle 31 1 false (-3),
.cycle 31 1 false (-3),
.last 34 (2,true),
.last 37 (2,true),
.last 32 (2,true),
.cycle 26 20 false (2),
.cycle 35 1 false (-1),
.cycle 26 14 false (2),
.last 34 (2,true)
])
theorem kid04_part504_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part504) = true := by rfl

def kid04_part505 : Audit := .cycle 19 1 false (-1)
theorem kid04_part505_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part505) = true := by rfl

def kid04_part506 : Audit := .cycle 13 1 false (-1)
theorem kid04_part506_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part506) = true := by rfl

def kid04_part507 : Audit := .cycle 12 1 false (-2)
theorem kid04_part507_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part507) = true := by rfl

def kid04_part508 : Audit := .cycle 12 1 false (-2)
theorem kid04_part508_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part508) = true := by rfl

def kid04_part509 : Audit := .cycle 11 1 false (-1)
theorem kid04_part509_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part509) = true := by rfl

def kid04_part510 : Audit := .split 18 (2,true) (byMove [
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 32771, 256, 1, 524288, 1048576, 32768, 2, 1048576, 4096, 128, 256, 8, 32768, 256, 1, 2147483648, 4294967296, 134217728, 2, 68719476736, 16777216, 2147483648, 4294967296, 8589934592, 32768, 68719476736, 1073741824, 2147483648, 4294967296, 8589934592, 84960903555, 84960903555, 1073741824, 68719476736],[2, 32768, 1048576, 1, 128, 68719476736, 8192, 1048576, 256, 4096, 68719476736, 68719476736, 2, 134217728, 4294967296, 1, 128, 68719476736, 33554432, 68719476736, 256, 16777216, 68719476736, 68719476736, 2147483648, 68719476736, 4294967296, 1073741824, 2147483648, 68719476736, 2147483648, 84960903555, 4294967296, 1073741824, 70866960384, 68719476736, 68719476736],137301327936⟩,
.cycle 0 22 true (-1),
.cycle 22 1 false (0),
.cycle 0 20 true (-1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 19 true (-1),
.last 30 (5,true),
.cycle 0 39 true (-1),
.cycle 3 16 true (-1),
.last 22 (5,true),
.cycle 0 20 true (-1),
.cycle 0 28 true (-1),
.cycle 13 6 true (-1),
.cycle 25 1 false (1),
.far false 5 ⟨0,[0, 1, 2, 3, 1, 1, 0, 4, 4, 4],[128, 256, 8, 1048704, 1327014347, 1, 524288, 1048576, 32768, 1327014347, 1048576, 4096, 128, 256, 512, 1327014347, 128, 64, 33554432, 67108864, 8, 128, 1140850688, 1, 33554432, 67108864, 134217728, 1327014347, 1327014347, 16777216, 1073741824],[2, 1327014347, 1048704, 1, 128, 1073741824, 8192, 1048576, 1327014347, 4096, 1074266112, 1073741824, 128, 8, 1327014347, 64, 128, 1073741824, 2, 1140850688, 128, 1, 1073741824, 1073741824, 33554432, 1327014347, 1327014347, 16777216, 1107296256, 1073741824, 1073741824],2135876434⟩,
.last 20 (5,true),
.last 19 (5,true),
.last 30 (5,true),
.last 29 (5,true),
.last 28 (5,true),
.last 34 (5,true),
.last 21 (5,true),
.cycle 0 20 true (-1)
])
theorem kid04_part510_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part510) = true := by rfl

def kid04_part511 : Audit := .split 13 (2,true) (byMove [
.cycle 25 1 false (3),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 26 1 false (2),
.cycle 0 19 true (-1),
.last 14 (5,true),
.cycle 0 41 true (-1),
.cycle 18 22 true (-1),
.cycle 23 1 false (1),
.cycle 0 15 true (-1),
.cycle 8 26 true (-1),
.last 14 (5,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.last 14 (5,true),
.last 26 (5,true),
.last 16 (5,true),
.last 24 (5,true),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part511_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part511) = true := by rfl

def kid04_part512 : Audit := .cycle 22 1 false (4)
theorem kid04_part512_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part512) = true := by rfl

def kid04_part513 : Audit := .cycle 12 1 false (0)
theorem kid04_part513_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part513) = true := by rfl

def kid04_part514 : Audit := .cycle 12 1 false (0)
theorem kid04_part514_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part514) = true := by rfl

def kid04_part515 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 17 1 true (1),
.cycle 22 1 false (4),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 15 1 true (1),
.cycle 15 1 true (3),
.cycle 24 1 true (0),
.last 15 (2,true),
.cycle 24 1 false (4),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 12 2 true (0),
.last 54 (2,true),
.cycle 16 1 true (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 15 5 true (0),
.cycle 15 1 true (3)
])
theorem kid04_part515_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part515) = true := by rfl

def kid04_part516 : Audit := .cycle 10 4 false (0)
theorem kid04_part516_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part516) = true := by rfl

def kid04_part517 : Audit := .split 13 (2,true) (byMove [
.cycle 28 13 false (2),
.cycle 15 1 false (-3),
.cycle 16 1 false (-2),
.cycle 24 1 false (-2),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 19 1 false (-3),
.cycle 21 1 false (-3),
.cycle 26 12 false (2),
.cycle 19 1 false (-1),
.cycle 8 6 false (2),
.last 17 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 25 1 false (1),
.cycle 21 1 false (1),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 17 (5,true),
.last 18 (5,true),
.last 30 (5,true),
.cycle 4 10 false (3),
.last 16 (5,true),
.cycle 10 6 false (0)
])
theorem kid04_part517_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part517) = true := by rfl

def kid04_part518 : Audit := .split 22 (2,true) (byMove [
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 0, 1, 524288, 1048576, 32768, 33554434, 1048576, 274878955776, 524288, 1048576, 134217728, 8589967360, 1048832, 16777216, 137438953472, 274877906944, 8589934592, 33554432, 281543712964608, 274877907200, 128, 256, 134217728, 325945119506816, 1048832, 16777216, 137438953472, 274877906944, 549755813888, 8589967360, 290271103287296, 68719476736, 137438953472, 274877906944, 35184372088832, 325945119506816, 325945119506816, 4672925466880, 137438953472, 274877906944, 549755813888, 325945119506816, 325945119506816, 68719476736, 281474976710656],[2, 0, 1048576, 1, 128, 281474976710656, 8192, 1048576, 256, 4096, 281474976710656, 281474976710656, 33554432, 8589934592, 274877906944, 16777216, 35192962056192, 281474976710656, 2147483648, 325945119506816, 1048832, 1073741824, 281474976710656, 281474976710656, 33554432, 8589967360, 274878955520, 16777216, 128, 281474976710656, 137438953472, 281612415664256, 274877906944, 68719476736, 35184372121600, 281474976710656, 8796093022208, 325945119506816, 274877906944, 4398046511104, 281612415664128, 281474976710656, 137438953472, 325945119506816, 274877906944, 68719476736, 35330401009664, 281474976710656, 281474976710656],562940504463424⟩,
.cycle 0 28 true (-2),
.cycle 26 1 false (0),
.cycle 37 1 false (-1),
.last 24 (5,true),
.last 23 (5,true),
.last 69 (5,true),
.last 34 (5,true),
.cycle 0 47 true (-2),
.cycle 3 20 true (-2),
.last 26 (5,true),
.cycle 0 26 true (-2),
.cycle 0 36 true (-2),
.cycle 15 8 true (-2),
.cycle 29 1 false (1),
.proven (BB6.Agent11Raw39B0RBCounter61.M61.table) (fun m hm => BB6.Agent11Raw39B0RBCounter61.M61.never m hm),
.last 24 (5,true),
.last 23 (5,true),
.last 34 (5,true),
.last 33 (5,true),
.last 32 (5,true),
.last 38 (5,true),
.last 25 (5,true),
.last 25 (5,true)
])
theorem kid04_part518_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part518) = true := by rfl

def kid04_part519 : Audit := .cycle 12 1 false (-2)
theorem kid04_part519_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part519) = true := by rfl

def kid04_part520 : Audit := .cycle 12 1 false (-2)
theorem kid04_part520_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part520) = true := by rfl

def kid04_part521 : Audit := .cycle 11 1 false (-1)
theorem kid04_part521_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part521) = true := by rfl

def kid04_part522 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 false (3),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 0 21 true (-2),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 16 23 true (0),
.last 42 (2,true),
.last 17 (2,true),
.last 20 (2,true),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 0 21 true (-2),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.last 20 (2,true),
.cycle 9 7 false (1),
.last 63 (2,true)
])
theorem kid04_part522_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part522) = true := by rfl

def kid04_part523 : Audit := .split 13 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 128, 8192, 16384, 512, 2, 16384, 8192, 33554432, 67108864, 2097152, 128, 1140850688, 33554432, 33554432, 67108864, 134217728, 2097152, 1140850688, 33554432, 33554432, 67108864, 134217728, 1258291200, 1140850688, 33554432, 1073741824],[2, 0, 16384, 1, 16384, 1073741824, 128, 2097152, 67109120, 64, 1140850688, 1073741824, 524288, 1207959552, 16384, 262144, 1073741824, 1073741824, 33554432, 1207959552, 67108864, 16777216, 67108864, 1073741824, 33554432, 1207959552, 67108864, 16777216, 1140850688, 1073741824, 1073741824],2145335360⟩,
.cycle 1 16 false (3),
.cycle 17 1 false (-1),
.last 29 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 27 (5,true),
.last 17 (5,true),
.last 48 (5,true),
.cycle 0 15 true (-1),
.last 26 (5,true),
.last 14 (5,true),
.cycle 9 7 false (1),
.last 34 (5,true),
.cycle 20 1 false (0),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true),
.last 26 (5,true),
.last 16 (5,true),
.last 24 (5,true),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part523_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part523) = true := by rfl

def kid04_part524 : Audit := .cycle 24 9 false (2)
theorem kid04_part524_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part524) = true := by rfl

def kid04_part525 : Audit := .cycle 16 1 false (0)
theorem kid04_part525_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part525) = true := by rfl

def kid04_part526 : Audit := .cycle 9 3 false (1)
theorem kid04_part526_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part526) = true := by rfl

def kid04_part527 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 25 1 false (-3),
.last 14 (2,true),
.cycle 18 1 true (0),
.cycle 16 1 false (-2),
.cycle 25 1 true (-3),
.cycle 0 48 true (-1),
.last 19 (2,true),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 15 1 true (1),
.cycle 15 1 true (3),
.cycle 9 7 false (1),
.last 24 (2,true),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 16 1 false (-2),
.cycle 14 3 false (0),
.last 33 (2,true),
.last 29 (2,true),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 9 13 false (2),
.cycle 15 1 true (3)
])
theorem kid04_part527_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part527) = true := by rfl

def kid04_part503 : Audit := .split 11 (5,false) (byMove [(kid04_part504),(kid04_part505),(kid04_part506),(kid04_part507),(kid04_part508),(kid04_part509),(kid04_part510),(kid04_part511),(kid04_part512),(kid04_part513),(kid04_part514),(kid04_part515),(kid04_part516),(kid04_part517),(kid04_part518),(kid04_part519),(kid04_part520),(kid04_part521),(kid04_part522),(kid04_part523),(kid04_part524),(kid04_part525),(kid04_part526),(kid04_part527)])

theorem kid04_part503_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part503) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part504),(kid04_part505),(kid04_part506),(kid04_part507),(kid04_part508),(kid04_part509),(kid04_part510),(kid04_part511),(kid04_part512),(kid04_part513),(kid04_part514),(kid04_part515),(kid04_part516),(kid04_part517),(kid04_part518),(kid04_part519),(kid04_part520),(kid04_part521),(kid04_part522),(kid04_part523),(kid04_part524),(kid04_part525),(kid04_part526),(kid04_part527)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part504_checked

  · exact kid04_part510_checked

  · exact kid04_part516_checked

  · exact kid04_part522_checked

  · exact kid04_part505_checked

  · exact kid04_part511_checked

  · exact kid04_part517_checked

  · exact kid04_part523_checked

  · exact kid04_part506_checked

  · exact kid04_part512_checked

  · exact kid04_part518_checked

  · exact kid04_part524_checked

  · exact kid04_part507_checked

  · exact kid04_part513_checked

  · exact kid04_part519_checked

  · exact kid04_part525_checked

  · exact kid04_part508_checked

  · exact kid04_part514_checked

  · exact kid04_part520_checked

  · exact kid04_part526_checked

  · exact kid04_part509_checked

  · exact kid04_part515_checked

  · exact kid04_part521_checked

  · exact kid04_part527_checked

def kid04_part528 : Audit := .cycle 13 1 false (1)
theorem kid04_part528_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part528) = true := by rfl

def kid04_part529 : Audit := .cycle 12 1 false (0)
theorem kid04_part529_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part529) = true := by rfl

def kid04_part530 : Audit := .split 11 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 11, 4, 64, 64],[2, 8, 4, 1, 4, 64, 64],96⟩,
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 17 1 false (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 14 (5,true),
.cycle 17 1 false (1),
.last 15 (5,true),
.cycle 19 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 23 1 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 14 (5,true)
]),
.cycle 20 1 false (4),
.cycle 13 1 false (1),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 13 1 false (3),
.last 13 (5,false),
.cycle 17 1 false (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (3),
.cycle 23 1 false (5),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 0 17 true (0),
.cycle 15 1 false (-1),
.cycle 22 1 false (4),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.split 12 (5,false) (byMove [
.last 16 (5,true),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 11 2 true (0),
.cycle 22 1 false (4),
.cycle 18 1 false (4),
.last 13 (5,true),
.cycle 26 1 false (4),
.last 15 (5,true),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 42 (5,true),
.cycle 0 17 true (0),
.last 14 (5,true),
.last 41 (5,true),
.cycle 0 35 true (0),
.last 13 (5,true)
]),
.cycle 0 30 true (0),
.cycle 15 1 false (3),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.split 12 (5,true) (byMove [
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 15 1 false (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 30 (5,false),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 8 5 true (0),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 11 2 true (1),
.cycle 22 1 false (4),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 14 16 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid04_part530_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part530) = true := by rfl

def kid04_part531 : Audit := .cycle 20 1 false (4)
theorem kid04_part531_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part531) = true := by rfl

def kid04_part532 : Audit := .cycle 13 1 false (3)
theorem kid04_part532_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part532) = true := by rfl

def kid04_part534 : Audit := .split 14 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 11, 256, 4096, 128, 256, 8, 2, 256, 4096, 4096],[2, 8, 256, 1, 32, 256, 2, 4096, 256, 1, 32, 256, 4096],6176⟩,
.last 17 (5,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 24 1 false (2),
.cycle 0 15 true (0),
.cycle 0 34 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.last 15 (5,false),
.cycle 0 20 true (0),
.last 17 (5,false),
.cycle 21 1 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 524290, 256, 1073741824, 33554432, 67108864, 2097152, 303360, 524290, 1073741824, 128, 256, 32768, 827394, 256, 1073741824, 128, 256, 32768, 8192, 256, 1073741824, 1073741824],[2, 0, 0, 1, 32, 256, 8192, 1073741824, 524290, 4096, 131072, 67109120, 524288, 32768, 303360, 262144, 8388608, 256, 8192, 256, 827394, 4096, 131072, 256, 8192, 1073741824, 8192, 4096, 131072, 256, 1073741824],1619134496⟩,
.cycle 0 17 true (0),
.cycle 11 8 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 16 18 true (1),
.cycle 0 18 true (0),
.last 15 (5,false)
])
theorem kid04_part534_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part534) = true := by rfl

def kid04_part535 : Audit := .cycle 0 15 true (0)
theorem kid04_part535_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part535) = true := by rfl

def kid04_part536 : Audit := .cycle 13 1 false (1)
theorem kid04_part536_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part536) = true := by rfl

def kid04_part537 : Audit := .cycle 12 1 false (0)
theorem kid04_part537_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part537) = true := by rfl

def kid04_part538 : Audit := .cycle 12 1 false (0)
theorem kid04_part538_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part538) = true := by rfl

def kid04_part539 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 17 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 true (1),
.cycle 12 4 true (-1),
.last 14 (2,true),
.cycle 0 21 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 17 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.cycle 17 1 true (-1)
])
theorem kid04_part539_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part539) = true := by rfl

def kid04_part540 : Audit := .cycle 20 1 false (4)
theorem kid04_part540_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part540) = true := by rfl

def kid04_part541 : Audit := .cycle 13 1 false (1)
theorem kid04_part541_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part541) = true := by rfl

def kid04_part542 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 13 1 false (3),
.last 13 (5,false),
.last 16 (5,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (3),
.cycle 23 1 false (5),
.cycle 17 1 false (5),
.last 13 (5,false)
])
theorem kid04_part542_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part542) = true := by rfl

def kid04_part543 : Audit := .cycle 0 13 true (0)
theorem kid04_part543_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part543) = true := by rfl

def kid04_part544 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 21 1 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 12 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 24 1 false (6),
.cycle 17 1 false (5),
.cycle 13 1 true (3)
])
theorem kid04_part544_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part544) = true := by rfl

def kid04_part545 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 21 1 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 13 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 24 1 false (6),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part545_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part545) = true := by rfl

def kid04_part546 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 24 1 false (4),
.cycle 17 1 false (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 18 1 false (4),
.cycle 20 1 true (2),
.cycle 12 4 true (0),
.last 17 (2,true),
.cycle 26 1 false (4),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 42 true (0),
.cycle 1 18 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 16 7 true (2),
.cycle 19 1 false (1)
])
theorem kid04_part546_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part546) = true := by rfl

def kid04_part547 : Audit := .split 13 (2,true) (byMove [
.cycle 25 1 false (3),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.last 18 (5,false),
.last 15 (5,false),
.cycle 11 3 false (1),
.cycle 0 41 true (0),
.cycle 18 22 true (0),
.cycle 23 1 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 10 4 true (0),
.cycle 11 3 false (1),
.cycle 0 36 true (0),
.last 16 (5,false),
.cycle 2 13 true (0),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false)
])
theorem kid04_part547_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part547) = true := by rfl

def kid04_part548 : Audit := .cycle 22 1 false (4)
theorem kid04_part548_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part548) = true := by rfl

def kid04_part549 : Audit := .cycle 12 1 false (0)
theorem kid04_part549_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part549) = true := by rfl

def kid04_part550 : Audit := .cycle 12 1 false (0)
theorem kid04_part550_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part550) = true := by rfl

def kid04_part551 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 13 (2,true),
.cycle 22 1 false (4),
.cycle 18 1 false (4),
.cycle 11 2 true (0),
.cycle 12 4 true (-1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 41 (2,true),
.cycle 1 18 true (0),
.last 13 (2,true),
.last 40 (2,true),
.cycle 13 6 true (1),
.cycle 11 3 false (1)
])
theorem kid04_part551_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part551) = true := by rfl

def kid04_part552 : Audit := .cycle 0 30 true (0)
theorem kid04_part552_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part552) = true := by rfl

def kid04_part553 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 22 1 false (4),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.cycle 12 4 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 1 17 true (0),
.cycle 14 1 true (2)
])
theorem kid04_part553_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part553) = true := by rfl

def kid04_part554 : Audit := .split 12 (2,true) (byMove [
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 20 1 false (2),
.cycle 0 13 true (0),
.cycle 36 1 false (4),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 8 5 true (0),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 24 1 false (4),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 14 16 true (1),
.last 29 (5,false),
.last 13 (5,false)
])
theorem kid04_part554_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part554) = true := by rfl

def kid04_part555 : Audit := .cycle 0 13 true (0)
theorem kid04_part555_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part555) = true := by rfl

def kid04_part556 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 14 3 true (1),
.cycle 15 3 true (1),
.cycle 0 14 true (0),
.cycle 10 17 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 19 3 true (3),
.cycle 13 1 true (3),
.cycle 12 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 18 1 false (2),
.cycle 9 5 true (0),
.cycle 16 3 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 25 3 true (3),
.cycle 33 3 true (5),
.cycle 14 3 true (3),
.cycle 13 1 true (3)
])
theorem kid04_part556_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part556) = true := by rfl

def kid04_part557 : Audit := .split 13 (5,false) (byMove [
.cycle 11 16 true (1),
.cycle 24 1 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 11 15 true (1),
.last 27 (2,true),
.cycle 3 11 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 22 1 false (2),
.last 18 (2,true),
.last 14 (2,true),
.cycle 11 19 true (1),
.cycle 12 3 true (2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 11 20 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part557_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part557) = true := by rfl

def kid04_part533 : Audit := .split 11 (5,true) (byMove [(kid04_part534),(kid04_part535),(kid04_part536),(kid04_part537),(kid04_part538),(kid04_part539),(kid04_part540),(kid04_part541),(kid04_part542),(kid04_part543),(kid04_part544),(kid04_part545),(kid04_part546),(kid04_part547),(kid04_part548),(kid04_part549),(kid04_part550),(kid04_part551),(kid04_part552),(kid04_part553),(kid04_part554),(kid04_part555),(kid04_part556),(kid04_part557)])

theorem kid04_part533_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part533) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part534),(kid04_part535),(kid04_part536),(kid04_part537),(kid04_part538),(kid04_part539),(kid04_part540),(kid04_part541),(kid04_part542),(kid04_part543),(kid04_part544),(kid04_part545),(kid04_part546),(kid04_part547),(kid04_part548),(kid04_part549),(kid04_part550),(kid04_part551),(kid04_part552),(kid04_part553),(kid04_part554),(kid04_part555),(kid04_part556),(kid04_part557)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part534_checked

  · exact kid04_part540_checked

  · exact kid04_part546_checked

  · exact kid04_part552_checked

  · exact kid04_part535_checked

  · exact kid04_part541_checked

  · exact kid04_part547_checked

  · exact kid04_part553_checked

  · exact kid04_part536_checked

  · exact kid04_part542_checked

  · exact kid04_part548_checked

  · exact kid04_part554_checked

  · exact kid04_part537_checked

  · exact kid04_part543_checked

  · exact kid04_part549_checked

  · exact kid04_part555_checked

  · exact kid04_part538_checked

  · exact kid04_part544_checked

  · exact kid04_part550_checked

  · exact kid04_part556_checked

  · exact kid04_part539_checked

  · exact kid04_part545_checked

  · exact kid04_part551_checked

  · exact kid04_part557_checked

def kid04_part558 : Audit := .cycle 10 3 false (0)
theorem kid04_part558_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part558) = true := by rfl

def kid04_part559 : Audit := .split 12 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 24 true (-1),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 33 1 false (-3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 0 24 true (-1),
.cycle 27 1 false (3),
.cycle 24 1 false (4),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.last 29 (5,false),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 18 1 false (-2),
.cycle 45 1 false (-3),
.cycle 26 11 false (2),
.cycle 18 1 false (0),
.cycle 9 5 false (1),
.last 14 (5,false)
]),
.cycle 6 7 false (3),
.cycle 9 5 false (1),
.cycle 24 1 false (0),
.cycle 24 9 false (2),
.cycle 54 1 false (-4),
.split 13 (5,true) (byMove [
.last 17 (5,false),
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.last 19 (5,false),
.cycle 9 5 false (1),
.last 14 (5,false),
.cycle 24 9 false (2),
.cycle 7 7 false (3),
.last 15 (5,false),
.cycle 0 15 true (-1),
.last 17 (5,false),
.last 15 (5,false),
.cycle 18 1 false (-2),
.last 19 (5,false),
.cycle 26 11 false (2),
.cycle 18 1 false (0),
.cycle 9 5 false (1),
.last 14 (5,false),
.last 54 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.cycle 0 15 true (-1),
.cycle 31 1 false (-3),
.last 15 (5,false)
]),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 11 8 true (-2),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.last 17 (5,false),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 9 7 false (1),
.cycle 10 5 false (0),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.cycle 16 1 false (-2),
.last 17 (5,false)
]),
.cycle 18 1 false (-2),
.cycle 16 1 false (-2),
.cycle 37 1 false (-3),
.cycle 28 1 false (-2),
.cycle 21 1 false (-3),
.split 13 (5,true) (byMove [
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 20 (5,false),
.cycle 16 1 false (-2),
.last 16 (5,false),
.cycle 28 1 false (-2),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 15 true (-1),
.last 17 (5,false),
.last 15 (5,false),
.cycle 9 7 false (1),
.last 18 (5,false),
.cycle 12 2 true (0),
.cycle 5 9 false (3),
.cycle 16 1 false (-2),
.last 16 (5,false),
.last 30 (5,false),
.last 20 (5,false),
.last 15 (5,false),
.cycle 0 15 true (-1),
.cycle 18 1 false (-2),
.last 15 (5,false)
])
])
theorem kid04_part559_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part559) = true := by rfl

def kid04_part560 : Audit := .cycle 15 1 false (1)
theorem kid04_part560_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part560) = true := by rfl

def kid04_part561 : Audit := .cycle 11 1 false (-1)
theorem kid04_part561_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part561) = true := by rfl

def kid04_part562 : Audit := .cycle 11 1 false (-1)
theorem kid04_part562_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part562) = true := by rfl

def kid04_part564 : Audit := .split 14 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 1, 4, 4],[128, 256, 8, 0, 0, 16384, 8192, 16384, 512, 1260389058, 16384, 67109120, 33554432, 67108864, 2097152, 128, 1140867328, 16384, 128, 256, 134217728, 2097152, 1140867328, 67108864, 33554432, 67108864, 134217728, 1260389056, 1140867328, 67125504, 1073741824],[2, 0, 16384, 1, 16384, 1073741824, 128, 2097152, 67109120, 64, 1140867328, 1073741824, 524288, 1210057216, 16384, 262144, 1073741824, 1073741824, 33554432, 1210057216, 67108864, 16777216, 16384, 1073741824, 33554432, 1210057216, 67125504, 16777216, 1140867328, 1073741824, 1073741824],2144942914⟩,
.cycle 10 6 false (0),
.cycle 18 1 false (-2),
.cycle 21 28 true (-1),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.last 18 (5,true),
.last 46 (5,true),
.last 30 (5,true),
.cycle 8 17 true (-2),
.last 15 (5,true),
.cycle 9 8 false (1),
.cycle 10 6 false (0),
.cycle 21 1 false (-1),
.cycle 5 10 false (3),
.last 16 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 17 (5,true),
.last 26 (5,true),
.last 29 (5,true),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid04_part564_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part564) = true := by rfl

def kid04_part565 : Audit := .cycle 8 10 false (2)
theorem kid04_part565_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part565) = true := by rfl

def kid04_part566 : Audit := .cycle 13 1 false (-1)
theorem kid04_part566_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part566) = true := by rfl

def kid04_part567 : Audit := .cycle 12 1 false (-2)
theorem kid04_part567_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part567) = true := by rfl

def kid04_part568 : Audit := .cycle 12 1 false (-2)
theorem kid04_part568_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part568) = true := by rfl

def kid04_part569 : Audit := .cycle 11 1 false (-1)
theorem kid04_part569_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part569) = true := by rfl

def kid04_part570 : Audit := .cycle 14 1 false (0)
theorem kid04_part570_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part570) = true := by rfl

def kid04_part571 : Audit := .cycle 13 1 false (-1)
theorem kid04_part571_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part571) = true := by rfl

def kid04_part572 : Audit := .split 12 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 4, 8192, 16384, 512, 2, 16384, 256, 33554432, 67108864, 2097152, 128, 1140850944, 1048576, 33554432, 67108864, 134217728, 2097152, 1140850944, 67108864, 33554432, 67108864, 134217728, 1260389056, 1140850944, 67108864, 1073741824],[2, 0, 16384, 1, 16384, 1073741824, 128, 2097152, 67109120, 64, 1140850944, 1073741824, 524288, 1207960064, 16384, 262144, 1073741824, 1073741824, 33554432, 1207960064, 67108864, 16777216, 67108864, 1073741824, 33554432, 1207960064, 67108864, 16777216, 1140850688, 1073741824, 1073741824],2145333312⟩,
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 24 1 false (4),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 22 1 false (4),
.cycle 19 1 false (3),
.last 13 (5,true),
.cycle 10 5 false (0),
.cycle 16 1 false (-2),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.last 53 (5,true),
.last 29 (5,true),
.last 24 (5,true),
.cycle 13 29 true (-1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid04_part572_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part572) = true := by rfl

def kid04_part573 : Audit := .cycle 15 1 false (1)
theorem kid04_part573_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part573) = true := by rfl

def kid04_part574 : Audit := .cycle 10 2 true (-1)
theorem kid04_part574_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part574) = true := by rfl

def kid04_part575 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 19 1 true (1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 13 (2,true),
.cycle 22 1 false (4),
.cycle 19 1 false (3),
.cycle 15 1 true (3),
.cycle 10 5 false (0),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.last 41 (2,true),
.last 18 (2,true),
.last 13 (2,true),
.last 40 (2,true),
.cycle 12 2 true (0),
.cycle 15 1 true (3)
])
theorem kid04_part575_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part575) = true := by rfl

def kid04_part576 : Audit := .cycle 10 4 false (0)
theorem kid04_part576_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part576) = true := by rfl

def kid04_part577 : Audit := .split 13 (2,true) (byMove [
.cycle 31 1 false (3),
.cycle 15 1 false (-3),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 6 8 false (3),
.cycle 9 6 false (1),
.cycle 27 1 false (-1),
.cycle 8 10 false (2),
.cycle 17 1 false (-3),
.last 14 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.last 26 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part577_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part577) = true := by rfl

def kid04_part578 : Audit := .cycle 16 1 false (0)
theorem kid04_part578_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part578) = true := by rfl

def kid04_part579 : Audit := .cycle 12 1 false (-2)
theorem kid04_part579_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part579) = true := by rfl

def kid04_part580 : Audit := .cycle 12 1 false (-2)
theorem kid04_part580_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part580) = true := by rfl

def kid04_part581 : Audit := .cycle 11 1 false (-1)
theorem kid04_part581_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part581) = true := by rfl

def kid04_part582 : Audit := .cycle 9 5 false (1)
theorem kid04_part582_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part582) = true := by rfl

def kid04_part583 : Audit := .cycle 10 3 false (0)
theorem kid04_part583_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part583) = true := by rfl

def kid04_part584 : Audit := .split 12 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 24 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 6 7 false (3),
.cycle 9 5 false (1),
.cycle 24 1 false (0),
.cycle 24 9 false (2),
.last 22 (5,true),
.last 13 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 24 (5,true),
.last 27 (5,true),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid04_part584_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part584) = true := by rfl

def kid04_part585 : Audit := .cycle 5 7 false (3)
theorem kid04_part585_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part585) = true := by rfl

def kid04_part586 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 9 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.cycle 14 8 true (0),
.cycle 10 6 false (0),
.last 15 (2,true),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (0),
.cycle 9 7 false (1),
.cycle 10 5 false (0),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 12 2 true (-1),
.cycle 14 6 true (0)
])
theorem kid04_part586_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part586) = true := by rfl

def kid04_part587 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 14 1 false (-2),
.last 13 (2,true),
.last 22 (2,true),
.cycle 10 3 false (0),
.cycle 32 1 true (-4),
.cycle 6 7 false (3),
.cycle 9 5 false (1),
.last 13 (2,true),
.cycle 24 9 false (2),
.cycle 10 13 true (-1),
.cycle 15 1 true (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 13 (2,true),
.cycle 16 1 false (0),
.cycle 10 3 false (0),
.cycle 11 3 false (0),
.last 45 (2,true),
.cycle 0 23 true (-2),
.last 13 (2,true),
.last 39 (2,true),
.cycle 12 2 true (0),
.cycle 15 1 true (3)
])
theorem kid04_part587_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part587) = true := by rfl

def kid04_part563 : Audit := .split 11 (5,false) (byMove [(kid04_part564),(kid04_part565),(kid04_part566),(kid04_part567),(kid04_part568),(kid04_part569),(kid04_part570),(kid04_part571),(kid04_part572),(kid04_part573),(kid04_part574),(kid04_part575),(kid04_part576),(kid04_part577),(kid04_part578),(kid04_part579),(kid04_part580),(kid04_part581),(kid04_part582),(kid04_part583),(kid04_part584),(kid04_part585),(kid04_part586),(kid04_part587)])

theorem kid04_part563_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part563) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part564),(kid04_part565),(kid04_part566),(kid04_part567),(kid04_part568),(kid04_part569),(kid04_part570),(kid04_part571),(kid04_part572),(kid04_part573),(kid04_part574),(kid04_part575),(kid04_part576),(kid04_part577),(kid04_part578),(kid04_part579),(kid04_part580),(kid04_part581),(kid04_part582),(kid04_part583),(kid04_part584),(kid04_part585),(kid04_part586),(kid04_part587)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part564_checked

  · exact kid04_part570_checked

  · exact kid04_part576_checked

  · exact kid04_part582_checked

  · exact kid04_part565_checked

  · exact kid04_part571_checked

  · exact kid04_part577_checked

  · exact kid04_part583_checked

  · exact kid04_part566_checked

  · exact kid04_part572_checked

  · exact kid04_part578_checked

  · exact kid04_part584_checked

  · exact kid04_part567_checked

  · exact kid04_part573_checked

  · exact kid04_part579_checked

  · exact kid04_part585_checked

  · exact kid04_part568_checked

  · exact kid04_part574_checked

  · exact kid04_part580_checked

  · exact kid04_part586_checked

  · exact kid04_part569_checked

  · exact kid04_part575_checked

  · exact kid04_part581_checked

  · exact kid04_part587_checked

def kid04_part588 : Audit := .split 33 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 4, 1, 1, 64, 64],96⟩,
.cycle 12 22 true (0),
.cycle 41 1 false (1),
.cycle 0 35 true (0),
.cycle 0 35 true (0),
.split 34 (5,true) (byMove [
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 41 1 false (1),
.cycle 45 1 false (3),
.cycle 13 22 true (0),
.last 35 (5,false),
.cycle 0 35 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 43 1 false (1),
.cycle 41 1 false (1),
.cycle 23 12 true (0),
.last 35 (5,false),
.cycle 0 38 true (0),
.cycle 39 1 false (-1),
.cycle 0 37 true (0),
.cycle 39 1 false (1),
.cycle 9 26 true (0),
.last 35 (5,false),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 17 18 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 13 22 true (0),
.last 35 (5,false)
]),
.cycle 0 34 true (0),
.cycle 16 18 true (0),
.cycle 0 54 true (0),
.cycle 18 16 true (0),
.cycle 8 26 true (0),
.split 34 (5,false) (byMove [
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 17 18 true (0),
.last 58 (5,true),
.cycle 13 22 true (0),
.last 36 (5,true),
.cycle 0 35 true (0),
.last 54 (5,true),
.last 56 (5,true),
.cycle 0 54 true (0),
.cycle 23 12 true (0),
.cycle 34 1 true (4),
.cycle 0 38 true (0),
.cycle 32 3 true (2),
.cycle 0 37 true (0),
.cycle 19 16 true (0),
.cycle 9 26 true (0),
.last 36 (5,true),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 17 18 true (0),
.last 58 (5,true),
.cycle 13 22 true (0),
.cycle 34 1 true (4)
]),
.cycle 6 28 true (0),
.cycle 28 6 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 1, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 1, 64, 64],96⟩,
.cycle 14 20 true (0),
.split 34 (5,true) (byMove [
.cycle 31 8 true (1),
.cycle 0 38 true (0),
.cycle 41 1 false (1),
.cycle 41 1 false (1),
.cycle 29 6 true (0),
.last 35 (5,false),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 7 28 true (0),
.last 36 (5,false),
.cycle 0 36 true (0),
.cycle 0 36 true (0),
.last 36 (5,false),
.cycle 0 41 true (0),
.cycle 39 1 false (-1),
.far false 4 ⟨0,[0, 1, 2, 1, 1, 3, 2, 1],[128, 256, 8, 0, 0, 16777216, 128, 256, 32768, 1089730, 8192, 16777216, 524288, 1048576, 512, 1089728, 1048576, 16777216, 128, 256, 32768, 8192, 8192, 16777216, 16777216],[2, 0, 16777216, 1, 64, 1, 8192, 32896, 17866946, 4096, 64, 17871040, 128, 1048576, 16777216, 64, 262144, 64, 8192, 128, 8192, 4096, 64, 16777216, 16777216],25298976⟩,
.cycle 39 1 false (1),
.cycle 25 10 true (0),
.last 35 (5,false),
.cycle 15 20 true (0),
.cycle 0 37 true (0),
.cycle 33 2 true (2),
.cycle 0 36 true (0),
.cycle 0 36 true (0),
.last 36 (5,false)
]),
.cycle 0 34 true (0),
.cycle 1 33 true (0),
.cycle 2 32 true (0),
.cycle 0 57 true (0),
.cycle 13 21 true (0),
.split 34 (5,false) (byMove [
.cycle 15 20 true (0),
.cycle 0 37 true (0),
.cycle 33 2 true (3),
.cycle 0 36 true (0),
.cycle 0 36 true (0),
.last 35 (5,true),
.cycle 0 35 true (0),
.cycle 16 19 true (0),
.cycle 0 53 true (0),
.cycle 3 32 true (0),
.cycle 8 27 true (0),
.cycle 34 1 true (4),
.cycle 11 24 true (0),
.cycle 0 40 true (0),
.last 36 (5,true),
.last 56 (5,true),
.cycle 14 21 true (0),
.last 35 (5,true),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 2 33 true (0),
.last 57 (5,true),
.cycle 13 22 true (0),
.cycle 34 1 true (4)
])
])
theorem kid04_part588_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part588) = true := by rfl

def kid04_part589 : Audit := .split 14 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 4, 1, 2, 64, 64],96⟩,
.cycle 1 16 true (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.split 15 (5,true) (byMove [
.cycle 24 1 false (2),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 8 8 true (0),
.last 16 (5,false),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 25 1 false (3),
.cycle 1 18 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 1 19 true (0),
.last 16 (5,false)
]),
.cycle 0 15 true (0),
.cycle 1 34 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.last 35 (5,true),
.cycle 1 19 true (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.last 32 (5,true),
.last 33 (5,true),
.cycle 0 31 true (0),
.last 24 (5,true),
.cycle 15 1 true (3),
.cycle 1 18 true (0),
.cycle 13 3 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (0),
.cycle 9 7 true (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 30 (5,true),
.last 36 (5,true),
.cycle 1 19 true (0),
.cycle 15 1 true (3)
]),
.cycle 1 20 true (0),
.cycle 11 4 true (0),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 2, 64, 64],96⟩,
.cycle 1 17 true (0),
.split 15 (5,true) (byMove [
.cycle 13 8 true (0),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 1 19 true (0),
.cycle 12 4 true (0),
.last 17 (5,false),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 1 20 true (0),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 17 (5,false),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 19 1 false (1),
.cycle 10 6 true (0),
.last 17 (5,false),
.cycle 1 38 true (0),
.cycle 1 17 true (0),
.cycle 14 2 true (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 17 (5,false)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 16 18 true (1),
.cycle 1 18 true (0),
.split 15 (5,false) (byMove [
.last 32 (5,true),
.cycle 1 17 true (0),
.cycle 14 2 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.last 31 (5,true),
.last 48 (5,true),
.cycle 3 13 true (0),
.cycle 8 8 true (0),
.cycle 15 1 true (3),
.cycle 1 21 true (0),
.cycle 11 5 true (0),
.last 17 (5,true),
.last 34 (5,true),
.cycle 1 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.last 35 (5,true),
.cycle 1 19 true (0),
.cycle 15 1 true (3)
])
])
theorem kid04_part589_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part589) = true := by rfl

def kid04_part590 : Audit := .split 11 (2,true) (byMove [
.cycle 23 1 false (3),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 22 1 false (2),
.cycle 0 15 true (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 22 1 false (0),
.cycle 11 3 false (1),
.cycle 24 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 2 14 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false)
]),
.cycle 0 35 true (0),
.cycle 15 18 true (0),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 8 18 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.last 35 (5,false),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 35 (5,false),
.last 13 (5,false),
.cycle 2 14 true (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 26 (5,false),
.cycle 5 26 true (0),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 10 2 true (0),
.split 12 (5,true) (byMove [
.cycle 11 8 true (-1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 22 1 false (4),
.cycle 23 1 false (3),
.last 15 (5,false),
.cycle 28 13 false (2),
.cycle 11 3 false (1),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 17 24 true (0),
.cycle 0 17 true (0),
.cycle 11 2 true (0),
.cycle 0 43 true (0),
.cycle 2 15 true (0),
.last 15 (5,false)
]),
.cycle 0 30 true (0),
.cycle 2 12 true (0),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 2 11 true (0),
.split 12 (5,true) (byMove [
.last 30 (5,false),
.cycle 21 1 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 2 12 true (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.last 30 (5,false),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.last 13 (5,false),
.last 18 (5,false),
.cycle 0 17 true (0),
.cycle 11 2 true (1),
.last 41 (5,false),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 14 16 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid04_part590_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part590) = true := by rfl

def kid04_part591 : Audit := .split 34 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 4, 1, 8, 64, 64],96⟩,
.cycle 7 28 true (0),
.cycle 43 1 false (1),
.cycle 0 36 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 8, 64, 64],96⟩,
.split 35 (5,true) (byMove [
.cycle 0 36 true (0),
.cycle 5 42 true (0),
.cycle 43 1 false (1),
.cycle 41 1 false (1),
.cycle 8 28 true (0),
.last 36 (5,false),
.cycle 0 36 true (0),
.far true 1 ⟨0,[0, 0],[16, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 16, 16, 64],96⟩,
.cycle 45 1 false (1),
.cycle 43 1 false (1),
.cycle 20 16 true (0),
.last 36 (5,false),
.far true 1 ⟨0,[0, 0],[16, 17, 24, 8, 16, 64, 64],[16, 16, 32, 16, 16, 1, 64],96⟩,
.cycle 43 1 false (-1),
.cycle 0 38 true (0),
.cycle 41 1 false (1),
.cycle 5 34 true (0),
.last 36 (5,false),
.cycle 0 36 true (0),
.cycle 1 35 true (0),
.cycle 14 22 true (0),
.far true 1 ⟨0,[0, 0],[16, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 16, 16, 64],96⟩,
.cycle 0 39 true (0),
.last 36 (5,false)
]),
.cycle 0 35 true (0),
.cycle 5 41 true (0),
.cycle 0 59 true (0),
.cycle 15 20 true (0),
.cycle 8 27 true (0),
.split 35 (5,false) (byMove [
.cycle 0 36 true (0),
.cycle 1 35 true (0),
.cycle 14 22 true (0),
.last 63 (5,true),
.cycle 0 39 true (0),
.last 37 (5,true),
.cycle 0 36 true (0),
.cycle 13 23 true (0),
.last 61 (5,true),
.cycle 0 59 true (0),
.cycle 5 35 true (0),
.cycle 35 1 true (5),
.cycle 11 29 true (0),
.cycle 33 3 true (3),
.cycle 0 38 true (0),
.cycle 16 20 true (0),
.cycle 9 27 true (0),
.last 37 (5,true),
.cycle 0 36 true (0),
.cycle 1 35 true (0),
.cycle 5 41 true (0),
.last 62 (5,true),
.cycle 0 39 true (0),
.cycle 35 1 true (5)
]),
.cycle 5 36 true (0),
.cycle 27 8 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 8, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 8, 64, 64],96⟩,
.cycle 0 37 true (0),
.split 35 (5,true) (byMove [
.cycle 32 8 true (2),
.cycle 0 39 true (0),
.cycle 43 1 false (1),
.cycle 41 1 false (1),
.cycle 28 8 true (0),
.last 36 (5,false),
.far true 1 ⟨0,[0, 0],[16, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 16, 16, 64],96⟩,
.cycle 5 36 true (0),
.last 37 (5,false),
.cycle 0 37 true (0),
.cycle 5 62 true (0),
.last 37 (5,false),
.cycle 5 42 true (0),
.cycle 43 1 false (-1),
.far false 7 ⟨0,[0, 5, 3, 1, 2, 4, 6, 4, 2, 4, 3, 1, 3, 5],[2147483648, 4294967296, 8, 0, 0, 4398046511104, 128, 256, 2097152, 137438953472, 262144, 4398046511104, 33554432, 67108864, 32768, 4610750722306, 4610750722306, 4398046511104, 33554432, 67108864, 549755813888, 4294967296, 137438953474, 4398046511104, 33554432, 67108864, 32768, 532480, 4096, 4398046511104, 128, 256, 2097152, 137438953474, 262144, 4398046511104, 2147483648, 4294967296, 2097152, 137438953474, 4294967296, 4398046511104, 4398046511104],[2, 0, 4398046511104, 1, 8589934592, 1, 524288, 137438953472, 4535485464578, 262144, 512, 4402341478400, 8192, 4610750722306, 4398046511104, 4096, 134217728, 4096, 137438953472, 35651584, 4398046511104, 68719476736, 134217728, 68719476736, 8192, 532480, 4610750722306, 4096, 134217728, 4610750722306, 524288, 137438953474, 137438953474, 262144, 512, 4398046511104, 524288, 4294967296, 4398046511104, 262144, 8589934592, 262144, 4398046511104],6649675775008⟩,
.cycle 41 1 false (1),
.cycle 22 14 true (0),
.last 36 (5,false),
.cycle 5 43 true (0),
.far true 1 ⟨0,[0, 0],[16, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 16, 16, 64],96⟩,
.cycle 34 2 true (3),
.cycle 0 37 true (0),
.cycle 11 27 true (0),
.last 37 (5,false)
]),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 2 33 true (0),
.cycle 11 25 true (0),
.cycle 0 38 true (0),
.split 35 (5,false) (byMove [
.cycle 5 43 true (0),
.last 65 (5,true),
.cycle 34 2 true (4),
.cycle 0 37 true (0),
.cycle 11 27 true (0),
.last 36 (5,true),
.cycle 0 36 true (0),
.cycle 5 42 true (0),
.cycle 25 15 true (0),
.cycle 3 33 true (0),
.cycle 8 28 true (0),
.cycle 35 1 true (5),
.cycle 0 41 true (0),
.cycle 16 22 true (0),
.last 37 (5,true),
.cycle 11 25 true (0),
.cycle 0 38 true (0),
.last 36 (5,true),
.cycle 0 36 true (0),
.cycle 1 35 true (0),
.cycle 2 34 true (0),
.cycle 11 26 true (0),
.cycle 0 39 true (0),
.cycle 35 1 true (5)
])
])
theorem kid04_part591_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part591) = true := by rfl

def kid04_part592 : Audit := .cycle 11 3 true (1)
theorem kid04_part592_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part592) = true := by rfl

def kid04_part594 : Audit := .split 14 (2,true) (byMove [
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 8 7 true (0),
.last 15 (5,false),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 26 1 false (4),
.cycle 24 1 false (4),
.cycle 25 1 false (3),
.cycle 11 8 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 16 18 true (1),
.last 35 (5,false),
.last 15 (5,false)
])
theorem kid04_part594_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part594) = true := by rfl

def kid04_part595 : Audit := .cycle 13 1 false (-1)
theorem kid04_part595_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part595) = true := by rfl

def kid04_part596 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.last 16 (5,false),
.cycle 42 1 false (4),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.last 16 (5,false),
.cycle 16 1 false (-2),
.last 18 (5,false),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.last 16 (5,false),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid04_part596_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part596) = true := by rfl

def kid04_part597 : Audit := .split 16 (5,false) (byMove [
.cycle 25 1 false (3),
.cycle 18 1 false (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 15 2 true (1),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 0 39 true (0),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 8 9 true (0),
.cycle 16 1 true (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 17 (2,true),
.cycle 26 1 false (4),
.cycle 0 20 true (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 18 20 true (1),
.cycle 0 21 true (0),
.cycle 16 1 true (2)
])
theorem kid04_part597_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part597) = true := by rfl

def kid04_part598 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 0 20 true (0),
.cycle 12 2 true (0),
.cycle 15 1 false (-1),
.last 40 (2,true),
.last 41 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 8 true (0),
.cycle 19 1 true (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 0 36 true (0),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 5 true (2),
.cycle 16 1 true (2)
])
theorem kid04_part598_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part598) = true := by rfl

def kid04_part599 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 17 1 true (1),
.cycle 20 1 false (-2),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.last 18 (2,true),
.cycle 9 5 false (1),
.cycle 20 1 true (-2)
])
theorem kid04_part599_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part599) = true := by rfl

def kid04_part600 : Audit := .split 34 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 295170, 256, 16777216, 128, 256, 32768, 524290, 4096, 16777216, 128, 256, 2097152, 33024, 524288, 16777216, 128, 256, 8, 262400, 256, 16777216, 16777216],[2, 32768, 256, 1, 2048, 1, 8192, 16777216, 256, 4096, 2048, 4096, 524288, 128, 256, 262144, 2048, 262144, 2, 256, 256, 1, 2048, 1, 16777216],25298976⟩,
.cycle 7 28 true (0),
.cycle 43 1 false (1),
.cycle 0 36 true (0),
.last 36 (5,false),
.cycle 0 36 true (0),
.cycle 0 35 true (0),
.cycle 6 41 true (0),
.cycle 0 59 true (0),
.cycle 15 20 true (0),
.cycle 8 27 true (0),
.last 35 (5,false),
.cycle 6 36 true (0),
.cycle 27 8 true (0),
.far false 7 ⟨0,[0, 5, 3, 1, 2, 4, 6, 4, 2, 4, 3, 1, 3, 5],[2147483648, 4294967296, 8, 0, 0, 4398046511104, 128, 256, 2097152, 137438953472, 262144, 4398046511104, 33554432, 67108864, 32768, 4610750722306, 4610750722306, 4398046511104, 33554432, 67108864, 549755813888, 4294967296, 137438953474, 4398046511104, 33554432, 67108864, 32768, 532480, 4096, 4398046511104, 128, 256, 2097152, 137438953474, 262144, 4398046511104, 2147483648, 4294967296, 2097152, 137438953474, 4294967296, 4398046511104, 4398046511104],[2, 0, 1, 1, 34359738368, 1, 524288, 4398046511104, 141733920770, 262144, 2048, 262144, 8192, 4610750722306, 4096, 4096, 536870912, 4096, 137438953472, 35651584, 68719476736, 68719476736, 536870912, 68719476736, 8192, 4398046511104, 4610750722306, 4096, 536870912, 4096, 524288, 4398046511104, 137438953474, 262144, 2048, 262144, 524288, 4294967296, 262144, 262144, 34359738368, 262144, 4398046511104],6649675775008⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 524290, 4096, 1073741824, 33554432, 67108864, 2097152, 256, 524290, 1073741824, 128, 256, 32768, 524290, 256, 1073741824, 33554432, 67108864, 134217728, 1326227842, 1326227842, 1073741824, 1073741824],[2, 0, 0, 1, 2048, 1, 8192, 1073741824, 524290, 4096, 2048, 4096, 524288, 33587200, 256, 262144, 536870912, 262144, 8192, 256, 524290, 4096, 2048, 4096, 33554432, 1326227842, 1326227842, 16777216, 536870912, 16777216, 1073741824],2139241504⟩,
.cycle 0 37 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 524290, 4096, 1073741824, 33554432, 67108864, 2097152, 256, 524290, 1073741824, 128, 256, 32768, 524290, 256, 1073741824, 33554432, 67108864, 134217728, 1326227842, 1326227842, 1073741824, 1073741824],[2, 0, 1073741824, 1, 2048, 1, 8192, 1073741824, 524290, 4096, 2048, 4096, 524288, 33587200, 1073741824, 262144, 536870912, 262144, 8192, 256, 1073741824, 4096, 2048, 4096, 33554432, 1326227842, 1107304448, 16777216, 536870912, 16777216, 1073741824],2139241504⟩,
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 2 33 true (0),
.cycle 12 25 true (0),
.cycle 0 38 true (0),
.last 35 (5,false)
])
theorem kid04_part600_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part600) = true := by rfl

def kid04_part601 : Audit := .split 33 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32771, 256, 262144, 128, 256, 32768, 2, 8192, 262144, 128, 256, 8, 32768, 256, 262144, 262144],[2, 32768, 256, 1, 2048, 2, 8192, 262144, 256, 4096, 2048, 8192, 2, 256, 256, 1, 2048, 2, 262144],395296⟩,
.cycle 12 22 true (0),
.cycle 41 1 false (1),
.cycle 0 35 true (0),
.last 35 (5,false),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32771, 256, 262144, 128, 256, 32768, 2, 8192, 262144, 128, 256, 8, 32768, 256, 262144, 262144],[2, 32768, 262144, 1, 2048, 2, 8192, 262144, 256, 4096, 2048, 8192, 2, 256, 262144, 1, 2048, 2, 262144],395296⟩,
.cycle 0 34 true (0),
.cycle 16 18 true (0),
.cycle 0 54 true (0),
.cycle 18 16 true (0),
.cycle 8 26 true (0),
.last 34 (5,false),
.cycle 6 28 true (0),
.cycle 28 6 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 524290, 8192, 1073741824, 33554432, 67108864, 2097152, 67149824, 67108864, 1073741824, 128, 256, 32768, 67379200, 8192, 1073741824, 128, 256, 32768, 8192, 8192, 1073741824, 1073741824],[2, 0, 1, 1, 2048, 2, 8192, 1073741824, 67936258, 4096, 2048, 8192, 524288, 67108864, 262144, 262144, 536870912, 524288, 8192, 32768, 4096, 4096, 2048, 8192, 8192, 1073741824, 8192, 4096, 2048, 8192, 1073741824],1619134496⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 524290, 8192, 1073741824, 33554432, 67108864, 2097152, 67149824, 67108864, 1073741824, 128, 256, 32768, 67379200, 8192, 1073741824, 128, 256, 32768, 8192, 8192, 1073741824, 1073741824],[2, 0, 0, 1, 2048, 2, 8192, 1073741824, 524290, 4096, 2048, 8192, 524288, 67108864, 67149824, 262144, 536870912, 524288, 8192, 32768, 67379200, 4096, 2048, 8192, 8192, 1073741824, 8192, 4096, 2048, 8192, 1073741824],1619134496⟩,
.cycle 14 20 true (0),
.cycle 7 28 true (0),
.cycle 0 34 true (0),
.cycle 1 33 true (0),
.cycle 2 32 true (0),
.cycle 0 57 true (0),
.cycle 13 21 true (0),
.last 34 (5,false)
])
theorem kid04_part601_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part601) = true := by rfl

def kid04_part602 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 23 1 false (3),
.cycle 23 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 7 41 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 24 true (0),
.cycle 5 26 true (0),
.last 30 (5,false),
.last 13 (5,false)
])
theorem kid04_part602_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part602) = true := by rfl

def kid04_part603 : Audit := .cycle 0 13 true (0)
theorem kid04_part603_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part603) = true := by rfl

def kid04_part604 : Audit := .split 13 (5,false) (byMove [
.cycle 10 18 true (0),
.cycle 8 10 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.cycle 8 14 true (0),
.cycle 0 14 true (0),
.cycle 8 20 true (0),
.cycle 8 26 true (0),
.cycle 8 18 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 6 8 true (0),
.cycle 8 16 true (0),
.last 14 (2,true),
.cycle 8 26 true (0),
.cycle 8 8 true (0),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 10 20 true (0),
.cycle 8 9 true (0),
.cycle 13 1 true (3)
])
theorem kid04_part604_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part604) = true := by rfl

def kid04_part605 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 11, 32, 8, 128, 256, 8, 2, 32, 395, 4096],[2, 8, 4096, 1, 2048, 32, 2, 395, 4096, 1, 2048, 32, 4096],4096⟩,
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 6 true (0),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 32, 2, 64],[2, 2, 64, 1, 32, 32, 64],64⟩,
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 13 1 true (3),
.cycle 6 12 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 19 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 262402, 32, 256, 128, 256, 32768, 2, 131072, 256, 2, 4, 8, 256, 32, 4, 262144],[2, 256, 262144, 1, 2048, 32, 8192, 256, 262144, 4096, 2048, 131072, 2, 4, 262144, 1, 32, 32, 262144],418828⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 11, 32, 8, 64],[2, 8, 64, 1, 32, 32, 64],64⟩,
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part605_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part605) = true := by rfl

def kid04_part606 : Audit := .cycle 14 1 false (0)
theorem kid04_part606_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part606) = true := by rfl

def kid04_part607 : Audit := .cycle 13 1 false (-1)
theorem kid04_part607_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part607) = true := by rfl

def kid04_part608 : Audit := .split 12 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 11, 256, 4096, 128, 256, 8, 2, 256, 4096, 4096],[2, 8, 256, 1, 2048, 1, 2, 4096, 256, 1, 2048, 256, 4096],6176⟩,
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 22 1 false (4),
.last 17 (5,false),
.cycle 24 1 false (4),
.last 16 (5,false),
.cycle 16 1 false (-2),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 42 true (0),
.last 15 (5,false),
.cycle 2 13 true (0),
.cycle 13 29 true (0),
.last 17 (5,false),
.cycle 11 2 true (0)
])
theorem kid04_part608_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part608) = true := by rfl

def kid04_part609 : Audit := .cycle 15 1 false (1)
theorem kid04_part609_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part609) = true := by rfl

def kid04_part610 : Audit := .cycle 10 2 true (0)
theorem kid04_part610_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part610) = true := by rfl

def kid04_part611 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.cycle 12 2 true (-1),
.cycle 20 1 false (-2),
.last 15 (2,true),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 9 7 false (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 128, 128, 128, 256, 32768, 2, 128, 128, 128, 256, 8, 256, 128, 128, 262144],[2, 256, 262144, 1, 2048, 128, 8192, 128, 262144, 4096, 2048, 128, 2, 256, 262144, 1, 2048, 128, 262144],278540⟩,
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 11 5 false (1),
.cycle 11 3 false (1)
])
theorem kid04_part611_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part611) = true := by rfl

def kid04_part612 : Audit := .cycle 0 30 true (0)
theorem kid04_part612_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part612) = true := by rfl

def kid04_part613 : Audit := .split 14 (5,false) (byMove [
.last 33 (2,true),
.cycle 19 1 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 1 33 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.cycle 14 1 true (2),
.cycle 1 19 true (0),
.cycle 19 1 false (-1),
.last 15 (2,true),
.last 46 (2,true),
.cycle 1 16 true (0),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 16 18 true (1),
.cycle 1 17 true (0),
.cycle 14 1 true (2)
])
theorem kid04_part613_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part613) = true := by rfl

def kid04_part614 : Audit := .split 12 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 11, 256, 4096, 128, 256, 8, 2, 256, 4096, 4096],[2, 8, 256, 1, 2048, 256, 2, 4096, 256, 1, 2048, 256, 4096],6176⟩,
.last 15 (5,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 2 12 true (0),
.cycle 0 13 true (0),
.cycle 2 28 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.last 13 (5,false),
.cycle 2 16 true (0),
.last 15 (5,false),
.cycle 19 1 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 524290, 256, 1073741824, 33554432, 67108864, 2097152, 303360, 524290, 1073741824, 128, 256, 32768, 827394, 256, 1073741824, 128, 256, 32768, 8192, 256, 1073741824, 1073741824],[2, 0, 0, 1, 2048, 256, 8192, 1073741824, 524290, 4096, 2048, 256, 524288, 32768, 303360, 262144, 536870912, 67108864, 8192, 256, 827394, 4096, 2048, 256, 8192, 1073741824, 8192, 4096, 2048, 256, 1073741824],1619134496⟩,
.cycle 2 13 true (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 14 16 true (1),
.cycle 2 14 true (0),
.last 13 (5,false)
])
theorem kid04_part614_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part614) = true := by rfl

def kid04_part615 : Audit := .cycle 0 13 true (0)
theorem kid04_part615_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part615) = true := by rfl

def kid04_part616 : Audit := .split 13 (5,false) (byMove [
.cycle 27 3 true (3),
.cycle 21 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.cycle 14 3 true (2),
.cycle 0 14 true (0),
.cycle 26 3 true (4),
.last 27 (2,true),
.cycle 3 11 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 16 3 true (1),
.cycle 21 1 false (-1),
.last 14 (2,true),
.cycle 10 19 true (0),
.cycle 14 3 true (2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 10 20 true (0),
.cycle 14 3 true (3),
.cycle 13 1 true (3)
])
theorem kid04_part616_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part616) = true := by rfl

def kid04_part617 : Audit := .split 13 (5,false) (byMove [
.cycle 11 16 true (1),
.cycle 21 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 2 true (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 11 15 true (1),
.last 27 (2,true),
.cycle 3 11 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 12 6 true (1),
.cycle 21 1 false (-1),
.last 14 (2,true),
.cycle 11 19 true (1),
.cycle 12 3 true (2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 11 20 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part617_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part617) = true := by rfl

def kid04_part593 : Audit := .split 11 (5,true) (byMove [(kid04_part594),(kid04_part595),(kid04_part596),(kid04_part597),(kid04_part598),(kid04_part599),(kid04_part600),(kid04_part601),(kid04_part602),(kid04_part603),(kid04_part604),(kid04_part605),(kid04_part606),(kid04_part607),(kid04_part608),(kid04_part609),(kid04_part610),(kid04_part611),(kid04_part612),(kid04_part613),(kid04_part614),(kid04_part615),(kid04_part616),(kid04_part617)])

theorem kid04_part593_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part593) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part594),(kid04_part595),(kid04_part596),(kid04_part597),(kid04_part598),(kid04_part599),(kid04_part600),(kid04_part601),(kid04_part602),(kid04_part603),(kid04_part604),(kid04_part605),(kid04_part606),(kid04_part607),(kid04_part608),(kid04_part609),(kid04_part610),(kid04_part611),(kid04_part612),(kid04_part613),(kid04_part614),(kid04_part615),(kid04_part616),(kid04_part617)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part594_checked

  · exact kid04_part600_checked

  · exact kid04_part606_checked

  · exact kid04_part612_checked

  · exact kid04_part595_checked

  · exact kid04_part601_checked

  · exact kid04_part607_checked

  · exact kid04_part613_checked

  · exact kid04_part596_checked

  · exact kid04_part602_checked

  · exact kid04_part608_checked

  · exact kid04_part614_checked

  · exact kid04_part597_checked

  · exact kid04_part603_checked

  · exact kid04_part609_checked

  · exact kid04_part615_checked

  · exact kid04_part598_checked

  · exact kid04_part604_checked

  · exact kid04_part610_checked

  · exact kid04_part616_checked

  · exact kid04_part599_checked

  · exact kid04_part605_checked

  · exact kid04_part611_checked

  · exact kid04_part617_checked

def kid04_part497 : Audit := .split 10 (4,true) (byMove [(kid04_part498),(kid04_part499),(kid04_part500),(kid04_part501),(kid04_part502),(kid04_part503),(kid04_part528),(kid04_part529),(kid04_part530),(kid04_part531),(kid04_part532),(kid04_part533),(kid04_part558),(kid04_part559),(kid04_part560),(kid04_part561),(kid04_part562),(kid04_part563),(kid04_part588),(kid04_part589),(kid04_part590),(kid04_part591),(kid04_part592),(kid04_part593)])

theorem kid04_part497_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (kid04_part497) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part498),(kid04_part499),(kid04_part500),(kid04_part501),(kid04_part502),(kid04_part503),(kid04_part528),(kid04_part529),(kid04_part530),(kid04_part531),(kid04_part532),(kid04_part533),(kid04_part558),(kid04_part559),(kid04_part560),(kid04_part561),(kid04_part562),(kid04_part563),(kid04_part588),(kid04_part589),(kid04_part590),(kid04_part591),(kid04_part592),(kid04_part593)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part498_checked

  · exact kid04_part528_checked

  · exact kid04_part558_checked

  · exact kid04_part588_checked

  · exact kid04_part499_checked

  · exact kid04_part529_checked

  · exact kid04_part559_checked

  · exact kid04_part589_checked

  · exact kid04_part500_checked

  · exact kid04_part530_checked

  · exact kid04_part560_checked

  · exact kid04_part590_checked

  · exact kid04_part501_checked

  · exact kid04_part531_checked

  · exact kid04_part561_checked

  · exact kid04_part591_checked

  · exact kid04_part502_checked

  · exact kid04_part532_checked

  · exact kid04_part562_checked

  · exact kid04_part592_checked

  · exact kid04_part503_checked

  · exact kid04_part533_checked

  · exact kid04_part563_checked

  · exact kid04_part593_checked

def kid04_part620 : Audit := .cycle 11 13 true (1)
theorem kid04_part620_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part620) = true := by rfl

def kid04_part621 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 false (3),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.cycle 0 22 false (3),
.cycle 0 21 false (3),
.cycle 13 14 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 14 7 false (0),
.cycle 0 22 false (3),
.cycle 19 3 false (-1),
.cycle 11 10 false (2),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.cycle 15 6 false (0),
.last 36 (5,true),
.cycle 1 20 false (3),
.cycle 13 13 false (1),
.cycle 13 17 true (-2),
.last 22 (5,true),
.cycle 13 16 true (-2)
])
theorem kid04_part621_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part621) = true := by rfl

def kid04_part622 : Audit := .cycle 15 1 false (1)
theorem kid04_part622_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part622) = true := by rfl

def kid04_part623 : Audit := .cycle 0 14 true (0)
theorem kid04_part623_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part623) = true := by rfl

def kid04_part624 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 7 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 7 false (1),
.cycle 0 15 false (3),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 8 12 true (0),
.cycle 0 15 true (0),
.cycle 13 3 false (1),
.cycle 11 3 false (2),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 7 false (1),
.last 19 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 24 true (0),
.cycle 11 16 true (1),
.last 15 (5,true),
.cycle 11 15 true (1)
])
theorem kid04_part624_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part624) = true := by rfl

def kid04_part625 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 7 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 20 (4,true),
.cycle 0 15 false (3),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 8 12 true (0),
.cycle 0 15 true (0),
.last 16 (4,true),
.cycle 11 3 false (2),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.last 20 (4,true),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 24 true (0),
.cycle 11 16 true (1),
.last 16 (4,true),
.cycle 11 15 true (1)
])
theorem kid04_part625_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part625) = true := by rfl

def kid04_part626 : Audit := .cycle 0 13 true (0)
theorem kid04_part626_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part626) = true := by rfl

def kid04_part627 : Audit := .cycle 11 12 true (1)
theorem kid04_part627_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part627) = true := by rfl

def kid04_part628 : Audit := .cycle 0 27 true (0)
theorem kid04_part628_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part628) = true := by rfl

def kid04_part629 : Audit := .cycle 3 20 true (0)
theorem kid04_part629_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part629) = true := by rfl

def kid04_part630 : Audit := .cycle 8 5 true (0)
theorem kid04_part630_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part630) = true := by rfl

def kid04_part631 : Audit := .cycle 0 14 true (0)
theorem kid04_part631_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part631) = true := by rfl

def kid04_part632 : Audit := .split 23 (5,true) (byMove [
.cycle 17 7 false (1),
.cycle 0 27 true (-2),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.cycle 15 9 false (1),
.cycle 26 29 true (-2),
.cycle 13 17 true (-1),
.cycle 14 10 false (2),
.last 27 (4,true),
.cycle 0 25 true (-1),
.last 24 (4,true),
.cycle 0 26 true (-1),
.last 26 (4,true),
.cycle 11 13 false (2),
.cycle 13 19 true (-2),
.cycle 24 1 false (-2),
.cycle 15 9 false (1),
.cycle 16 8 false (1),
.cycle 13 17 true (-1),
.last 25 (4,true),
.cycle 12 12 false (2),
.cycle 0 25 true (-1),
.last 24 (4,true),
.cycle 13 19 true (-1)
])
theorem kid04_part632_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part632) = true := by rfl

def kid04_part633 : Audit := .split 20 (4,true) (byMove [
.last 49 (5,true),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.cycle 0 22 false (3),
.cycle 0 32 true (-2),
.cycle 11 10 false (2),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 14 7 false (0),
.cycle 15 6 true (-2),
.cycle 19 3 false (-1),
.cycle 11 10 false (2),
.cycle 0 40 true (-3),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.cycle 15 6 false (0),
.last 47 (5,true),
.cycle 17 4 true (-2),
.cycle 0 41 true (-2),
.cycle 13 11 false (1),
.last 22 (5,true),
.cycle 9 12 false (2)
])
theorem kid04_part633_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part633) = true := by rfl

def kid04_part634 : Audit := .cycle 21 11 false (5)
theorem kid04_part634_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part634) = true := by rfl

def kid04_part635 : Audit := .cycle 11 14 true (1)
theorem kid04_part635_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part635) = true := by rfl

def kid04_part636 : Audit := .split 13 (4,true) (byMove [
.cycle 10 8 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 7 false (1),
.cycle 0 19 true (-1),
.cycle 11 14 true (1),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 15 true (0),
.cycle 11 7 true (1),
.last 14 (5,true),
.cycle 13 3 false (1),
.cycle 11 3 false (2),
.cycle 24 7 false (4),
.cycle 14 1 false (0),
.cycle 13 7 false (1),
.last 19 (5,true),
.cycle 11 14 true (1),
.cycle 1 15 true (0),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
])
theorem kid04_part636_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part636) = true := by rfl

def kid04_part637 : Audit := .split 13 (5,true) (byMove [
.cycle 10 8 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 20 (4,true),
.cycle 0 19 true (-1),
.cycle 11 14 true (1),
.cycle 13 10 false (2),
.cycle 9 12 true (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 16 true (0),
.last 16 (4,true),
.cycle 11 3 false (2),
.cycle 25 6 false (4),
.cycle 14 1 false (0),
.last 20 (4,true),
.cycle 13 6 false (1),
.cycle 11 14 true (1),
.last 15 (4,true),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 11 16 true (1)
])
theorem kid04_part637_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part637) = true := by rfl

def kid04_part638 : Audit := .cycle 0 13 true (0)
theorem kid04_part638_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part638) = true := by rfl

def kid04_part639 : Audit := .cycle 1 12 true (0)
theorem kid04_part639_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part639) = true := by rfl

def kid04_part640 : Audit := .cycle 2 11 true (0)
theorem kid04_part640_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part640) = true := by rfl

def kid04_part641 : Audit := .cycle 11 15 true (1)
theorem kid04_part641_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part641) = true := by rfl

def kid04_part642 : Audit := .split 14 (5,true) (byMove [
.cycle 10 5 true (0),
.last 24 (4,true),
.cycle 19 1 false (1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 0 17 false (3),
.cycle 11 15 true (1),
.cycle 13 14 false (3),
.cycle 12 3 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 17 true (0),
.last 30 (4,true),
.last 24 (4,true),
.last 16 (4,true),
.cycle 5 20 true (0),
.last 15 (4,true),
.last 20 (4,true),
.cycle 11 15 true (1),
.last 16 (4,true),
.cycle 12 3 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 11 17 true (1)
])
theorem kid04_part642_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part642) = true := by rfl

def kid04_part643 : Audit := .cycle 11 14 true (1)
theorem kid04_part643_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part643) = true := by rfl

def kid04_part619 : Audit := .split 12 (2,true) (byMove [(kid04_part620),(kid04_part621),(kid04_part622),(kid04_part623),(kid04_part624),(kid04_part625),(kid04_part626),(kid04_part627),(kid04_part628),(kid04_part629),(kid04_part630),(kid04_part631),(kid04_part632),(kid04_part633),(kid04_part634),(kid04_part635),(kid04_part636),(kid04_part637),(kid04_part638),(kid04_part639),(kid04_part640),(kid04_part641),(kid04_part642),(kid04_part643)])

theorem kid04_part619_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part619) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid04_part620),(kid04_part621),(kid04_part622),(kid04_part623),(kid04_part624),(kid04_part625),(kid04_part626),(kid04_part627),(kid04_part628),(kid04_part629),(kid04_part630),(kid04_part631),(kid04_part632),(kid04_part633),(kid04_part634),(kid04_part635),(kid04_part636),(kid04_part637),(kid04_part638),(kid04_part639),(kid04_part640),(kid04_part641),(kid04_part642),(kid04_part643)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part620_checked

  · exact kid04_part626_checked

  · exact kid04_part632_checked

  · exact kid04_part638_checked

  · exact kid04_part621_checked

  · exact kid04_part627_checked

  · exact kid04_part633_checked

  · exact kid04_part639_checked

  · exact kid04_part622_checked

  · exact kid04_part628_checked

  · exact kid04_part634_checked

  · exact kid04_part640_checked

  · exact kid04_part623_checked

  · exact kid04_part629_checked

  · exact kid04_part635_checked

  · exact kid04_part641_checked

  · exact kid04_part624_checked

  · exact kid04_part630_checked

  · exact kid04_part636_checked

  · exact kid04_part642_checked

  · exact kid04_part625_checked

  · exact kid04_part631_checked

  · exact kid04_part637_checked

  · exact kid04_part643_checked

def kid04_part645 : Audit := .split 46 (4,true) (byMove [
.last 59 (5,true),
.proven (BB6.Agent11Raw39B0RBPumps.M108.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M108.never m hm),
.cycle 45 15 false (1),
.cycle 60 35 false (2),
.proven (BB6.Agent11Raw39B0RBPumps.M109.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M109.never m hm),
.proven (BB6.Agent11Raw39B0RBPumps.M110.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M110.never m hm),
.cycle 0 66 true (-3),
.cycle 13 34 true (-3),
.cycle 29 45 true (-4),
.cycle 45 15 false (1),
.cycle 11 44 true (-3),
.cycle 10 60 true (-3),
.last 107 (5,true),
.cycle 10 64 true (-3),
.cycle 0 70 true (-3),
.cycle 45 13 false (1),
.last 81 (5,true),
.last 89 (5,true),
.cycle 16 62 true (0),
.cycle 13 34 true (-3),
.cycle 10 56 true (-3),
.cycle 50 53 true (2),
.last 48 (5,true),
.proven (BB6.Agent11Raw39B0RBPumps.M111.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M111.never m hm)
])
theorem kid04_part645_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part645) = true := by rfl

def kid04_part646 : Audit := .split 20 (4,true) (byMove [
.last 33 (5,true),
.cycle 10 44 false (4),
.cycle 19 15 false (1),
.cycle 7 34 false (3),
.cycle 8 13 false (2),
.cycle 1 21 false (3),
.cycle 0 21 true (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M112.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M112.never m hm),
.cycle 50 47 true (-2),
.cycle 19 15 false (1),
.last 41 (5,true),
.last 49 (5,true),
.cycle 7 37 false (3),
.last 25 (5,true),
.cycle 0 23 true (-3),
.cycle 19 13 false (1),
.cycle 8 13 false (2),
.cycle 12 28 false (4),
.cycle 16 17 true (0),
.cycle 7 23 false (3),
.last 47 (5,true),
.cycle 19 57 true (-2),
.last 22 (5,true),
.cycle 7 15 false (3)
])
theorem kid04_part646_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part646) = true := by rfl

def kid04_part647 : Audit := .split 35 (4,true) (byMove [
.last 48 (5,true),
.cycle 10 59 false (3),
.cycle 21 15 false (0),
.cycle 7 49 false (3),
.cycle 8 28 false (2),
.cycle 1 36 false (3),
.cycle 3 56 false (3),
.cycle 51 62 false (5),
.cycle 23 106 true (-5),
.cycle 22 15 false (0),
.last 56 (5,true),
.last 64 (5,true),
.cycle 7 52 false (3),
.cycle 7 53 false (3),
.cycle 3 58 false (3),
.cycle 23 13 false (0),
.cycle 8 28 false (2),
.cycle 12 43 false (3),
.cycle 18 33 false (3),
.cycle 7 38 false (3),
.last 62 (5,true),
.proven (BB6.Agent11Raw39B0RBPumps.M113.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M113.never m hm),
.last 37 (5,true),
.cycle 7 30 false (3)
])
theorem kid04_part647_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part647) = true := by rfl

def kid04_part648 : Audit := .split 32 (5,true) (byMove [
.last 55 (4,true),
.cycle 13 20 true (-3),
.last 47 (4,true),
.last 65 (4,true),
.last 67 (4,true),
.last 75 (4,true),
.last 78 (4,true),
.last 57 (4,true),
.last 47 (4,true),
.cycle 15 18 true (-1),
.last 33 (4,true),
.last 49 (4,true),
.last 35 (4,true),
.last 38 (4,true),
.last 80 (4,true),
.last 45 (4,true),
.last 47 (4,true),
.last 82 (4,true),
.cycle 13 41 true (-3),
.last 34 (4,true),
.last 53 (4,true),
.cycle 15 18 true (-1),
.last 33 (4,true),
.last 36 (4,true)
])
theorem kid04_part648_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part648) = true := by rfl

def kid04_part649 : Audit := .split 19 (4,true) (byMove [
.proven (BB6.Agent11Raw39B0RBPumps.M114.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M114.never m hm),
.cycle 7 13 false (3),
.cycle 8 13 false (2),
.cycle 0 21 true (-3),
.cycle 8 13 false (2),
.last 20 (5,true),
.last 32 (5,true),
.cycle 13 34 true (-3),
.cycle 59 64 true (1),
.last 45 (5,true),
.cycle 7 15 false (3),
.cycle 7 23 false (3),
.cycle 40 3 false (-2),
.cycle 7 13 false (3),
.cycle 8 13 false (2),
.cycle 122 1 false (-4),
.cycle 8 13 false (2),
.last 20 (5,true),
.cycle 16 16 true (0),
.cycle 13 36 true (-3),
.cycle 7 21 false (3),
.last 50 (5,true),
.last 21 (5,true),
.cycle 7 17 false (3)
])
theorem kid04_part649_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part649) = true := by rfl

def kid04_part650 : Audit := .split 19 (5,true) (byMove [
.proven (BB6.Agent11Raw39B0RBPumps.M115.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M115.never m hm),
.cycle 7 13 false (3),
.cycle 1 21 false (3),
.cycle 0 21 true (-3),
.last 20 (4,true),
.cycle 1 21 false (3),
.last 78 (4,true),
.last 46 (4,true),
.last 34 (4,true),
.last 79 (4,true),
.cycle 7 15 false (3),
.cycle 7 23 false (3),
.last 41 (4,true),
.cycle 7 13 false (3),
.cycle 1 21 false (3),
.last 73 (4,true),
.last 20 (4,true),
.last 55 (4,true),
.last 31 (4,true),
.last 30 (4,true),
.cycle 7 21 false (3),
.cycle 13 76 true (-3),
.last 22 (4,true),
.last 22 (4,true)
])
theorem kid04_part650_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part650) = true := by rfl

def kid04_part651 : Audit := .split 31 (5,true) (byMove [
.cycle 16 19 true (0),
.proven (BB6.Agent11Raw39B0RBPumps.M116.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M116.never m hm),
.last 35 (4,true),
.last 35 (4,true),
.last 32 (4,true),
.last 74 (4,true),
.cycle 67 46 true (3),
.last 55 (4,true),
.cycle 16 17 true (0),
.cycle 15 17 true (-1),
.last 32 (4,true),
.last 48 (4,true),
.last 41 (4,true),
.last 46 (4,true),
.last 58 (4,true),
.last 58 (4,true),
.last 32 (4,true),
.last 62 (4,true),
.cycle 13 40 true (-3),
.last 33 (4,true),
.cycle 16 17 true (0),
.cycle 15 17 true (-1),
.last 32 (4,true),
.last 35 (4,true)
])
theorem kid04_part651_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part651) = true := by rfl

def kid04_part652 : Audit := .split 45 (4,true) (byMove [
.last 74 (5,true),
.last 91 (5,true),
.last 154 (5,true),
.cycle 13 35 true (-3),
.last 91 (5,true),
.last 46 (5,true),
.last 67 (5,true),
.cycle 13 33 true (-3),
.cycle 14 47 true (-2),
.last 77 (5,true),
.last 108 (5,true),
.last 132 (5,true),
.cycle 13 41 true (-3),
.last 98 (5,true),
.cycle 13 41 true (-3),
.cycle 13 35 true (-3),
.last 60 (5,true),
.last 46 (5,true),
.last 67 (5,true),
.cycle 13 33 true (-3),
.last 126 (5,true),
.last 69 (5,true),
.last 47 (5,true),
.last 95 (5,true)
])
theorem kid04_part652_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part652) = true := by rfl

def kid04_part653 : Audit := .cycle 7 21 false (4)
theorem kid04_part653_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part653) = true := by rfl

def kid04_part654 : Audit := .cycle 7 19 false (3)
theorem kid04_part654_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part654) = true := by rfl

def kid04_part655 : Audit := .split 22 (4,true) (byMove [
.last 35 (5,true),
.cycle 10 19 true (-3),
.cycle 21 15 false (1),
.cycle 7 36 false (3),
.cycle 8 15 false (3),
.cycle 1 23 false (3),
.cycle 16 7 true (0),
.proven (BB6.Agent11Raw39B0RBPumps.M117.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M117.never m hm),
.proven (BB6.Agent11Raw39B0RBPumps.M118.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M118.never m hm),
.cycle 21 15 false (1),
.last 51 (5,true),
.last 67 (5,true),
.cycle 7 39 false (3),
.last 29 (5,true),
.cycle 14 9 true (-2),
.cycle 21 13 false (1),
.last 36 (5,true),
.cycle 12 11 true (-3),
.cycle 16 7 true (0),
.cycle 13 28 true (-3),
.last 63 (5,true),
.cycle 8 20 true (-3),
.last 24 (5,true),
.cycle 7 17 false (3)
])
theorem kid04_part655_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part655) = true := by rfl

def kid04_part656 : Audit := .split 30 (4,true) (byMove [
.last 43 (5,true),
.cycle 10 27 true (-3),
.cycle 29 15 false (1),
.cycle 7 44 false (4),
.cycle 8 23 false (4),
.cycle 1 31 false (4),
.cycle 16 15 true (0),
.proven (BB6.Agent11Raw39B0RBPumps.M119.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M119.never m hm),
.last 321 (5,true),
.cycle 29 15 false (1),
.last 59 (5,true),
.last 75 (5,true),
.cycle 7 47 false (4),
.last 45 (5,true),
.cycle 14 17 true (-2),
.cycle 29 13 false (1),
.last 42 (5,true),
.cycle 12 19 true (-3),
.cycle 16 15 true (0),
.cycle 13 36 true (-3),
.last 71 (5,true),
.cycle 1 36 true (-3),
.last 32 (5,true),
.cycle 7 25 false (4)
])
theorem kid04_part656_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part656) = true := by rfl

def kid04_part657 : Audit := .split 22 (5,true) (byMove [
.cycle 7 50 false (3),
.last 73 (4,true),
.last 37 (4,true),
.cycle 10 17 false (2),
.cycle 8 15 false (2),
.cycle 1 23 false (3),
.last 77 (4,true),
.last 43 (4,true),
.last 26 (4,true),
.cycle 0 24 true (-3),
.last 23 (4,true),
.proven (BB6.Agent11Raw39B0RBPumps.M120.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M120.never m hm),
.last 25 (4,true),
.cycle 6 19 false (3),
.last 81 (4,true),
.last 35 (4,true),
.cycle 8 15 false (2),
.last 57 (4,true),
.last 50 (4,true),
.last 24 (4,true),
.last 45 (4,true),
.cycle 15 22 true (-1),
.last 23 (4,true),
.last 26 (4,true)
])
theorem kid04_part657_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part657) = true := by rfl

def kid04_part658 : Audit := .split 20 (4,true) (byMove [
.last 92 (5,true),
.cycle 121 63 true (-3),
.cycle 19 15 false (1),
.cycle 63 40 false (1),
.cycle 8 13 false (2),
.cycle 1 21 false (3),
.cycle 0 24 true (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M121.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M121.never m hm),
.cycle 0 23 true (-3),
.cycle 19 15 false (1),
.last 57 (5,true),
.proven (BB6.Agent11Raw39B0RBPumps.M122.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M122.never m hm),
.cycle 7 37 false (3),
.last 25 (5,true),
.cycle 0 28 true (-3),
.cycle 19 13 false (1),
.cycle 8 13 false (2),
.last 47 (5,true),
.cycle 16 20 true (0),
.cycle 17 4 true (0),
.far false 10 ⟨0,[0, 9, 3, 2, 3, 2, 2, 3, 1, 9, 3, 1, 1, 3, 6, 5, 4, 1, 8, 7],[36028797018963968, 72057594037927936, 8, 0, 16777216, 2251799813685248, 8192, 16384, 2097152, 1191220243402125504, 1152921504606851072, 1191220243402125504, 8192, 16384, 2097152, 1191220243402125504, 1191220243402125504, 1191220243402125504, 524288, 1048576, 32768, 1191220243402125504, 1191220243402125504, 1191220243402125504, 36028797018963968, 72057594037927936, 512, 1191220243402125504, 64, 2097152, 128, 256, 2097152, 128, 1152921504606846976, 36028797018963968, 524288, 1048576, 512, 36028797018963968, 1191220243402125504, 2097152, 2147483648, 4294967296, 549755813888, 33554432, 1152921504606846976, 1191220243402125504, 128, 256, 134217728, 1191220243402125504, 16777216, 549755813888, 8796093022208, 17592186044416, 2251799813685248, 524290, 1152921504606846976, 17592186044416, 1152921504606846976],[2, 36028797018963968, 2251799813685248, 1, 72057594037927936, 1152921504606846976, 524288, 1191220243402125504, 1191220243402125504, 262144, 16384, 1152921504606846976, 524288, 1191220243402125504, 1191220243402125504, 262144, 16384, 1152921504606846976, 8192, 1191220243402125504, 1191220243402125504, 4096, 1048576, 1152921504606846976, 128, 36028797018963968, 1191220243402125504, 64, 72057594037927936, 1152921504606846976, 524288, 2097152, 64, 262144, 256, 1152921504606846976, 128, 1152921504606846976, 64, 64, 1048576, 1152921504606846976, 137438953472, 549755813888, 16777216, 68719476736, 4294967296, 1152921504606846976, 33554432, 1152921504606846976, 16777216, 16777216, 256, 1152921504606846976, 562949953421312, 2251799813685248, 2251799813685248, 281474976710656, 17592186044416, 1152921504606846976, 1152921504606846976],1679824484690821090⟩,
.last 45 (5,true),
.last 22 (5,true),
.cycle 7 15 false (3)
])
theorem kid04_part658_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part658) = true := by rfl

def kid04_part659 : Audit := .split 45 (5,true) (byMove [
.cycle 13 88 true (-5),
.last 81 (4,true),
.cycle 47 1 false (-3),
.cycle 46 1 false (-4),
.last 53 (4,true),
.last 61 (4,true),
.cycle 13 34 true (-3),
.last 109 (4,true),
.last 81 (4,true),
.last 79 (4,true),
.last 46 (4,true),
.last 62 (4,true),
.last 48 (4,true),
.last 131 (4,true),
.cycle 13 36 true (-4),
.cycle 46 1 false (-4),
.last 92 (4,true),
.cycle 13 38 true (-5),
.cycle 13 34 true (-3),
.last 47 (4,true),
.cycle 13 38 true (-4),
.last 79 (4,true),
.last 46 (4,true),
.last 49 (4,true)
])
theorem kid04_part659_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part659) = true := by rfl

def kid04_part660 : Audit := .split 48 (5,true) (byMove [
.cycle 13 41 true (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M124.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M124.never m hm),
.last 63 (4,true),
.cycle 13 51 true (-4),
.cycle 13 53 true (-6),
.cycle 13 61 true (-6),
.cycle 13 37 true (-3),
.cycle 13 43 true (-3),
.last 63 (4,true),
.cycle 13 72 true (-3),
.last 49 (4,true),
.last 65 (4,true),
.last 51 (4,true),
.cycle 13 47 true (-3),
.cycle 13 39 true (-3),
.last 61 (4,true),
.last 84 (4,true),
.cycle 13 41 true (-3),
.cycle 13 37 true (-3),
.last 50 (4,true),
.cycle 13 39 true (-3),
.cycle 13 70 true (-3),
.last 49 (4,true),
.last 52 (4,true)
])
theorem kid04_part660_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part660) = true := by rfl

def kid04_part661 : Audit := .split 19 (4,true) (byMove [
.cycle 16 8 true (0),
.cycle 7 13 false (3),
.cycle 8 13 false (2),
.cycle 7 51 false (3),
.cycle 8 13 false (2),
.last 20 (5,true),
.last 48 (5,true),
.last 22 (5,true),
.last 22 (5,true),
.far false 10 ⟨0,[0, 9, 3, 2, 3, 2, 2, 3, 1, 9, 3, 1, 1, 3, 6, 5, 4, 1, 8, 7],[36028797018963968, 72057594037927936, 8, 0, 16777216, 2251799813685248, 8192, 16384, 2097152, 1188968443588440256, 1152921504606851072, 1155190896606609408, 8192, 16384, 2097152, 1188968443588440256, 1188968443588440256, 1188968443588440256, 524288, 1048576, 32768, 1188968443588440256, 1188968443588440256, 1188968443588440256, 36028797018963968, 72057594037927936, 512, 1188968443588440256, 64, 2097152, 128, 256, 2097152, 128, 1152921504606846976, 1188968443588440256, 524288, 1048576, 512, 36028797018963968, 1188968443588440256, 2097152, 2147483648, 4294967296, 549755813888, 33554432, 1152921504606846976, 1188968443588440256, 128, 256, 134217728, 1188968443588440256, 16777216, 549755813888, 8796093022208, 17592186044416, 2251799813685248, 524290, 1152921504606846976, 17592186044416, 1152921504606846976],[2, 36028797018963968, 128, 1, 8, 1152921504606846976, 524288, 1188968443588440256, 1188968443588440256, 262144, 2097152, 1152921504606846976, 524288, 1188968443588440256, 1188968443588440256, 262144, 2097152, 1152921504606846976, 8192, 1188968443588440256, 1188968443588440256, 4096, 32768, 1152921504606846976, 128, 36028797018963968, 128, 64, 512, 1152921504606846976, 524288, 36028797018963968, 64, 262144, 2097152, 1152921504606846976, 128, 1152921504606846976, 1152921504606846976, 64, 512, 1152921504606846976, 137438953472, 1188968443588440256, 16777216, 68719476736, 549755813888, 1152921504606846976, 33554432, 1152921504606846976, 1152921504606846976, 16777216, 134217728, 1152921504606846976, 562949953421312, 1188968443588440256, 262145, 281474976710656, 2251799813685248, 1152921504606846976, 1152921504606846976],1679824519050559458⟩,
.cycle 11 38 true (-3),
.last 20 (5,true),
.last 39 (5,true),
.cycle 7 13 false (3),
.cycle 8 13 false (2),
.last 43 (5,true),
.cycle 8 13 false (2),
.last 20 (5,true),
.last 71 (5,true),
.cycle 13 38 true (-3),
.cycle 18 2 true (1),
.last 33 (5,true),
.last 22 (5,true),
.last 20 (5,true)
])
theorem kid04_part661_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part661) = true := by rfl

def kid04_part662 : Audit := .split 19 (5,true) (byMove [
.cycle 16 8 true (0),
.cycle 7 13 false (3),
.last 27 (4,true),
.last 23 (4,true),
.last 20 (4,true),
.cycle 1 21 false (3),
.cycle 13 37 true (-3),
.last 43 (4,true),
.cycle 7 15 false (3),
.far false 10 ⟨0,[0, 9, 3, 2, 3, 2, 2, 3, 1, 9, 3, 1, 1, 3, 6, 5, 4, 1, 8, 7],[36028797018963968, 72057594037927936, 8, 0, 16777216, 2251799813685248, 8192, 16384, 2097152, 1188950301626343552, 4160, 1155190896607657984, 8192, 16384, 2097152, 1188950301626343424, 1152921504623628288, 1152939096793989120, 524288, 1048576, 32768, 1188950301626343424, 1152921504623890432, 1152939096795004928, 36028797018963968, 72057594037927936, 512, 1188950301626343424, 64, 2097152, 128, 256, 2097152, 128, 64, 1152921504606846976, 524288, 1048576, 512, 36028797018963968, 1152921504606846976, 2097152, 2147483648, 4294967296, 549755813888, 33554432, 16777216, 1152921504606846976, 128, 256, 134217728, 1188950301625819136, 16777216, 549755813888, 8796093022208, 17592186044416, 2251799813685248, 524290, 262145, 17592186044416, 1152921504606846976],[2, 36028797018963968, 16777216, 1, 1152921504606846976, 8, 524288, 1152921504606855168, 4160, 262144, 1152921504606846976, 2097152, 524288, 1188950301626343424, 1152921504623628288, 262144, 1152921504606846976, 2097152, 8192, 1188950301625819136, 1152921504623890432, 4096, 1152921504606846976, 32768, 128, 36028797018963968, 64, 64, 1152921504606846976, 512, 524288, 1152921504606846976, 64, 262144, 1152921504606846976, 2097152, 128, 36028797018963968, 1152921504606846976, 64, 1152921504606846976, 512, 137438953472, 1152921504606846976, 16777216, 68719476736, 1152921504606846976, 549755813888, 33554432, 36028797019488256, 16777216, 16777216, 1152921504606846976, 134217728, 562949953421312, 1152921504606846976, 262145, 281474976710656, 1152921504606846976, 2251799813685248, 1152921504606846976],1679754150306381794⟩,
.last 20 (4,true),
.last 48 (4,true),
.last 29 (4,true),
.cycle 7 13 false (3),
.last 46 (4,true),
.cycle 44 1 false (-4),
.last 20 (4,true),
.last 46 (4,true),
.last 47 (4,true),
.last 21 (4,true),
.cycle 18 2 true (1),
.cycle 15 19 true (-1),
.last 20 (4,true),
.last 23 (4,true)
])
theorem kid04_part662_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part662) = true := by rfl

def kid04_part663 : Audit := .split 30 (4,true) (byMove [
.last 59 (5,true),
.cycle 7 141 false (6),
.cycle 13 40 true (-3),
.cycle 107 86 true (3),
.cycle 8 25 false (6),
.last 31 (5,true),
.cycle 16 15 true (0),
.last 49 (5,true),
.cycle 145 76 true (3),
.proven (BB6.Agent11Raw39B0RBPumps.M127.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M127.never m hm),
.last 71 (5,true),
.last 103 (5,true),
.last 34 (5,true),
.last 119 (5,true),
.last 51 (5,true),
.cycle 67 46 true (3),
.last 47 (5,true),
.last 31 (5,true),
.cycle 16 15 true (0),
.cycle 13 36 true (-3),
.last 95 (5,true),
.cycle 17 17 true (1),
.last 32 (5,true),
.cycle 7 31 false (6)
])
theorem kid04_part663_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part663) = true := by rfl

def kid04_part664 : Audit := .split 29 (4,true) (byMove [
.last 58 (5,true),
.cycle 7 23 false (5),
.cycle 21 39 false (5),
.last 188 (5,true),
.cycle 8 23 false (5),
.last 30 (5,true),
.cycle 16 14 true (0),
.last 48 (5,true),
.cycle 0 47 true (-3),
.cycle 10 24 true (-3),
.last 70 (5,true),
.last 86 (5,true),
.last 65 (5,true),
.last 100 (5,true),
.cycle 31 147 true (-1),
.cycle 13 64 true (-3),
.cycle 29 15 false (1),
.last 30 (5,true),
.cycle 16 14 true (0),
.cycle 13 35 true (-3),
.last 82 (5,true),
.cycle 17 16 true (1),
.last 31 (5,true),
.cycle 7 27 false (5)
])
theorem kid04_part664_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part664) = true := by rfl

def kid04_part665 : Audit := .split 28 (4,true) (byMove [
.last 41 (5,true),
.cycle 10 25 true (-3),
.cycle 27 15 false (1),
.cycle 7 42 false (4),
.cycle 8 21 false (4),
.cycle 1 29 false (4),
.cycle 16 13 true (0),
.proven (BB6.Agent11Raw39B0RBPumps.M128.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M128.never m hm),
.last 309 (5,true),
.cycle 27 15 false (1),
.last 57 (5,true),
.last 73 (5,true),
.cycle 7 45 false (4),
.last 41 (5,true),
.cycle 14 15 true (-2),
.cycle 27 13 false (1),
.far true 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 3, 0, 1],[4195344, 8192, 2097152, 512, 2048, 2, 1024, 4195344, 33562624, 2097152, 8388608, 8192, 4195328, 16, 2097152, 512, 2048, 2, 1024, 4195328, 4203536, 2097152, 8388608, 33554432, 4194304, 4195344, 2097152, 512, 2048, 2, 1073741824],[8390672, 16, 8192, 8390656, 1024, 1073741824, 2048, 65536, 4195344, 33564672, 4194304, 1073741824, 8390656, 16, 16, 8388608, 1024, 1073741824, 2048, 268435456, 4195328, 8192, 4194304, 1073741824, 8388608, 16, 4195344, 8388608, 1024, 1073741824, 1073741824],1073741824⟩,
.cycle 12 17 true (-3),
.cycle 16 13 true (0),
.cycle 13 34 true (-3),
.last 69 (5,true),
.cycle 2 32 true (-3),
.last 30 (5,true),
.cycle 7 23 false (4)
])
theorem kid04_part665_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part665) = true := by rfl

def kid04_part666 : Audit := .split 49 (5,true) (byMove [
.cycle 51 44 true (1),
.cycle 70 42 true (4),
.cycle 13 48 true (-3),
.last 53 (4,true),
.last 50 (4,true),
.last 133 (4,true),
.cycle 13 38 true (-3),
.last 73 (4,true),
.cycle 17 42 true (1),
.cycle 17 40 true (1),
.last 50 (4,true),
.last 66 (4,true),
.last 59 (4,true),
.last 69 (4,true),
.cycle 13 40 true (-3),
.cycle 13 46 true (-3),
.last 50 (4,true),
.cycle 13 50 true (-3),
.cycle 13 38 true (-3),
.last 51 (4,true),
.cycle 17 42 true (1),
.cycle 17 40 true (1),
.last 50 (4,true),
.last 53 (4,true)
])
theorem kid04_part666_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part666) = true := by rfl

def kid04_part667 : Audit := .split 20 (5,true) (byMove [
.cycle 17 5 true (1),
.last 22 (4,true),
.last 41 (4,true),
.last 24 (4,true),
.last 21 (4,true),
.cycle 1 23 false (3),
.cycle 13 38 true (-3),
.last 47 (4,true),
.cycle 18 3 true (2),
.last 36 (4,true),
.last 21 (4,true),
.last 49 (4,true),
.last 27 (4,true),
.last 22 (4,true),
.last 22 (4,true),
.cycle 7 19 false (3),
.last 21 (4,true),
.last 36 (4,true),
.last 48 (4,true),
.last 22 (4,true),
.cycle 18 3 true (2),
.cycle 15 20 true (-1),
.last 21 (4,true),
.last 24 (4,true)
])
theorem kid04_part667_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part667) = true := by rfl

def kid04_part668 : Audit := .split 21 (4,true) (byMove [
.proven (BB6.Agent11Raw39B0RBPumps.M130.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M130.never m hm),
.cycle 7 15 false (3),
.cycle 7 17 false (3),
.cycle 0 23 true (-3),
.cycle 8 15 false (3),
.last 22 (5,true),
.last 34 (5,true),
.cycle 13 36 true (-3),
.cycle 61 66 true (1),
.last 47 (5,true),
.cycle 7 17 false (3),
.cycle 7 25 false (3),
.cycle 42 3 false (-2),
.cycle 7 15 false (3),
.last 23 (5,true),
.cycle 126 1 false (-4),
.last 34 (5,true),
.last 22 (5,true),
.cycle 16 18 true (0),
.cycle 13 38 true (-3),
.cycle 7 23 false (3),
.last 52 (5,true),
.last 23 (5,true),
.cycle 7 19 false (3)
])
theorem kid04_part668_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part668) = true := by rfl

def kid04_part644 : Audit := .split 18 (2,true) (byMove [(kid04_part645),(kid04_part646),(kid04_part647),(kid04_part648),(kid04_part649),(kid04_part650),(kid04_part651),(kid04_part652),(kid04_part653),(kid04_part654),(kid04_part655),(kid04_part656),(kid04_part657),(kid04_part658),(kid04_part659),(kid04_part660),(kid04_part661),(kid04_part662),(kid04_part663),(kid04_part664),(kid04_part665),(kid04_part666),(kid04_part667),(kid04_part668)])

theorem kid04_part644_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part644) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) 18 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (2,true) (some mv)) (byMove [(kid04_part645),(kid04_part646),(kid04_part647),(kid04_part648),(kid04_part649),(kid04_part650),(kid04_part651),(kid04_part652),(kid04_part653),(kid04_part654),(kid04_part655),(kid04_part656),(kid04_part657),(kid04_part658),(kid04_part659),(kid04_part660),(kid04_part661),(kid04_part662),(kid04_part663),(kid04_part664),(kid04_part665),(kid04_part666),(kid04_part667),(kid04_part668)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part645_checked

  · exact kid04_part651_checked

  · exact kid04_part657_checked

  · exact kid04_part663_checked

  · exact kid04_part646_checked

  · exact kid04_part652_checked

  · exact kid04_part658_checked

  · exact kid04_part664_checked

  · exact kid04_part647_checked

  · exact kid04_part653_checked

  · exact kid04_part659_checked

  · exact kid04_part665_checked

  · exact kid04_part648_checked

  · exact kid04_part654_checked

  · exact kid04_part660_checked

  · exact kid04_part666_checked

  · exact kid04_part649_checked

  · exact kid04_part655_checked

  · exact kid04_part661_checked

  · exact kid04_part667_checked

  · exact kid04_part650_checked

  · exact kid04_part656_checked

  · exact kid04_part662_checked

  · exact kid04_part668_checked

def kid04_part669 : Audit := .split 10 (2,true) (byMove [
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 24 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 24 1 false (2),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 11 3 false (2),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 23 1 false (1),
.cycle 27 1 false (3),
.last 15 (5,true),
.cycle 0 16 true (0)
]),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 20 (5,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 11 3 false (0),
.cycle 21 1 false (-3),
.last 22 (5,true),
.cycle 14 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 20 (5,true),
.cycle 0 17 true (-1),
.cycle 23 1 false (-1),
.cycle 24 1 false (0),
.last 15 (5,true),
.cycle 9 5 false (1)
]),
.cycle 17 1 false (-3),
.split 15 (4,true) (byMove [
.cycle 0 16 true (-1),
.cycle 26 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 16 true (-1),
.cycle 26 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 13 3 false (2),
.cycle 32 1 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 47 1 false (5),
.cycle 1 15 true (-1),
.cycle 25 1 false (1),
.cycle 29 1 false (3),
.last 17 (5,true),
.cycle 0 20 true (-1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.split 13 (4,true) (byMove [
.cycle 25 1 false (1),
.cycle 18 1 false (-2),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.cycle 18 1 false (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 32 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 8 6 true (0),
.cycle 24 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 34 1 false (0),
.cycle 26 1 false (2),
.cycle 18 1 false (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 36 1 false (0),
.last 15 (5,true),
.cycle 0 16 true (0)
]),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 37 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 14 (4,true),
.cycle 25 1 false (3),
.last 13 (4,true),
.cycle 17 1 false (3),
.last 15 (4,true),
.last 15 (4,true),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 36 1 false (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 34 1 false (0),
.last 13 (4,true),
.cycle 13 5 true (1)
]),
.cycle 9 2 true (0)
])
theorem kid04_part669_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part669) = true := by rfl

def kid04_part670 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 11 3 false (2),
.split 15 (2,true) (byMove [
.cycle 26 1 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 13 3 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 14 true (0),
.cycle 25 1 false (-1),
.cycle 23 1 false (-1),
.cycle 8 8 true (0),
.cycle 29 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 29 1 false (1),
.cycle 27 1 false (1),
.cycle 13 3 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 35 1 false (-1),
.last 17 (5,true),
.cycle 0 18 true (0)
]),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 26 1 false (2),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 26 1 false (2),
.cycle 19 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 13 3 true (1),
.cycle 18 1 false (2),
.cycle 11 5 false (2),
.last 17 (2,true),
.cycle 28 1 false (2),
.cycle 16 1 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 30 (2,true),
.cycle 12 4 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 13 3 true (1),
.cycle 0 19 true (0)
]),
.cycle 0 16 true (0)
])
theorem kid04_part670_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part670) = true := by rfl

def kid04_part671 : Audit := .split 10 (4,true) (byMove [
.cycle 0 15 true (-1),
.cycle 18 2 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 14 true (0),
.split 12 (2,true) (byMove [
.cycle 21 2 false (3),
.cycle 14 2 false (0),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 21 2 false (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.last 23 (5,true),
.cycle 20 2 false (2),
.cycle 18 2 false (2),
.cycle 8 5 true (0),
.last 15 (5,true),
.cycle 15 2 false (1),
.cycle 14 2 false (0),
.cycle 24 2 false (4),
.cycle 22 2 false (4),
.cycle 15 2 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 26 true (0),
.last 14 (5,true),
.last 25 (5,true)
]),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 11 2 false (1),
.cycle 10 3 false (0),
.split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 14 2 false (-2),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 0 18 true (-1),
.last 25 (5,true),
.cycle 0 15 true (-1),
.cycle 18 2 false (0),
.cycle 8 5 false (2),
.last 15 (5,true),
.cycle 15 2 false (-1),
.cycle 14 2 false (-2),
.cycle 30 2 false (4),
.cycle 26 2 false (4),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 10 7 false (2),
.cycle 28 2 false (-2),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 14 (5,true),
.cycle 16 2 false (-2)
]),
.cycle 0 18 true (-1),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 14 true (0),
.split 12 (2,true) (byMove [
.last 24 (5,true),
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.last 23 (5,true),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.last 15 (5,true),
.last 16 (5,true),
.cycle 10 4 true (0),
.cycle 19 2 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 2097152, 256, 524290, 1073741824, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 134217728, 1325408256, 1325408256, 1325408256, 1073741824],[2, 0, 0, 1, 128, 1073741824, 8192, 256, 524290, 4096, 128, 1073741824, 524288, 1073741824, 256, 262144, 33554432, 1073741824, 8192, 256, 524290, 4096, 128, 1073741824, 33554432, 1325408256, 1325408256, 16777216, 33554432, 1073741824, 1073741824],2135045120⟩,
.cycle 1 15 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 26 true (0),
.last 14 (5,true),
.cycle 1 14 true (0)
]),
.cycle 0 13 true (0),
.cycle 15 2 false (1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 49 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 15 2 false (1),
.cycle 14 2 false (0),
.last 13 (2,true),
.cycle 22 2 false (4),
.cycle 14 3 true (2),
.cycle 15 2 false (3),
.cycle 10 5 false (1),
.last 14 (2,true),
.cycle 17 2 false (1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 31 (2,true),
.cycle 10 4 true (0),
.last 13 (2,true),
.last 32 (2,true),
.cycle 14 3 true (2),
.cycle 13 5 true (1)
]),
.cycle 9 2 true (0)
])
theorem kid04_part671_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part671) = true := by rfl

def kid04_part673 : Audit := .cycle 0 15 true (-1)
theorem kid04_part673_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part673) = true := by rfl

def kid04_part674 : Audit := .cycle 19 1 false (-1)
theorem kid04_part674_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part674) = true := by rfl

def kid04_part675 : Audit := .cycle 12 1 false (0)
theorem kid04_part675_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part675) = true := by rfl

def kid04_part676 : Audit := .cycle 11 1 false (-1)
theorem kid04_part676_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part676) = true := by rfl

def kid04_part677 : Audit := .cycle 12 1 false (-2)
theorem kid04_part677_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part677) = true := by rfl

def kid04_part678 : Audit := .cycle 11 1 false (-1)
theorem kid04_part678_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part678) = true := by rfl

def kid04_part679 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 11 3 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 1 false (1),
.cycle 25 1 false (3),
.cycle 25 1 false (3),
.cycle 0 16 true (0)
])
theorem kid04_part679_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part679) = true := by rfl

def kid04_part680 : Audit := .split 12 (2,true) (byMove [
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 22 1 false (2),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 5 true (0),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.last 13 (4,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 36 1 false (2),
.cycle 20 1 false (0),
.cycle 0 29 true (0)
])
theorem kid04_part680_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part680) = true := by rfl

def kid04_part681 : Audit := .cycle 0 13 true (0)
theorem kid04_part681_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part681) = true := by rfl

def kid04_part682 : Audit := .cycle 11 1 false (1)
theorem kid04_part682_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part682) = true := by rfl

def kid04_part683 : Audit := .cycle 12 1 false (0)
theorem kid04_part683_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part683) = true := by rfl

def kid04_part684 : Audit := .cycle 11 1 false (1)
theorem kid04_part684_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part684) = true := by rfl

def kid04_part685 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.last 18 (2,true),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
])
theorem kid04_part685_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part685) = true := by rfl

def kid04_part686 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 15 1 false (-3),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 15 (4,true),
.cycle 0 31 true (-1),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 8 5 false (2),
.cycle 9 5 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 31 1 false (3),
.cycle 27 1 false (3),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 15 (4,true),
.last 26 (4,true),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3)
])
theorem kid04_part686_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part686) = true := by rfl

def kid04_part687 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 13 3 false (2),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.last 27 (2,true),
.cycle 1 15 true (-1),
.cycle 23 1 false (1),
.cycle 27 1 false (3),
.cycle 29 1 false (3),
.cycle 0 20 true (-1)
])
theorem kid04_part687_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part687) = true := by rfl

def kid04_part688 : Audit := .cycle 11 1 false (-1)
theorem kid04_part688_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part688) = true := by rfl

def kid04_part689 : Audit := .cycle 12 1 false (-2)
theorem kid04_part689_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part689) = true := by rfl

def kid04_part690 : Audit := .cycle 11 1 false (-1)
theorem kid04_part690_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part690) = true := by rfl

def kid04_part691 : Audit := .split 13 (4,true) (byMove [
.cycle 23 1 false (1),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 1 false (-2),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.last 27 (2,true),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 8 6 true (0),
.cycle 0 17 true (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 24 1 false (2),
.cycle 16 1 false (-2),
.last 29 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 33 true (0),
.last 30 (2,true),
.cycle 0 16 true (0)
])
theorem kid04_part691_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part691) = true := by rfl

def kid04_part692 : Audit := .split 12 (2,true) (byMove [
.cycle 0 28 true (0),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.cycle 1 15 true (0),
.last 18 (4,true),
.last 14 (4,true),
.cycle 20 1 false (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 2097152, 256, 524290, 32768, 128, 256, 32768, 524290, 262144, 256, 33554432, 67108864, 134217728, 1326227842, 1326227842, 1326227842, 1073741824],[2, 0, 0, 1, 1073741824, 128, 8192, 1073741824, 524290, 4096, 1073741824, 128, 524288, 1073741952, 256, 262144, 1073741824, 33554432, 8192, 256, 524290, 4096, 1073741824, 128, 33554432, 1326227842, 1326227842, 16777216, 1073741824, 33554432, 1073741824],2130719744⟩,
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 36 true (0),
.last 16 (4,true),
.cycle 1 14 true (0)
])
theorem kid04_part692_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part692) = true := by rfl

def kid04_part693 : Audit := .cycle 0 13 true (0)
theorem kid04_part693_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part693) = true := by rfl

def kid04_part694 : Audit := .cycle 16 1 false (0)
theorem kid04_part694_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part694) = true := by rfl

def kid04_part695 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 10 4 true (0),
.last 32 (2,true),
.last 33 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 14 6 true (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 12 2 true (0),
.cycle 0 32 true (0),
.cycle 1 15 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 3 true (2),
.cycle 14 5 true (2)
])
theorem kid04_part695_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part695) = true := by rfl

def kid04_part696 : Audit := .cycle 9 2 true (0)
theorem kid04_part696_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part696) = true := by rfl

def kid04_part672 : Audit := .split 10 (5,true) (byMove [(kid04_part673),(kid04_part674),(kid04_part675),(kid04_part676),(kid04_part677),(kid04_part678),(kid04_part679),(kid04_part680),(kid04_part681),(kid04_part682),(kid04_part683),(kid04_part684),(kid04_part685),(kid04_part686),(kid04_part687),(kid04_part688),(kid04_part689),(kid04_part690),(kid04_part691),(kid04_part692),(kid04_part693),(kid04_part694),(kid04_part695),(kid04_part696)])

theorem kid04_part672_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part672) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part673),(kid04_part674),(kid04_part675),(kid04_part676),(kid04_part677),(kid04_part678),(kid04_part679),(kid04_part680),(kid04_part681),(kid04_part682),(kid04_part683),(kid04_part684),(kid04_part685),(kid04_part686),(kid04_part687),(kid04_part688),(kid04_part689),(kid04_part690),(kid04_part691),(kid04_part692),(kid04_part693),(kid04_part694),(kid04_part695),(kid04_part696)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part673_checked

  · exact kid04_part679_checked

  · exact kid04_part685_checked

  · exact kid04_part691_checked

  · exact kid04_part674_checked

  · exact kid04_part680_checked

  · exact kid04_part686_checked

  · exact kid04_part692_checked

  · exact kid04_part675_checked

  · exact kid04_part681_checked

  · exact kid04_part687_checked

  · exact kid04_part693_checked

  · exact kid04_part676_checked

  · exact kid04_part682_checked

  · exact kid04_part688_checked

  · exact kid04_part694_checked

  · exact kid04_part677_checked

  · exact kid04_part683_checked

  · exact kid04_part689_checked

  · exact kid04_part695_checked

  · exact kid04_part678_checked

  · exact kid04_part684_checked

  · exact kid04_part690_checked

  · exact kid04_part696_checked

def kid04_part697 : Audit := .cycle 1 10 true (1)
theorem kid04_part697_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part697) = true := by rfl

def kid04_part699 : Audit := .split 15 (2,true) (byMove [
.cycle 7 19 false (3),
.last 17 (4,true),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.last 16 (4,true),
.cycle 24 3 false (2),
.cycle 0 16 true (-1),
.cycle 7 36 true (-1),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 8 16 true (-1),
.cycle 7 44 true (-1),
.cycle 10 7 false (2),
.last 17 (4,true),
.cycle 21 3 false (1),
.cycle 7 23 false (4),
.last 16 (4,true),
.cycle 12 8 true (-1),
.cycle 14 16 true (0),
.cycle 14 15 true (0),
.cycle 2 28 true (-1),
.cycle 7 48 true (-1),
.cycle 14 5 true (0),
.cycle 14 19 true (0)
])
theorem kid04_part699_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part699) = true := by rfl

def kid04_part700 : Audit := .cycle 0 16 true (-1)
theorem kid04_part700_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part700) = true := by rfl

def kid04_part701 : Audit := .cycle 14 1 false (0)
theorem kid04_part701_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part701) = true := by rfl

def kid04_part702 : Audit := .cycle 13 1 false (-1)
theorem kid04_part702_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part702) = true := by rfl

def kid04_part703 : Audit := .cycle 13 3 false (-1)
theorem kid04_part703_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part703) = true := by rfl

def kid04_part704 : Audit := .split 15 (2,true) (byMove [
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.cycle 18 1 false (0),
.cycle 0 17 true (-1),
.last 16 (4,true),
.cycle 24 3 false (2),
.cycle 0 16 true (-1),
.cycle 7 18 true (-1),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.cycle 8 8 true (-1),
.cycle 7 22 true (-1),
.cycle 17 3 false (1),
.cycle 16 3 false (0),
.cycle 26 3 false (4),
.cycle 24 3 false (4),
.last 16 (4,true),
.cycle 12 4 true (-1),
.cycle 38 3 false (2),
.cycle 0 33 true (-1),
.cycle 2 14 true (-1),
.cycle 7 24 true (-1),
.cycle 0 23 true (-1),
.cycle 0 37 true (-1)
])
theorem kid04_part704_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part704) = true := by rfl

def kid04_part705 : Audit := .cycle 20 3 false (4)
theorem kid04_part705_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part705) = true := by rfl

def kid04_part706 : Audit := .cycle 13 3 false (1)
theorem kid04_part706_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part706) = true := by rfl

def kid04_part707 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 21 3 false (3),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 3 false (2),
.cycle 21 3 false (5),
.last 16 (4,true),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 14 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 23 3 false (5),
.cycle 11 3 true (0),
.cycle 7 17 true (0)
])
theorem kid04_part707_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part707) = true := by rfl

def kid04_part708 : Audit := .cycle 0 14 true (0)
theorem kid04_part708_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part708) = true := by rfl

def kid04_part709 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 21 3 false (3),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 3 false (2),
.cycle 21 3 false (5),
.cycle 13 3 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 14 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 23 3 false (5),
.cycle 11 3 true (0),
.cycle 7 17 true (0)
])
theorem kid04_part709_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part709) = true := by rfl

def kid04_part710 : Audit := .cycle 21 3 false (5)
theorem kid04_part710_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part710) = true := by rfl

def kid04_part711 : Audit := .split 15 (4,true) (byMove [
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 3 false (-2),
.cycle 0 20 true (-2),
.cycle 0 19 true (-1),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 16 3 false (0),
.cycle 16 3 false (1),
.cycle 13 3 false (0),
.last 17 (2,true),
.cycle 0 23 true (-2),
.cycle 16 1 false (-2),
.cycle 16 3 false (-2),
.cycle 16 3 false (-1),
.last 44 (2,true),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 19 3 false (1),
.cycle 11 5 false (1),
.cycle 9 7 false (2)
])
theorem kid04_part711_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part711) = true := by rfl

def kid04_part712 : Audit := .split 14 (2,true) (byMove [
.cycle 25 3 false (3),
.cycle 15 3 false (-1),
.cycle 17 1 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 7 21 false (4),
.cycle 10 5 false (2),
.cycle 23 3 false (1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 37 3 false (-1),
.cycle 16 3 false (0),
.cycle 15 3 false (-1),
.cycle 19 3 false (1),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 31 3 false (-1),
.last 16 (4,true),
.cycle 27 3 false (-1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.last 17 (4,true)
])
theorem kid04_part712_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part712) = true := by rfl

def kid04_part713 : Audit := .cycle 22 3 false (4)
theorem kid04_part713_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part713) = true := by rfl

def kid04_part714 : Audit := .cycle 13 1 false (-1)
theorem kid04_part714_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part714) = true := by rfl

def kid04_part715 : Audit := .cycle 13 3 false (-1)
theorem kid04_part715_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part715) = true := by rfl

def kid04_part716 : Audit := .cycle 13 3 false (0)
theorem kid04_part716_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part716) = true := by rfl

def kid04_part717 : Audit := .cycle 7 16 true (0)
theorem kid04_part717_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part717) = true := by rfl

def kid04_part718 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (-1),
.cycle 22 3 false (2),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (1),
.cycle 22 3 false (4),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (-1),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 24 3 false (4),
.cycle 11 4 true (0),
.cycle 7 18 true (0)
])
theorem kid04_part718_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part718) = true := by rfl

def kid04_part719 : Audit := .split 13 (2,true) (byMove [
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 20 3 false (2),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 8 6 true (0),
.cycle 7 20 true (0),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.cycle 24 3 false (4),
.cycle 22 3 false (4),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 22 true (0),
.cycle 11 3 true (0),
.cycle 7 17 true (0)
])
theorem kid04_part719_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part719) = true := by rfl

def kid04_part720 : Audit := .cycle 0 14 true (0)
theorem kid04_part720_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part720) = true := by rfl

def kid04_part721 : Audit := .split 13 (4,true) (byMove [
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 3 false (-1),
.cycle 11 4 true (0),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 8 6 true (0),
.cycle 7 20 true (0),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.last 14 (2,true),
.cycle 22 3 false (4),
.cycle 15 3 false (-1),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 22 true (0),
.cycle 11 3 true (0),
.cycle 7 17 true (0)
])
theorem kid04_part721_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part721) = true := by rfl

def kid04_part722 : Audit := .cycle 7 17 true (0)
theorem kid04_part722_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part722) = true := by rfl

def kid04_part698 : Audit := .split 12 (5,true) (byMove [(kid04_part699),(kid04_part700),(kid04_part701),(kid04_part702),(kid04_part703),(kid04_part704),(kid04_part705),(kid04_part706),(kid04_part707),(kid04_part708),(kid04_part709),(kid04_part710),(kid04_part711),(kid04_part712),(kid04_part713),(kid04_part714),(kid04_part715),(kid04_part716),(kid04_part717),(kid04_part718),(kid04_part719),(kid04_part720),(kid04_part721),(kid04_part722)])

theorem kid04_part698_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part698) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (5,true) (some mv)) (byMove [(kid04_part699),(kid04_part700),(kid04_part701),(kid04_part702),(kid04_part703),(kid04_part704),(kid04_part705),(kid04_part706),(kid04_part707),(kid04_part708),(kid04_part709),(kid04_part710),(kid04_part711),(kid04_part712),(kid04_part713),(kid04_part714),(kid04_part715),(kid04_part716),(kid04_part717),(kid04_part718),(kid04_part719),(kid04_part720),(kid04_part721),(kid04_part722)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part699_checked

  · exact kid04_part705_checked

  · exact kid04_part711_checked

  · exact kid04_part717_checked

  · exact kid04_part700_checked

  · exact kid04_part706_checked

  · exact kid04_part712_checked

  · exact kid04_part718_checked

  · exact kid04_part701_checked

  · exact kid04_part707_checked

  · exact kid04_part713_checked

  · exact kid04_part719_checked

  · exact kid04_part702_checked

  · exact kid04_part708_checked

  · exact kid04_part714_checked

  · exact kid04_part720_checked

  · exact kid04_part703_checked

  · exact kid04_part709_checked

  · exact kid04_part715_checked

  · exact kid04_part721_checked

  · exact kid04_part704_checked

  · exact kid04_part710_checked

  · exact kid04_part716_checked

  · exact kid04_part722_checked

def kid04_part723 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 0 16 true (-1),
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 16 1 false (4),
.last 15 (4,true),
.last 15 (4,true),
.cycle 23 3 false (3),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 8 16 true (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 31 true (0)
]),
.cycle 24 1 false (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 20 1 false (2),
.cycle 8 3 true (1),
.split 26 (5,true) (byMove [
.cycle 0 45 true (0),
.cycle 0 30 true (0),
.cycle 28 1 false (4),
.cycle 27 1 false (3),
.cycle 34 1 false (8),
.cycle 0 30 true (0),
.cycle 40 1 false (10),
.cycle 33 1 false (7),
.cycle 30 1 false (8),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 30 1 false (8),
.last 29 (4,true),
.cycle 28 17 true (4),
.cycle 42 1 false (10),
.cycle 27 1 false (3),
.cycle 24 4 true (2),
.cycle 34 1 false (8),
.cycle 26 32 true (4),
.last 28 (4,true),
.cycle 54 1 false (12),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 26 34 true (4)
]),
.split 13 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 48 1 false (8),
.cycle 19 3 false (0),
.cycle 14 10 false (0),
.cycle 0 25 true (-2),
.cycle 29 1 false (1),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 0 31 true (0)
]),
.split 14 (4,true) (byMove [
.cycle 0 19 true (-1),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 6 false (-1),
.cycle 17 1 false (1),
.cycle 0 18 true (0),
.cycle 15 6 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 15 6 false (1),
.cycle 15 6 false (2),
.cycle 13 3 false (1),
.cycle 15 6 false (0),
.cycle 0 22 true (-1),
.cycle 15 1 false (-1),
.cycle 15 6 false (-1),
.cycle 15 6 false (0),
.cycle 0 18 true (0),
.cycle 11 4 true (0),
.cycle 0 17 true (0),
.cycle 18 6 false (2),
.last 16 (5,true),
.cycle 9 6 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 30 13 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 24 3 false (4),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.cycle 13 3 false (1),
.cycle 22 3 false (4),
.last 13 (4,true),
.cycle 17 1 false (5),
.last 15 (4,true),
.last 15 (4,true),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.last 40 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.last 45 (4,true),
.last 13 (4,true),
.cycle 9 21 true (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.cycle 14 5 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 23 (4,true),
.cycle 13 5 false (1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 37 1 false (9),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 18 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 12 15 true (2)
]),
.cycle 9 13 true (1)
])
theorem kid04_part723_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part723) = true := by rfl

def kid04_part724 : Audit := .cycle 0 11 true (0)
theorem kid04_part724_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part724) = true := by rfl

def kid04_part725 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 14 3 false (0),
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.cycle 15 3 false (3),
.cycle 15 3 false (-1),
.last 14 (2,true),
.cycle 23 3 false (3),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 8 16 true (0),
.cycle 14 3 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.cycle 8 7 true (0)
]),
.cycle 8 4 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 20 1 false (2),
.cycle 8 3 true (1),
.cycle 8 4 true (1),
.cycle 18 3 false (0),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 14 6 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 17 3 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 8 6 true (1),
.last 16 (5,true),
.cycle 14 6 false (0),
.cycle 16 16 true (-1),
.cycle 1 14 true (1),
.cycle 17 3 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 8 6 true (1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 30 13 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 14 3 false (0),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.last 13 (2,true),
.cycle 22 3 false (4),
.cycle 13 3 false (1),
.cycle 16 3 false (4),
.cycle 15 3 false (-1),
.last 14 (2,true),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.last 39 (2,true),
.cycle 14 3 false (0),
.last 13 (2,true),
.last 44 (2,true),
.cycle 14 3 false (0),
.cycle 8 8 true (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 17 (2,true),
.cycle 13 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 8 7 true (1),
.cycle 22 5 false (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 19 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 10 4 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 8 7 true (1)
]),
.cycle 8 4 true (1)
])
theorem kid04_part725_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part725) = true := by rfl

def kid04_part726 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 12 3 false (0),
.cycle 11 1 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 20 1 false (2),
.cycle 8 3 true (1),
.cycle 11 1 true (3),
.split 13 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.cycle 18 1 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 14 1 true (2),
.cycle 19 3 false (0),
.last 22 (2,true),
.last 14 (2,true),
.cycle 29 1 false (1),
.cycle 14 6 false (0),
.cycle 14 5 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 20 5 false (0),
.cycle 14 1 true (2)
]),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 3 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 13 1 true (3),
.cycle 16 7 false (0),
.last 14 (4,true),
.cycle 16 16 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 3 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.cycle 13 1 true (3)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 12 3 false (0),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 7 false (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 27 (2,true),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 14 1 true (4),
.cycle 6 8 true (1),
.cycle 15 7 false (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 16 5 false (1),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (2),
.cycle 14 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid04_part726_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part726) = true := by rfl

def kid04_part728 : Audit := .split 41 (5,true) (byMove [
.last 44 (2,true),
.cycle 6 52 false (3),
.cycle 43 1 false (-3),
.cycle 42 1 false (-4),
.cycle 12 30 false (3),
.cycle 0 46 false (3),
.last 44 (2,true),
.last 54 (2,true),
.last 42 (2,true),
.cycle 0 46 false (3),
.cycle 16 26 true (-3),
.cycle 13 30 true (-3),
.cycle 14 28 false (3),
.last 43 (2,true),
.last 46 (2,true),
.cycle 42 1 false (-4),
.last 64 (2,true),
.last 52 (2,true),
.last 44 (2,true),
.cycle 0 44 false (3),
.last 42 (2,true),
.cycle 34 18 true (-3),
.cycle 6 54 false (3),
.cycle 37 6 true (-3)
])
theorem kid04_part728_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part728) = true := by rfl

def kid04_part729 : Audit := .cycle 10 12 false (1)
theorem kid04_part729_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part729) = true := by rfl

def kid04_part730 : Audit := .cycle 18 1 false (-2)
theorem kid04_part730_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part730) = true := by rfl

def kid04_part731 : Audit := .cycle 17 1 false (-3)
theorem kid04_part731_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part731) = true := by rfl

def kid04_part732 : Audit := .cycle 12 5 false (0)
theorem kid04_part732_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part732) = true := by rfl

def kid04_part733 : Audit := .cycle 13 4 false (-1)
theorem kid04_part733_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part733) = true := by rfl

def kid04_part734 : Audit := .split 22 (2,true) (byMove [
.cycle 0 39 true (-2),
.cycle 0 25 true (-2),
.cycle 26 1 false (0),
.far true 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 3, 0, 1],[2048, 262144, 2097152, 512, 2048, 64, 262144, 262144, 0, 2097152, 8388608, 262144, 2048, 0, 2097152, 512, 2048, 64, 0, 0, 0, 2097152, 8388608, 262144, 0, 0, 2097152, 512, 2048, 64, 1073741824],[0, 16, 8, 262144, 262144, 1073741824, 2048, 65536, 32768, 0, 0, 1073741824, 0, 16, 8, 0, 0, 1073741824, 2048, 268435456, 134217728, 262144, 262144, 1073741824, 0, 16, 8, 0, 0, 1073741824, 1073741824],1073741824⟩,
.far true 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 3, 0, 1],[2048, 262144, 2097152, 512, 2048, 64, 262144, 262144, 0, 2097152, 8388608, 262144, 2048, 0, 2097152, 512, 2048, 64, 0, 0, 0, 2097152, 8388608, 262144, 0, 0, 2097152, 512, 2048, 64, 1073741824],[0, 16, 16, 262144, 262144, 1073741824, 2048, 65536, 65536, 0, 0, 1073741824, 0, 16, 16, 0, 0, 1073741824, 2048, 268435456, 268435456, 262144, 262144, 1073741824, 0, 16, 16, 0, 0, 1073741824, 1073741824],1073741824⟩,
.last 23 (5,true),
.last 40 (5,true),
.cycle 0 38 true (-2),
.cycle 0 47 true (-2),
.cycle 3 20 true (-2),
.last 28 (5,true),
.last 44 (5,true),
.last 26 (5,true),
.cycle 0 28 true (-2),
.cycle 0 37 true (-2),
.cycle 0 40 true (-2),
.cycle 0 40 true (-2),
.last 23 (5,true),
.last 36 (5,true),
.last 35 (5,true),
.last 34 (5,true),
.cycle 0 41 true (-2),
.last 24 (5,true),
.last 27 (5,true)
])
theorem kid04_part734_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part734) = true := by rfl

def kid04_part735 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (-2),
.cycle 11 8 false (1),
.cycle 21 1 false (-1),
.far true 2 ⟨0,[0, 1, 0, 1],[2048, 64, 512, 512, 2048, 64, 0, 64, 0, 512, 2048, 64, 4096],[0, 16, 8, 64, 0, 4096, 2048, 16, 8, 64, 2048, 4096, 4096],4096⟩,
.cycle 0 23 true (-2),
.last 19 (5,true),
.cycle 0 65 true (-2),
.cycle 19 14 true (1),
.cycle 0 21 true (-2),
.cycle 10 12 true (-2),
.cycle 8 11 false (2),
.cycle 19 18 true (0),
.cycle 10 9 false (1),
.cycle 11 8 false (1),
.cycle 23 18 true (0),
.cycle 21 16 true (1),
.cycle 11 9 false (1),
.last 19 (5,true),
.last 49 (5,true),
.last 33 (5,true),
.cycle 0 21 true (-2),
.cycle 4 15 false (3),
.last 20 (5,true),
.last 23 (5,true)
])
theorem kid04_part735_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part735) = true := by rfl

def kid04_part736 : Audit := .cycle 23 1 false (3)
theorem kid04_part736_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part736) = true := by rfl

def kid04_part737 : Audit := .cycle 17 1 false (-1)
theorem kid04_part737_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part737) = true := by rfl

def kid04_part738 : Audit := .cycle 12 5 false (0)
theorem kid04_part738_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part738) = true := by rfl

def kid04_part739 : Audit := .cycle 13 4 true (-2)
theorem kid04_part739_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part739) = true := by rfl

def kid04_part740 : Audit := .cycle 14 3 false (-1)
theorem kid04_part740_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part740) = true := by rfl

def kid04_part741 : Audit := .split 18 (2,true) (byMove [
.last 66 (5,true),
.cycle 11 8 false (1),
.cycle 21 1 false (-3),
.far true 2 ⟨0,[0, 1, 0, 1],[2176, 80, 512, 512, 2048, 64, 128, 64, 128, 512, 2048, 64, 4096],[2176, 16, 8, 64, 128, 4096, 2048, 16, 8, 64, 128, 4096, 4096],4096⟩,
.cycle 16 3 false (-2),
.last 19 (5,true),
.last 44 (5,true),
.last 37 (5,true),
.cycle 10 21 true (-3),
.cycle 10 12 false (1),
.cycle 8 11 false (2),
.cycle 11 12 false (1),
.cycle 10 9 false (1),
.cycle 11 8 false (1),
.cycle 23 24 true (-2),
.cycle 21 20 true (-1),
.cycle 16 3 false (-2),
.last 19 (5,true),
.cycle 15 7 false (0),
.last 35 (5,true),
.last 41 (5,true),
.cycle 4 15 false (3),
.last 20 (5,true),
.last 23 (5,true)
])
theorem kid04_part741_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part741) = true := by rfl

def kid04_part742 : Audit := .split 26 (2,true) (byMove [
.cycle 0 78 true (-3),
.cycle 0 31 true (-3),
.cycle 30 1 false (0),
.far true 2 ⟨0,[0, 1, 0, 1],[2888, 840, 512, 512, 2048, 64, 256, 832, 768, 512, 2048, 64, 4096],[768, 16, 8, 832, 256, 4096, 2048, 16, 8, 832, 256, 4096, 4096],4096⟩,
.cycle 12 17 false (2),
.last 27 (5,true),
.last 44 (5,true),
.last 42 (5,true),
.cycle 0 55 true (-3),
.cycle 3 24 true (-3),
.last 32 (5,true),
.last 32 (5,true),
.last 30 (5,true),
.cycle 0 36 true (-3),
.cycle 0 45 true (-3),
.cycle 0 48 true (-3),
.cycle 0 56 true (-4),
.last 27 (5,true),
.last 40 (5,true),
.last 39 (5,true),
.last 38 (5,true),
.cycle 0 49 true (-3),
.last 28 (5,true),
.last 31 (5,true)
])
theorem kid04_part742_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part742) = true := by rfl

def kid04_part743 : Audit := .cycle 17 1 false (-3)
theorem kid04_part743_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part743) = true := by rfl

def kid04_part744 : Audit := .cycle 12 5 false (0)
theorem kid04_part744_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part744) = true := by rfl

def kid04_part745 : Audit := .cycle 13 4 false (-1)
theorem kid04_part745_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part745) = true := by rfl

def kid04_part746 : Audit := .split 22 (2,true) (byMove [
.last 52 (5,true),
.last 38 (5,true),
.cycle 28 1 false (-2),
.last 41 (5,true),
.last 37 (5,true),
.last 23 (5,true),
.last 40 (5,true),
.last 51 (5,true),
.last 35 (5,true),
.last 33 (5,true),
.last 28 (5,true),
.last 40 (5,true),
.last 26 (5,true),
.last 41 (5,true),
.cycle 10 19 false (2),
.last 53 (5,true),
.last 53 (5,true),
.last 23 (5,true),
.last 36 (5,true),
.last 35 (5,true),
.last 34 (5,true),
.last 54 (5,true),
.last 24 (5,true),
.last 27 (5,true)
])
theorem kid04_part746_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part746) = true := by rfl

def kid04_part747 : Audit := .split 18 (2,true) (byMove [
.cycle 0 23 true (-2),
.cycle 1 20 false (3),
.cycle 22 1 false (-2),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 128, 1048576, 524288, 1048576, 32768, 8796093022210, 18014398509481984, 1048576, 128, 256, 134217728, 22268348868853888, 128, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 18014398509481984, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 22268348868853888, 22268348868853888, 1048576, 137438953472, 274877906944, 35184372088832, 1048576, 18014398509481984, 22268348868853888, 562949953421312, 1125899906842624, 549755813888, 22268348868853888, 22268348868853888, 22268348868853888, 8796093022208, 17592186044416, 549755813888, 22268348868853888, 22268348868853888, 22268348868853888, 137438953472, 274877906944, 2251799813685248, 22268348868853888, 22268348868853888, 22268348868853888, 18014398509481984],[2, 1048576, 0, 1, 128, 18014398509481984, 8192, 1048576, 8796093022336, 4096, 524288, 18014398509481984, 33554432, 18014398509481984, 17592186044672, 16777216, 128, 18014398509481984, 2147483648, 274877906944, 128, 1073741824, 137438953472, 18014398509481984, 8796093022208, 1048576, 22268348868853888, 4398046511104, 8796093022208, 18014398509481984, 8796093022208, 18014398509481984, 17592186044416, 4398046511104, 137438953472, 18014398509481984, 137438953472, 22268348868853888, 22268348868853888, 68719476736, 562949953421312, 18014398509481984, 137438953472, 22268348868853888, 22268348868853888, 68719476736, 8796093022208, 18014398509481984, 562949953421312, 22268348868853888, 22268348868853888, 281474976710656, 137438953472, 18014398509481984, 18014398509481984],36028787891038018⟩,
.cycle 0 23 true (-2),
.last 19 (5,true),
.last 38 (5,true),
.cycle 19 14 true (1),
.cycle 0 21 true (-2),
.cycle 3 16 false (3),
.last 24 (5,true),
.last 41 (5,true),
.last 22 (5,true),
.cycle 15 4 true (-2),
.cycle 10 13 false (1),
.cycle 21 16 true (1),
.cycle 0 25 true (-2),
.last 19 (5,true),
.last 34 (5,true),
.last 33 (5,true),
.cycle 0 21 true (-2),
.last 28 (5,true),
.last 20 (5,true),
.last 23 (5,true)
])
theorem kid04_part747_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part747) = true := by rfl

def kid04_part748 : Audit := .cycle 0 35 true (-2)
theorem kid04_part748_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part748) = true := by rfl

def kid04_part749 : Audit := .cycle 10 9 false (1)
theorem kid04_part749_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part749) = true := by rfl

def kid04_part750 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.last 24 (2,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 12 7 false (0),
.cycle 13 6 false (-1),
.cycle 10 9 false (1),
.cycle 11 8 false (1),
.last 19 (2,true),
.last 22 (2,true),
.cycle 24 3 true (2),
.cycle 27 7 true (1),
.cycle 14 5 false (-1),
.last 20 (2,true),
.cycle 10 11 false (1),
.cycle 19 1 false (-3),
.cycle 12 7 false (0),
.cycle 13 6 false (-1),
.cycle 0 27 true (-2),
.cycle 15 4 true (-2),
.last 19 (2,true),
.last 22 (2,true),
.cycle 24 3 true (2),
.cycle 19 6 true (-1)
])
theorem kid04_part750_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part750) = true := by rfl

def kid04_part751 : Audit := .cycle 9 8 false (1)
theorem kid04_part751_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part751) = true := by rfl

def kid04_part727 : Audit := .split 16 (4,true) (byMove [(kid04_part728),(kid04_part729),(kid04_part730),(kid04_part731),(kid04_part732),(kid04_part733),(kid04_part734),(kid04_part735),(kid04_part736),(kid04_part737),(kid04_part738),(kid04_part739),(kid04_part740),(kid04_part741),(kid04_part742),(kid04_part743),(kid04_part744),(kid04_part745),(kid04_part746),(kid04_part747),(kid04_part748),(kid04_part749),(kid04_part750),(kid04_part751)])

theorem kid04_part727_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part727) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 16 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some mv)) (byMove [(kid04_part728),(kid04_part729),(kid04_part730),(kid04_part731),(kid04_part732),(kid04_part733),(kid04_part734),(kid04_part735),(kid04_part736),(kid04_part737),(kid04_part738),(kid04_part739),(kid04_part740),(kid04_part741),(kid04_part742),(kid04_part743),(kid04_part744),(kid04_part745),(kid04_part746),(kid04_part747),(kid04_part748),(kid04_part749),(kid04_part750),(kid04_part751)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part728_checked

  · exact kid04_part734_checked

  · exact kid04_part740_checked

  · exact kid04_part746_checked

  · exact kid04_part729_checked

  · exact kid04_part735_checked

  · exact kid04_part741_checked

  · exact kid04_part747_checked

  · exact kid04_part730_checked

  · exact kid04_part736_checked

  · exact kid04_part742_checked

  · exact kid04_part748_checked

  · exact kid04_part731_checked

  · exact kid04_part737_checked

  · exact kid04_part743_checked

  · exact kid04_part749_checked

  · exact kid04_part732_checked

  · exact kid04_part738_checked

  · exact kid04_part744_checked

  · exact kid04_part750_checked

  · exact kid04_part733_checked

  · exact kid04_part739_checked

  · exact kid04_part745_checked

  · exact kid04_part751_checked

def kid04_part753 : Audit := .cycle 22 15 true (2)
theorem kid04_part753_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part753) = true := by rfl

def kid04_part754 : Audit := .cycle 10 5 false (0)
theorem kid04_part754_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part754) = true := by rfl

def kid04_part755 : Audit := .cycle 17 1 false (-3)
theorem kid04_part755_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part755) = true := by rfl

def kid04_part756 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 false (3),
.cycle 10 15 false (0),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 11 8 false (-1),
.cycle 0 23 false (3),
.proven (BB6.Agent11Raw39B0RBPumps.M142.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M142.never m hm),
.cycle 23 15 true (2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 11 8 true (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M143.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M143.never m hm),
.cycle 16 3 false (-1),
.cycle 0 45 true (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M144.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M144.never m hm),
.cycle 19 1 false (-3),
.cycle 11 8 false (-1),
.cycle 12 7 false (-1),
.cycle 23 18 true (1),
.cycle 1 37 true (-3),
.cycle 10 14 true (-3),
.cycle 22 18 true (0),
.last 20 (5,true),
.cycle 9 10 false (1)
])
theorem kid04_part756_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part756) = true := by rfl

def kid04_part757 : Audit := .split 15 (4,true) (byMove [
.cycle 22 27 true (-2),
.cycle 10 12 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.proven (BB6.Agent11Raw39B0RBPumps.M145.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M145.never m hm),
.cycle 23 15 true (2),
.cycle 0 23 true (-3),
.cycle 16 1 false (-2),
.cycle 11 5 false (-1),
.cycle 12 4 true (-3),
.cycle 15 3 false (-3),
.cycle 13 3 false (-2),
.cycle 11 17 false (1),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 22 18 true (0),
.cycle 32 17 true (2),
.far false 10 ⟨0,[0, 9, 3, 2, 3, 2, 2, 3, 1, 9, 3, 1, 1, 3, 6, 5, 4, 1, 8, 7],[36028797018963968, 72057594037927936, 8, 0, 16777216, 2251799813685248, 8192, 16384, 2097152, 1191220243402125504, 1191220243402125504, 1191220243402125504, 8192, 16384, 2097152, 1191220243402125504, 1191220243402125504, 1191220243402125504, 524288, 1048576, 32768, 1191220243402125504, 1191220243402125504, 1191220243402125504, 36028797018963968, 72057594037927936, 512, 1191220243402125504, 64, 2121728, 128, 256, 2097152, 128, 1152921504606846976, 64, 524288, 1048576, 512, 36028797018963968, 128, 2097152, 2147483648, 4294967296, 549755813888, 33554432, 1152921504606846976, 16777216, 128, 256, 134217728, 1191220243402125504, 16777216, 549755813888, 8796093022208, 17592186044416, 2251799813685248, 524290, 1152921504606846976, 2251799813685248, 1152921504606846976],[2, 36028797018963968, 36028797018963968, 1, 72057594037927936, 1152921504606846976, 524288, 2121728, 2121728, 262144, 16384, 1152921504606846976, 524288, 1191220243402125504, 1191220243402125504, 262144, 16384, 1152921504606846976, 8192, 1191220243402125504, 1191220243402125504, 4096, 1048576, 1152921504606846976, 128, 36028797018963968, 36028797018963968, 64, 72057594037927936, 1152921504606846976, 524288, 2097152, 2097152, 262144, 256, 1152921504606846976, 128, 1152921504606846976, 1152921504606846976, 64, 1048576, 1152921504606846976, 137438953472, 549755813888, 549755813888, 68719476736, 4294967296, 1152921504606846976, 33554432, 1152921504606846976, 1152921504606846976, 16777216, 256, 1152921504606846976, 562949953421312, 2251799813685248, 2251799813685248, 281474976710656, 17592186044416, 1152921504606846976, 1152921504606846976],2256144533865627618⟩,
.cycle 10 9 false (0),
.last 17 (5,true),
.cycle 9 7 false (1)
])
theorem kid04_part757_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part757) = true := by rfl

def kid04_part758 : Audit := .split 15 (5,true) (byMove [
.last 22 (4,true),
.cycle 10 12 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 18 (4,true),
.cycle 23 15 true (2),
.last 20 (4,true),
.cycle 16 1 false (-2),
.cycle 11 5 false (-1),
.cycle 12 4 true (-3),
.last 18 (4,true),
.cycle 13 3 false (-2),
.last 20 (4,true),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 18 (4,true),
.last 48 (4,true),
.last 20 (4,true),
.cycle 10 9 false (0),
.last 18 (4,true),
.cycle 9 7 false (1)
])
theorem kid04_part758_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part758) = true := by rfl

def kid04_part759 : Audit := .cycle 16 12 true (0)
theorem kid04_part759_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part759) = true := by rfl

def kid04_part760 : Audit := .split 17 (5,true) (byMove [
.cycle 40 17 true (2),
.cycle 7 20 false (3),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.last 63 (4,true),
.cycle 22 15 true (2),
.cycle 10 8 false (0),
.cycle 23 15 true (2),
.far false 8 ⟨0,[0, 1, 2, 3, 4, 3, 5, 6, 4, 1, 6, 6, 7, 6, 6, 6],[128, 256, 8, 0, 128, 8192, 524288, 1048576, 32768, 33554434, 16777217, 2147483648, 524288, 1048576, 134217728, 1048576, 128, 2147483648, 137438953472, 274877906944, 8589934592, 33554432, 16777216, 281474976710656, 128, 256, 134217728, 281477124194432, 128, 2147491840, 137438953472, 274877906944, 549755813888, 1048576, 281474976710656, 8796093022208, 137438953472, 274877906944, 35184372088832, 325947216625792, 330345263136896, 325947216625792, 137438953472, 274877906944, 549755813888, 325947216625792, 325947216625792, 8796093022208, 281474976710656],[2, 1048576, 2, 1, 281474976710656, 8, 8192, 281474976710656, 8192, 4096, 281474976710656, 32768, 33554432, 128, 33554432, 16777216, 281474976710656, 134217728, 2147483648, 281474976710656, 2147483648, 1073741824, 281474976710656, 8589934592, 33554432, 1048576, 33554432, 16777216, 281474976710656, 134217728, 137438953472, 128, 137438953472, 68719476736, 281474976710656, 549755813888, 8796093022208, 325947216625792, 8796093022208, 4398046511104, 281474976710656, 35184372088832, 137438953472, 325947216625792, 137438953472, 68719476736, 281474976710656, 549755813888, 281474976710656],562941037271104⟩,
.last 18 (4,true),
.cycle 22 18 true (0),
.last 20 (4,true),
.cycle 13 5 false (-1),
.cycle 22 17 true (0),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.cycle 12 6 false (-1),
.cycle 22 15 true (2),
.last 19 (4,true),
.cycle 23 15 true (2),
.last 42 (4,true),
.last 18 (4,true),
.last 21 (4,true)
])
theorem kid04_part760_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part760) = true := by rfl

def kid04_part761 : Audit := .cycle 10 28 true (-3)
theorem kid04_part761_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part761) = true := by rfl

def kid04_part762 : Audit := .split 18 (4,true) (byMove [
.cycle 15 56 true (-2),
.cycle 88 61 true (-1),
.cycle 10 15 false (1),
.last 152 (5,true),
.cycle 8 11 false (2),
.cycle 3 19 false (3),
.cycle 0 22 true (-3),
.proven (BB6.Agent11Raw39B0RBPumps.M148.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M148.never m hm),
.cycle 0 21 true (-3),
.cycle 10 15 false (1),
.last 55 (5,true),
.proven (BB6.Agent11Raw39B0RBPumps.M149.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M149.never m hm),
.cycle 7 35 false (3),
.cycle 61 78 true (-6),
.cycle 0 26 true (-3),
.cycle 10 13 false (1),
.cycle 8 11 false (2),
.last 45 (5,true),
.cycle 16 18 true (0),
.cycle 7 21 false (3),
.far false 10 ⟨0,[0, 9, 3, 2, 3, 2, 2, 3, 1, 9, 3, 1, 1, 3, 6, 5, 4, 1, 8, 7],[36028797018963968, 72057594037927936, 8, 0, 16777216, 2251799813685248, 8192, 16384, 2097152, 1191220243402125504, 1152921504606851072, 1155173304420569088, 8192, 16384, 2097152, 1191220243402125504, 1191220243402125504, 1191220243402125504, 524288, 1048576, 32768, 1191220243402125504, 1191220243402125504, 1191220243402125504, 36028797018963968, 72057594037927936, 512, 1191220243402125504, 64, 2097152, 128, 256, 2097152, 128, 1152921504606846976, 64, 524288, 1048576, 512, 36028797018963968, 128, 2097152, 2147483648, 4294967296, 549755813888, 33554432, 1152921504606846976, 16777216, 128, 256, 134217728, 1191220243402125504, 16777216, 549755813888, 8796093022208, 17592186044416, 2251799813685248, 524290, 1152921504606846976, 2251799813685248, 1152921504606846976],[2, 36028797018963968, 8, 1, 72057594037927936, 1152921504606846976, 524288, 2121728, 2097152, 262144, 16384, 1152921504606846976, 524288, 1191220243402125504, 2097152, 262144, 16384, 1152921504606846976, 8192, 1191220243402125504, 32768, 4096, 1048576, 1152921504606846976, 128, 36028797018963968, 512, 64, 72057594037927936, 1152921504606846976, 524288, 2097152, 2097152, 262144, 256, 1152921504606846976, 128, 1152921504606846976, 512, 64, 1048576, 1152921504606846976, 137438953472, 549755813888, 549755813888, 68719476736, 4294967296, 1152921504606846976, 33554432, 1152921504606846976, 134217728, 16777216, 256, 1152921504606846976, 562949953421312, 2251799813685248, 2251799813685248, 281474976710656, 17592186044416, 1152921504606846976, 1152921504606846976],2256144533865627618⟩,
.last 43 (5,true),
.last 20 (5,true),
.cycle 7 13 false (3)
])
theorem kid04_part762_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part762) = true := by rfl

def kid04_part763 : Audit := .split 15 (4,true) (byMove [
.cycle 15 29 true (-2),
.cycle 1 15 false (3),
.cycle 10 11 false (0),
.cycle 21 15 true (1),
.last 17 (5,true),
.cycle 9 7 false (1),
.cycle 0 22 true (-3),
.cycle 16 12 true (0),
.cycle 10 28 true (-3),
.cycle 10 11 false (0),
.cycle 22 5 true (1),
.last 20 (5,true),
.cycle 10 10 false (0),
.cycle 8 16 false (2),
.cycle 0 28 true (-3),
.cycle 10 9 false (0),
.last 17 (5,true),
.cycle 9 7 false (1),
.cycle 15 18 true (-1),
.last 30 (5,true),
.cycle 20 11 true (2),
.cycle 25 15 true (-1),
.last 17 (5,true),
.last 19 (5,true)
])
theorem kid04_part763_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part763) = true := by rfl

def kid04_part764 : Audit := .split 15 (5,true) (byMove [
.last 44 (4,true),
.cycle 1 15 false (3),
.cycle 10 11 false (0),
.cycle 21 15 true (1),
.cycle 11 7 false (-1),
.cycle 9 7 false (1),
.last 18 (4,true),
.cycle 16 12 true (0),
.cycle 10 28 true (-3),
.cycle 10 11 false (0),
.last 21 (4,true),
.cycle 21 3 true (2),
.last 18 (4,true),
.cycle 25 3 true (1),
.last 20 (4,true),
.cycle 10 9 false (0),
.cycle 11 7 false (-1),
.cycle 9 7 false (1),
.last 18 (4,true),
.last 32 (4,true),
.cycle 20 11 true (2),
.cycle 25 15 true (-1),
.last 18 (4,true),
.last 23 (4,true)
])
theorem kid04_part764_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part764) = true := by rfl

def kid04_part765 : Audit := .cycle 10 6 false (0)
theorem kid04_part765_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part765) = true := by rfl

def kid04_part766 : Audit := .cycle 10 5 false (0)
theorem kid04_part766_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part766) = true := by rfl

def kid04_part767 : Audit := .cycle 10 9 false (0)
theorem kid04_part767_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part767) = true := by rfl

def kid04_part768 : Audit := .cycle 10 7 false (0)
theorem kid04_part768_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part768) = true := by rfl

def kid04_part769 : Audit := .split 15 (4,true) (byMove [
.cycle 13 8 true (-4),
.cycle 20 16 true (-1),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 10 7 false (0),
.cycle 10 6 false (0),
.cycle 11 6 false (-1),
.cycle 18 14 true (0),
.cycle 24 7 true (0),
.last 16 (5,true),
.cycle 15 3 false (-3),
.cycle 13 3 false (-2),
.cycle 10 9 false (0),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 19 (5,true),
.cycle 36 21 true (2),
.cycle 14 2 true (-3),
.cycle 18 14 true (0),
.last 19 (5,true),
.last 16 (5,true)
])
theorem kid04_part769_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part769) = true := by rfl

def kid04_part770 : Audit := .split 15 (5,true) (byMove [
.cycle 13 8 true (-4),
.cycle 20 16 true (-1),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 10 7 false (0),
.cycle 10 6 false (0),
.cycle 12 5 false (-2),
.cycle 18 14 true (0),
.last 16 (4,true),
.cycle 23 5 true (1),
.last 18 (4,true),
.cycle 13 3 false (-2),
.cycle 10 9 false (0),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 24 17 true (2),
.last 17 (4,true),
.cycle 14 2 true (-3),
.cycle 18 14 true (0),
.last 16 (4,true),
.last 20 (4,true)
])
theorem kid04_part770_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part770) = true := by rfl

def kid04_part771 : Audit := .cycle 16 12 true (0)
theorem kid04_part771_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part771) = true := by rfl

def kid04_part772 : Audit := .split 16 (4,true) (byMove [
.cycle 10 14 true (-3),
.cycle 10 7 false (0),
.cycle 1 17 false (3),
.cycle 0 37 true (-3),
.cycle 11 7 false (-1),
.last 17 (5,true),
.last 34 (5,true),
.cycle 21 13 true (2),
.cycle 10 13 false (0),
.cycle 10 11 false (0),
.cycle 8 9 false (2),
.cycle 20 24 true (0),
.cycle 10 8 false (0),
.cycle 10 7 false (0),
.far true 2 ⟨0,[0, 1, 0, 1],[272, 400, 512, 512, 2048, 128, 256, 256, 384, 512, 2048, 128, 4096],[2432, 16, 272, 2432, 256, 4096, 2048, 16, 256, 384, 256, 4096, 4096],4096⟩,
.cycle 21 15 true (1),
.cycle 11 7 false (-1),
.last 17 (5,true),
.cycle 20 18 true (1),
.cycle 30 15 true (2),
.cycle 2 15 false (3),
.cycle 20 16 true (0),
.last 18 (5,true),
.cycle 9 11 false (1)
])
theorem kid04_part772_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part772) = true := by rfl

def kid04_part773 : Audit := .split 40 (4,true) (byMove [
.cycle 16 27 true (0),
.cycle 10 37 true (-3),
.cycle 53 1 false (-3),
.cycle 50 1 false (-4),
.cycle 45 15 false (-2),
.last 54 (5,true),
.cycle 0 47 true (-3),
.cycle 28 13 true (2),
.cycle 16 25 true (0),
.cycle 52 1 false (-2),
.proven (BB6.Agent11Raw39B0RBPumps.M152.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M152.never m hm),
.cycle 29 15 true (2),
.last 50 (5,true),
.cycle 15 27 true (-1),
.cycle 0 53 true (-3),
.cycle 50 1 false (-4),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[4260864, 4202496, 32768, 512, 2048, 128, 1024, 4260864, 8192, 32768, 131072, 8192, 1024, 66560, 74752, 32768, 131072, 8192, 65536, 4259840, 32768, 512, 2048, 128, 16777216],[199680, 16, 4202496, 133120, 1024, 16777216, 2048, 16, 4260864, 139264, 65536, 16777216, 2048, 4194304, 66560, 8192, 65536, 16777216, 131072, 16, 4259840, 131072, 1024, 16777216, 16777216],16777216⟩,
.cycle 12 29 true (-3),
.cycle 31 18 true (2),
.cycle 28 13 true (2),
.cycle 16 25 true (0),
.last 75 (5,true),
.last 42 (5,true),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[4194304, 4202496, 32768, 512, 2048, 128, 4194320, 4194304, 8192, 32768, 131072, 8192, 4194320, 4194304, 4202496, 32768, 131072, 8192, 4194304, 4194304, 32768, 512, 2048, 128, 16777216],[4196352, 16, 4202496, 2048, 4194320, 16777216, 2048, 16, 4194304, 10240, 16777216, 16777216, 2048, 4194304, 4194304, 8192, 16777216, 16777216, 2048, 16, 4194304, 2048, 4194304, 16777216, 16777216],16777216⟩
])
theorem kid04_part773_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part773) = true := by rfl

def kid04_part774 : Audit := .split 18 (4,true) (byMove [
.last 58 (5,true),
.cycle 10 26 false (1),
.cycle 2 17 false (3),
.last 85 (5,true),
.last 20 (5,true),
.last 62 (5,true),
.cycle 0 22 true (-3),
.last 48 (5,true),
.cycle 0 21 true (-3),
.cycle 3 17 false (3),
.last 49 (5,true),
.last 35 (5,true),
.last 25 (5,true),
.last 58 (5,true),
.cycle 0 26 true (-3),
.cycle 4 15 false (3),
.last 20 (5,true),
.cycle 12 10 false (1),
.cycle 16 18 true (0),
.last 48 (5,true),
.last 36 (5,true),
.last 40 (5,true),
.last 20 (5,true),
.last 22 (5,true)
])
theorem kid04_part774_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part774) = true := by rfl

def kid04_part775 : Audit := .split 15 (4,true) (byMove [
.cycle 20 13 true (2),
.cycle 10 14 false (0),
.last 18 (5,true),
.last 34 (5,true),
.cycle 11 7 false (-1),
.last 16 (5,true),
.cycle 0 22 true (-3),
.cycle 16 12 true (0),
.last 52 (5,true),
.cycle 3 13 false (3),
.cycle 26 16 true (0),
.last 20 (5,true),
.last 19 (5,true),
.last 21 (5,true),
.cycle 14 2 true (-2),
.cycle 18 14 true (0),
.cycle 11 7 false (-1),
.last 16 (5,true),
.cycle 15 18 true (-1),
.cycle 15 14 true (-1),
.cycle 15 25 true (-1),
.cycle 10 17 false (1),
.last 17 (5,true),
.cycle 9 13 false (1)
])
theorem kid04_part775_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part775) = true := by rfl

def kid04_part776 : Audit := .split 15 (5,true) (byMove [
.cycle 20 13 true (2),
.last 17 (4,true),
.last 19 (4,true),
.last 38 (4,true),
.last 16 (4,true),
.last 23 (4,true),
.last 18 (4,true),
.cycle 16 12 true (0),
.last 53 (4,true),
.cycle 3 13 false (3),
.last 19 (4,true),
.last 26 (4,true),
.last 22 (4,true),
.last 17 (4,true),
.cycle 14 2 true (-2),
.cycle 18 14 true (0),
.last 16 (4,true),
.cycle 12 6 false (-1),
.last 18 (4,true),
.last 29 (4,true),
.last 40 (4,true),
.last 23 (4,true),
.last 18 (4,true),
.last 18 (4,true)
])
theorem kid04_part776_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part776) = true := by rfl

def kid04_part752 : Audit := .split 14 (2,true) (byMove [(kid04_part753),(kid04_part754),(kid04_part755),(kid04_part756),(kid04_part757),(kid04_part758),(kid04_part759),(kid04_part760),(kid04_part761),(kid04_part762),(kid04_part763),(kid04_part764),(kid04_part765),(kid04_part766),(kid04_part767),(kid04_part768),(kid04_part769),(kid04_part770),(kid04_part771),(kid04_part772),(kid04_part773),(kid04_part774),(kid04_part775),(kid04_part776)])

theorem kid04_part752_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part752) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid04_part753),(kid04_part754),(kid04_part755),(kid04_part756),(kid04_part757),(kid04_part758),(kid04_part759),(kid04_part760),(kid04_part761),(kid04_part762),(kid04_part763),(kid04_part764),(kid04_part765),(kid04_part766),(kid04_part767),(kid04_part768),(kid04_part769),(kid04_part770),(kid04_part771),(kid04_part772),(kid04_part773),(kid04_part774),(kid04_part775),(kid04_part776)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part753_checked

  · exact kid04_part759_checked

  · exact kid04_part765_checked

  · exact kid04_part771_checked

  · exact kid04_part754_checked

  · exact kid04_part760_checked

  · exact kid04_part766_checked

  · exact kid04_part772_checked

  · exact kid04_part755_checked

  · exact kid04_part761_checked

  · exact kid04_part767_checked

  · exact kid04_part773_checked

  · exact kid04_part756_checked

  · exact kid04_part762_checked

  · exact kid04_part768_checked

  · exact kid04_part774_checked

  · exact kid04_part757_checked

  · exact kid04_part763_checked

  · exact kid04_part769_checked

  · exact kid04_part775_checked

  · exact kid04_part758_checked

  · exact kid04_part764_checked

  · exact kid04_part770_checked

  · exact kid04_part776_checked

def kid04_part778 : Audit := .cycle 17 12 true (1)
theorem kid04_part778_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part778) = true := by rfl

def kid04_part779 : Audit := .cycle 12 12 true (0)
theorem kid04_part779_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part779) = true := by rfl

def kid04_part780 : Audit := .cycle 12 1 false (0)
theorem kid04_part780_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part780) = true := by rfl

def kid04_part781 : Audit := .cycle 11 1 false (-1)
theorem kid04_part781_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part781) = true := by rfl

def kid04_part782 : Audit := .split 18 (4,true) (byMove [
.cycle 13 27 true (-3),
.cycle 34 12 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 8 76 true (-3),
.last 26 (5,true),
.cycle 0 22 true (-3),
.cycle 22 12 true (1),
.cycle 0 21 true (-3),
.cycle 19 1 false (1),
.cycle 22 12 true (-1),
.cycle 19 12 true (0),
.cycle 18 3 false (0),
.cycle 16 3 false (1),
.cycle 0 26 true (-3),
.cycle 19 1 false (-1),
.cycle 104 12 true (1),
.cycle 26 12 true (-1),
.cycle 18 18 true (0),
.cycle 16 17 true (0),
.far true 2 ⟨0,[0, 1, 0, 1],[272, 272, 512, 512, 2048, 256, 272, 272, 256, 512, 2048, 256, 4096],[2304, 16, 16, 2304, 272, 4096, 2048, 16, 16, 256, 272, 4096, 4096],4096⟩,
.cycle 19 12 true (-1),
.last 20 (5,true),
.cycle 9 10 true (-3)
])
theorem kid04_part782_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part782) = true := by rfl

def kid04_part783 : Audit := .split 16 (4,true) (byMove [
.cycle 0 21 true (-2),
.last 31 (5,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 62 (5,true),
.last 23 (5,true),
.cycle 0 20 true (-2),
.last 19 (5,true),
.cycle 0 19 true (-2),
.cycle 17 1 false (1),
.cycle 20 12 true (-1),
.cycle 17 12 true (0),
.cycle 14 3 false (1),
.last 19 (5,true),
.cycle 0 24 true (-2),
.cycle 17 1 false (-1),
.last 74 (5,true),
.last 23 (5,true),
.last 31 (5,true),
.last 19 (5,true),
.cycle 0 19 true (-2),
.cycle 17 12 true (-1),
.last 18 (5,true),
.cycle 9 8 true (-2)
])
theorem kid04_part783_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part783) = true := by rfl

def kid04_part784 : Audit := .cycle 11 12 true (-1)
theorem kid04_part784_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part784) = true := by rfl

def kid04_part785 : Audit := .cycle 19 12 true (2)
theorem kid04_part785_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part785) = true := by rfl

def kid04_part786 : Audit := .cycle 14 1 false (4)
theorem kid04_part786_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part786) = true := by rfl

def kid04_part787 : Audit := .cycle 11 12 true (1)
theorem kid04_part787_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part787) = true := by rfl

def kid04_part788 : Audit := .split 11 (4,true) (byMove [
.cycle 8 7 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 8 11 true (-2),
.cycle 0 21 true (-1),
.cycle 12 12 true (2),
.cycle 12 12 true (-1),
.cycle 13 12 true (1),
.cycle 0 13 true (0),
.cycle 13 12 true (1),
.last 12 (5,true),
.cycle 11 3 false (1),
.cycle 8 9 true (0),
.cycle 12 12 true (0),
.cycle 12 1 false (0),
.cycle 8 17 true (-2),
.cycle 14 12 true (-1),
.cycle 12 12 true (2),
.cycle 1 13 true (0),
.cycle 8 5 true (0),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid04_part788_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part788) = true := by rfl

def kid04_part789 : Audit := .split 11 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 22 true (-2),
.last 17 (4,true),
.cycle 12 12 true (2),
.cycle 12 12 true (-1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 16 true (0),
.last 14 (4,true),
.cycle 0 20 true (0),
.cycle 12 12 true (0),
.cycle 12 1 false (0),
.cycle 0 28 true (-2),
.cycle 14 12 true (-1),
.cycle 12 12 true (2),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
])
theorem kid04_part789_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part789) = true := by rfl

def kid04_part790 : Audit := .split 13 (4,true) (byMove [
.cycle 16 12 true (0),
.cycle 37 12 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 20 12 true (0),
.last 23 (5,true),
.cycle 0 20 true (-1),
.cycle 25 12 true (-1),
.cycle 14 12 true (0),
.cycle 14 1 false (0),
.cycle 27 12 true (-1),
.cycle 16 12 true (-1),
.cycle 11 3 false (0),
.cycle 24 12 true (0),
.cycle 0 26 true (-2),
.cycle 14 1 false (-2),
.cycle 26 12 true (0),
.cycle 29 12 true (-1),
.last 34 (5,true),
.last 19 (5,true),
.cycle 14 12 true (0),
.cycle 25 12 true (-1),
.last 15 (5,true),
.cycle 9 5 false (1)
])
theorem kid04_part790_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part790) = true := by rfl

def kid04_part791 : Audit := .cycle 11 8 true (-4)
theorem kid04_part791_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part791) = true := by rfl

def kid04_part792 : Audit := .cycle 12 12 true (-1)
theorem kid04_part792_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part792) = true := by rfl

def kid04_part793 : Audit := .cycle 11 1 false (-1)
theorem kid04_part793_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part793) = true := by rfl

def kid04_part794 : Audit := .split 24 (4,true) (byMove [
.cycle 21 8 true (-1),
.cycle 26 12 true (0),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 17 8 true (-3),
.last 38 (5,true),
.cycle 25 12 true (-1),
.cycle 34 12 true (-1),
.cycle 44 12 true (-1),
.cycle 25 12 true (1),
.cycle 27 12 true (1),
.last 25 (5,true),
.cycle 24 3 false (0),
.cycle 22 3 false (1),
.cycle 26 12 true (-1),
.cycle 25 1 false (-1),
.cycle 11 14 true (-3),
.cycle 40 12 true (-1),
.last 28 (5,true),
.cycle 22 23 true (0),
.cycle 23 2 true (0),
.cycle 25 12 true (1),
.last 28 (5,true),
.last 25 (5,true)
])
theorem kid04_part794_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part794) = true := by rfl

def kid04_part795 : Audit := .split 23 (5,true) (byMove [
.cycle 20 8 true (0),
.cycle 0 27 true (-2),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 16 8 true (-2),
.last 29 (4,true),
.cycle 24 12 true (2),
.cycle 24 12 true (-1),
.cycle 25 12 true (0),
.cycle 0 25 true (-2),
.last 24 (4,true),
.cycle 0 28 true (-2),
.last 26 (4,true),
.cycle 21 3 false (2),
.cycle 24 12 true (0),
.cycle 24 1 false (0),
.cycle 11 14 true (-2),
.cycle 26 12 true (-1),
.cycle 24 12 true (2),
.last 25 (4,true),
.cycle 22 2 true (1),
.cycle 5 46 true (-2),
.last 24 (4,true),
.cycle 23 5 true (1)
])
theorem kid04_part795_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part795) = true := by rfl

def kid04_part796 : Audit := .split 14 (5,true) (byMove [
.cycle 16 18 true (0),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 37 (4,true),
.last 20 (4,true),
.cycle 15 12 true (1),
.cycle 15 12 true (-2),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 19 true (0),
.last 17 (4,true),
.cycle 17 12 true (1),
.cycle 15 12 true (-1),
.cycle 15 1 false (-1),
.last 43 (4,true),
.cycle 17 12 true (-2),
.cycle 15 12 true (1),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 18 12 true (2)
])
theorem kid04_part796_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part796) = true := by rfl

def kid04_part797 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 13 32 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.far true 2 ⟨0,[0, 1, 0, 1],[16, 272, 512, 512, 2048, 256, 16, 16, 256, 512, 2048, 256, 4096],[2304, 16, 16, 2048, 16, 4096, 2048, 16, 16, 256, 16, 4096, 4096],4096⟩,
.last 31 (5,true),
.cycle 0 16 true (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 12 true (-1),
.cycle 13 12 true (0),
.cycle 11 3 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 2, 1, 128, 256, 32768, 524290, 1073741824, 256, 524288, 1048576, 2097152, 256, 128, 262144, 33554432, 67108864, 134217728, 33554560, 1107296256, 16777472, 33554432, 67108864, 134217728, 1174405504, 1107296384, 1157628160, 1073741824],[2, 256, 128, 1, 128, 1073741824, 8192, 256, 128, 4096, 128, 1073741824, 524288, 1073741824, 524288, 262144, 128, 1073741824, 33554432, 256, 33554432, 16777216, 1107296256, 1073741824, 33554432, 1140850944, 33554432, 16777216, 1107296384, 1073741824, 1073741824],2147382784⟩,
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.far true 2 ⟨0,[0, 1, 0, 1],[1024, 1280, 512, 512, 2048, 256, 1024, 1024, 256, 512, 2048, 256, 4096],[2304, 16, 1024, 2048, 1024, 4096, 2048, 16, 1024, 256, 1024, 4096, 4096],4096⟩,
.last 31 (5,true),
.cycle 0 16 true (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 13 12 true (-1),
.last 14 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part797_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part797) = true := by rfl

def kid04_part798 : Audit := .cycle 2 11 true (0)
theorem kid04_part798_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part798) = true := by rfl

def kid04_part799 : Audit := .cycle 11 12 true (1)
theorem kid04_part799_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part799) = true := by rfl

def kid04_part800 : Audit := .split 11 (4,true) (byMove [
.last 16 (5,true),
.last 51 (5,true),
.last 14 (5,true),
.cycle 16 1 false (0),
.last 51 (5,true),
.last 12 (5,true),
.cycle 12 12 true (2),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 13 12 true (1),
.last 12 (5,true),
.last 22 (5,true),
.last 26 (5,true),
.cycle 10 2 true (0),
.cycle 12 12 true (-1),
.cycle 11 16 true (-3),
.last 12 (5,true),
.cycle 12 12 true (2),
.cycle 1 13 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid04_part800_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part800) = true := by rfl

def kid04_part801 : Audit := .split 11 (5,true) (byMove [
.cycle 18 12 true (2),
.last 54 (4,true),
.cycle 9 4 true (0),
.last 15 (4,true),
.last 12 (4,true),
.cycle 0 28 true (-2),
.cycle 12 12 true (2),
.cycle 15 12 true (-2),
.cycle 9 36 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 16 true (0),
.last 30 (4,true),
.last 22 (4,true),
.cycle 10 2 true (0),
.cycle 12 12 true (-1),
.last 12 (4,true),
.cycle 11 17 true (-2),
.cycle 12 12 true (2),
.last 13 (4,true),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
])
theorem kid04_part801_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part801) = true := by rfl

def kid04_part777 : Audit := .split 10 (2,true) (byMove [(kid04_part778),(kid04_part779),(kid04_part780),(kid04_part781),(kid04_part782),(kid04_part783),(kid04_part784),(kid04_part785),(kid04_part786),(kid04_part787),(kid04_part788),(kid04_part789),(kid04_part790),(kid04_part791),(kid04_part792),(kid04_part793),(kid04_part794),(kid04_part795),(kid04_part796),(kid04_part797),(kid04_part798),(kid04_part799),(kid04_part800),(kid04_part801)])

theorem kid04_part777_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part777) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid04_part778),(kid04_part779),(kid04_part780),(kid04_part781),(kid04_part782),(kid04_part783),(kid04_part784),(kid04_part785),(kid04_part786),(kid04_part787),(kid04_part788),(kid04_part789),(kid04_part790),(kid04_part791),(kid04_part792),(kid04_part793),(kid04_part794),(kid04_part795),(kid04_part796),(kid04_part797),(kid04_part798),(kid04_part799),(kid04_part800),(kid04_part801)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part778_checked

  · exact kid04_part784_checked

  · exact kid04_part790_checked

  · exact kid04_part796_checked

  · exact kid04_part779_checked

  · exact kid04_part785_checked

  · exact kid04_part791_checked

  · exact kid04_part797_checked

  · exact kid04_part780_checked

  · exact kid04_part786_checked

  · exact kid04_part792_checked

  · exact kid04_part798_checked

  · exact kid04_part781_checked

  · exact kid04_part787_checked

  · exact kid04_part793_checked

  · exact kid04_part799_checked

  · exact kid04_part782_checked

  · exact kid04_part788_checked

  · exact kid04_part794_checked

  · exact kid04_part800_checked

  · exact kid04_part783_checked

  · exact kid04_part789_checked

  · exact kid04_part795_checked

  · exact kid04_part801_checked

def kid04_part802 : Audit := .cycle 15 1 false (-1)
theorem kid04_part802_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part802) = true := by rfl

def kid04_part804 : Audit := .split 13 (2,true) (byMove [
.proven (BB6.Agent11Raw39B0RBPumps.M159.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M159.never m hm),
.cycle 0 16 false (3),
.cycle 17 1 false (-1),
.cycle 0 36 true (-1),
.cycle 0 19 true (-1),
.last 14 (5,true),
.cycle 0 41 true (-1),
.last 16 (5,true),
.last 47 (5,true),
.cycle 0 15 true (-1),
.cycle 12 15 true (0),
.last 14 (5,true),
.last 17 (5,true),
.last 33 (5,true),
.cycle 20 2 false (0),
.cycle 5 9 false (3),
.cycle 10 8 true (-1),
.last 14 (5,true),
.last 25 (5,true),
.last 27 (5,true),
.cycle 12 13 true (0),
.cycle 0 15 true (-1),
.last 26 (5,true),
.last 14 (5,true)
])
theorem kid04_part804_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part804) = true := by rfl

def kid04_part805 : Audit := .split 27 (5,true) (byMove [
.last 30 (2,true),
.cycle 24 9 false (2),
.cycle 29 1 false (-1),
.cycle 28 1 false (-2),
.cycle 28 2 false (-2),
.cycle 28 2 false (-2),
.cycle 30 2 false (0),
.cycle 29 2 false (-1),
.last 28 (2,true),
.cycle 31 2 false (1),
.last 44 (2,true),
.cycle 33 2 false (5),
.cycle 38 2 false (-2),
.last 29 (2,true),
.cycle 32 2 false (0),
.cycle 28 1 false (-2),
.cycle 28 2 false (-2),
.cycle 28 2 false (-2),
.last 34 (2,true),
.cycle 37 2 false (-1),
.last 28 (2,true),
.last 39 (2,true),
.cycle 30 2 false (-2),
.cycle 40 2 false (-2)
])
theorem kid04_part805_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part805) = true := by rfl

def kid04_part806 : Audit := .cycle 12 1 false (0)
theorem kid04_part806_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part806) = true := by rfl

def kid04_part807 : Audit := .cycle 11 1 false (-1)
theorem kid04_part807_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part807) = true := by rfl

def kid04_part808 : Audit := .cycle 11 2 false (-1)
theorem kid04_part808_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part808) = true := by rfl

def kid04_part809 : Audit := .cycle 11 2 false (-1)
theorem kid04_part809_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part809) = true := by rfl

def kid04_part810 : Audit := .cycle 13 2 false (1)
theorem kid04_part810_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part810) = true := by rfl

def kid04_part811 : Audit := .cycle 12 2 false (0)
theorem kid04_part811_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part811) = true := by rfl

def kid04_part812 : Audit := .split 11 (2,true) (byMove [
.last 26 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 20 2 false (4),
.cycle 13 2 false (1),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.last 12 (5,true),
.cycle 0 17 true (0),
.cycle 15 2 false (-1),
.cycle 22 2 false (4),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.last 23 (5,true),
.cycle 15 1 false (3),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 20 2 false (2),
.last 12 (5,true)
])
theorem kid04_part812_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part812) = true := by rfl

def kid04_part813 : Audit := .cycle 20 2 false (4)
theorem kid04_part813_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part813) = true := by rfl

def kid04_part814 : Audit := .cycle 13 2 false (3)
theorem kid04_part814_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part814) = true := by rfl

def kid04_part815 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 20 2 false (4),
.cycle 13 2 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 2 false (3),
.cycle 13 2 false (3),
.cycle 15 2 false (1),
.last 13 (2,true),
.cycle 22 2 false (4),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.last 30 (2,true),
.cycle 14 2 false (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 8 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part815_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part815) = true := by rfl

def kid04_part816 : Audit := .cycle 10 3 false (0)
theorem kid04_part816_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part816) = true := by rfl

def kid04_part817 : Audit := .split 12 (2,true) (byMove [
.cycle 27 2 false (3),
.cycle 14 2 false (-2),
.cycle 15 1 false (-1),
.cycle 0 24 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 6 7 false (3),
.last 15 (5,true),
.cycle 24 2 false (0),
.last 27 (5,true),
.cycle 54 2 false (-4),
.last 13 (5,true),
.cycle 15 2 false (-1),
.cycle 14 2 false (-2),
.cycle 18 2 false (0),
.cycle 16 2 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 16 (5,true),
.cycle 16 2 false (-2),
.last 35 (5,true),
.cycle 28 2 false (-2),
.last 19 (5,true),
.last 13 (5,true)
])
theorem kid04_part817_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part817) = true := by rfl

def kid04_part818 : Audit := .cycle 15 2 false (1)
theorem kid04_part818_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part818) = true := by rfl

def kid04_part819 : Audit := .cycle 11 1 false (-1)
theorem kid04_part819_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part819) = true := by rfl

def kid04_part820 : Audit := .cycle 11 2 false (-1)
theorem kid04_part820_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part820) = true := by rfl

def kid04_part821 : Audit := .cycle 11 2 false (-1)
theorem kid04_part821_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part821) = true := by rfl

def kid04_part822 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 23 2 false (3),
.cycle 16 2 false (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 16 2 false (2),
.last 48 (2,true),
.last 16 (2,true),
.cycle 25 2 false (3),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 33 (2,true),
.cycle 0 17 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 14 17 true (0)
])
theorem kid04_part822_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part822) = true := by rfl

def kid04_part823 : Audit := .split 14 (2,true) (byMove [
.last 26 (5,true),
.cycle 1 16 true (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.last 25 (5,true),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.last 17 (5,true),
.last 18 (5,true),
.cycle 11 4 true (0),
.cycle 21 2 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 2097152, 256, 524290, 1073741824, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 134217728, 1325408256, 1325408256, 1325408256, 1073741824],[2, 0, 0, 1, 128, 1073741824, 8192, 256, 524290, 4096, 128, 1073741824, 524288, 1073741824, 256, 262144, 33554432, 1073741824, 8192, 256, 524290, 4096, 128, 1073741824, 33554432, 1325408256, 1325408256, 16777216, 33554432, 1073741824, 1073741824],2135045120⟩,
.cycle 1 17 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 16 18 true (1),
.last 16 (5,true),
.cycle 1 18 true (0)
])
theorem kid04_part823_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part823) = true := by rfl

def kid04_part824 : Audit := .split 11 (2,true) (byMove [
.cycle 23 2 false (3),
.cycle 13 2 false (-1),
.cycle 14 1 false (0),
.cycle 22 2 false (2),
.cycle 0 15 true (0),
.last 12 (5,true),
.cycle 0 35 true (0),
.last 14 (5,true),
.cycle 21 2 false (1),
.cycle 0 13 true (0),
.last 22 (5,true),
.last 12 (5,true),
.cycle 14 2 false (0),
.cycle 13 2 false (-1),
.cycle 17 2 false (1),
.cycle 15 2 false (1),
.cycle 10 2 true (0),
.last 12 (5,true),
.last 23 (5,true),
.cycle 2 12 true (0),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 2 11 true (0),
.last 12 (5,true)
])
theorem kid04_part824_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part824) = true := by rfl

def kid04_part825 : Audit := .split 34 (2,true) (byMove [
.last 48 (5,true),
.cycle 7 28 true (0),
.cycle 43 2 false (1),
.cycle 0 36 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 1073741824, 4096, 33554432, 67108864, 2097152, 256, 524290, 1073741824, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 134217728, 1325408256, 1325408256, 1325408256, 1073741824],[2, 0, 0, 1, 512, 1073741824, 8192, 524290, 524290, 4096, 512, 1073741824, 524288, 1073741824, 1073741824, 262144, 134217728, 1073741824, 8192, 256, 256, 4096, 512, 1073741824, 33554432, 1325408256, 1325408256, 16777216, 134217728, 1073741824, 1073741824],2135047168⟩,
.last 35 (5,true),
.cycle 0 35 true (0),
.last 45 (5,true),
.cycle 0 59 true (0),
.cycle 15 20 true (0),
.cycle 8 27 true (0),
.last 37 (5,true),
.last 40 (5,true),
.cycle 27 8 true (0),
.far false 7 ⟨0,[0, 5, 3, 1, 2, 4, 6, 4, 2, 4, 3, 1, 3, 5],[2147483648, 4294967296, 8, 0, 0, 0, 128, 256, 2097152, 137438953472, 4398046511104, 262144, 33554432, 67108864, 32768, 4398147743744, 4398147743744, 4398147743744, 33554432, 67108864, 549755813888, 4294967296, 137438953474, 4398046511104, 33554432, 67108864, 32768, 532480, 4398046511104, 4096, 128, 256, 2097152, 137438953474, 4398046511104, 262144, 2147483648, 4294967296, 2097152, 137438953474, 4398046511104, 4294967296, 4398046511104],[2, 0, 1, 1, 8589934592, 4398046511104, 524288, 137438953472, 141733920770, 262144, 512, 4398046511104, 8192, 4398147743744, 4096, 4096, 134217728, 4398046511104, 137438953472, 4398046511104, 68719476736, 68719476736, 134217728, 4398046511104, 8192, 532480, 4398147743744, 4096, 134217728, 4398046511104, 524288, 137438953474, 137438953474, 262144, 512, 4398046511104, 524288, 4294967296, 262144, 262144, 8589934592, 4398046511104, 4398046511104],5550164147200⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 1073741824, 4096, 33554432, 67108864, 2097152, 256, 524290, 1073741824, 128, 256, 32768, 524290, 1073741824, 256, 33554432, 67108864, 134217728, 1325408256, 1325408256, 1325408256, 1073741824],[2, 0, 0, 1, 512, 1073741824, 8192, 524290, 524290, 4096, 512, 1073741824, 524288, 1073741824, 256, 262144, 134217728, 1073741824, 8192, 256, 524290, 4096, 512, 1073741824, 33554432, 1325408256, 1325408256, 16777216, 134217728, 1073741824, 1073741824],2135047168⟩,
.cycle 0 37 true (0),
.last 35 (5,true),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 2 33 true (0),
.cycle 11 25 true (0),
.last 36 (5,true),
.cycle 0 38 true (0)
])
theorem kid04_part825_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part825) = true := by rfl

def kid04_part826 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 30 true (-1),
.last 15 (2,true),
.last 25 (2,true),
.cycle 21 2 false (-1),
.cycle 17 2 false (-1),
.cycle 10 19 true (0),
.cycle 22 2 false (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.cycle 10 10 true (0),
.cycle 17 5 false (1),
.last 20 (2,true),
.last 15 (2,true),
.cycle 5 10 true (0),
.cycle 10 5 true (0),
.cycle 17 2 false (-1),
.last 33 (2,true),
.cycle 12 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.cycle 11 6 true (1)
])
theorem kid04_part826_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part826) = true := by rfl

def kid04_part827 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 13 2 false (-1),
.last 12 (2,true),
.cycle 0 20 true (0),
.cycle 9 4 true (0),
.cycle 13 2 false (-1),
.last 34 (2,true),
.cycle 16 2 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 8 true (0),
.cycle 29 2 false (5),
.cycle 14 2 false (0),
.cycle 13 2 false (-1),
.last 12 (2,true),
.cycle 15 2 false (1),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.last 30 (2,true),
.cycle 1 16 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 6 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part827_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part827) = true := by rfl

def kid04_part803 : Audit := .split 10 (4,true) (byMove [(kid04_part804),(kid04_part805),(kid04_part806),(kid04_part807),(kid04_part808),(kid04_part809),(kid04_part810),(kid04_part811),(kid04_part812),(kid04_part813),(kid04_part814),(kid04_part815),(kid04_part816),(kid04_part817),(kid04_part818),(kid04_part819),(kid04_part820),(kid04_part821),(kid04_part822),(kid04_part823),(kid04_part824),(kid04_part825),(kid04_part826),(kid04_part827)])

theorem kid04_part803_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part803) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part804),(kid04_part805),(kid04_part806),(kid04_part807),(kid04_part808),(kid04_part809),(kid04_part810),(kid04_part811),(kid04_part812),(kid04_part813),(kid04_part814),(kid04_part815),(kid04_part816),(kid04_part817),(kid04_part818),(kid04_part819),(kid04_part820),(kid04_part821),(kid04_part822),(kid04_part823),(kid04_part824),(kid04_part825),(kid04_part826),(kid04_part827)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part804_checked

  · exact kid04_part810_checked

  · exact kid04_part816_checked

  · exact kid04_part822_checked

  · exact kid04_part805_checked

  · exact kid04_part811_checked

  · exact kid04_part817_checked

  · exact kid04_part823_checked

  · exact kid04_part806_checked

  · exact kid04_part812_checked

  · exact kid04_part818_checked

  · exact kid04_part824_checked

  · exact kid04_part807_checked

  · exact kid04_part813_checked

  · exact kid04_part819_checked

  · exact kid04_part825_checked

  · exact kid04_part808_checked

  · exact kid04_part814_checked

  · exact kid04_part820_checked

  · exact kid04_part826_checked

  · exact kid04_part809_checked

  · exact kid04_part815_checked

  · exact kid04_part821_checked

  · exact kid04_part827_checked

def kid04_part829 : Audit := .split 13 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 11, 256, 256, 128, 256, 8, 2, 256, 256, 4096],[2, 8, 256, 1, 4096, 256, 2, 4096, 256, 1, 4096, 256, 4096],4096⟩,
.last 15 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 19 true (-1),
.cycle 0 41 true (-1),
.cycle 18 22 true (-1),
.cycle 71 1 false (-1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 12 15 true (0),
.cycle 10 7 false (1),
.last 15 (4,true),
.cycle 21 1 false (-1),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 10 8 true (-1),
.cycle 12 36 true (0),
.last 15 (4,true),
.cycle 12 13 true (0),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 30 5 true (1)
])
theorem kid04_part829_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part829) = true := by rfl

def kid04_part830 : Audit := .cycle 25 9 false (2)
theorem kid04_part830_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part830) = true := by rfl

def kid04_part831 : Audit := .cycle 12 1 false (0)
theorem kid04_part831_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part831) = true := by rfl

def kid04_part832 : Audit := .cycle 11 1 false (-1)
theorem kid04_part832_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part832) = true := by rfl

def kid04_part833 : Audit := .cycle 12 1 false (-2)
theorem kid04_part833_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part833) = true := by rfl

def kid04_part834 : Audit := .cycle 11 1 false (-1)
theorem kid04_part834_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part834) = true := by rfl

def kid04_part835 : Audit := .cycle 14 1 false (0)
theorem kid04_part835_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part835) = true := by rfl

def kid04_part836 : Audit := .cycle 13 1 false (-1)
theorem kid04_part836_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part836) = true := by rfl

def kid04_part837 : Audit := .split 11 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 11, 256, 256, 128, 256, 8, 2, 256, 256, 4096],[2, 8, 256, 1, 4096, 4, 2, 4096, 256, 1, 4096, 4, 4096],4096⟩,
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (4),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 23 1 false (3),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 30 true (0),
.last 13 (4,true),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 21 1 false (1)
])
theorem kid04_part837_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part837) = true := by rfl

def kid04_part838 : Audit := .cycle 21 1 false (3)
theorem kid04_part838_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part838) = true := by rfl

def kid04_part839 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 11 3 false (1),
.last 13 (2,true),
.cycle 23 1 false (3),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 30 true (0),
.cycle 1 13 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 8 5 true (0)
])
theorem kid04_part839_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part839) = true := by rfl

def kid04_part840 : Audit := .cycle 13 1 false (3)
theorem kid04_part840_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part840) = true := by rfl

def kid04_part841 : Audit := .split 13 (4,true) (byMove [
.cycle 35 1 false (-3),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 0 20 true (-1),
.last 15 (2,true),
.cycle 25 1 false (3),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.last 15 (2,true),
.cycle 0 26 true (-2),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 38 1 false (-2),
.last 15 (2,true),
.cycle 27 11 false (2),
.cycle 19 1 false (-1),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
])
theorem kid04_part841_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part841) = true := by rfl

def kid04_part842 : Audit := .split 12 (2,true) (byMove [
.cycle 28 1 false (2),
.cycle 15 1 false (-3),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.cycle 10 5 false (1),
.cycle 25 1 false (-1),
.cycle 25 9 false (2),
.last 13 (4,true),
.last 23 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 19 1 false (-3),
.last 14 (4,true),
.last 25 (4,true),
.cycle 29 1 false (-3),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid04_part842_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part842) = true := by rfl

def kid04_part843 : Audit := .cycle 16 1 false (0)
theorem kid04_part843_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part843) = true := by rfl

def kid04_part844 : Audit := .cycle 11 1 false (-1)
theorem kid04_part844_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part844) = true := by rfl

def kid04_part845 : Audit := .cycle 12 1 false (-2)
theorem kid04_part845_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part845) = true := by rfl

def kid04_part846 : Audit := .cycle 11 1 false (-1)
theorem kid04_part846_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part846) = true := by rfl

def kid04_part847 : Audit := .split 33 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32771, 256, 256, 128, 256, 32768, 2, 8192, 8192, 128, 256, 8, 32768, 256, 256, 262144],[2, 32768, 256, 1, 262144, 64, 8192, 262144, 256, 4096, 262144, 64, 2, 256, 256, 1, 262144, 64, 262144],262144⟩,
.cycle 12 22 true (0),
.cycle 42 1 false (0),
.cycle 0 35 true (0),
.last 34 (4,true),
.cycle 0 35 true (0),
.cycle 0 34 true (0),
.cycle 16 18 true (0),
.cycle 0 54 true (0),
.cycle 18 16 true (0),
.cycle 8 26 true (0),
.cycle 9 26 true (0),
.cycle 6 28 true (0),
.cycle 28 6 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 8192, 8192, 33554432, 67108864, 2097152, 67149824, 67108864, 67108864, 128, 256, 32768, 67379200, 8192, 8192, 128, 256, 32768, 8192, 8192, 8192, 1073741824],[2, 0, 1, 1, 1073741824, 64, 8192, 1073741824, 67936258, 4096, 1073741824, 64, 524288, 67108864, 262144, 262144, 1073741824, 16777216, 8192, 32768, 4096, 4096, 1073741824, 64, 8192, 1073741824, 8192, 4096, 1073741824, 64, 1073741824],1073741824⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 8192, 8192, 33554432, 67108864, 2097152, 67149824, 67108864, 67108864, 128, 256, 32768, 67379200, 8192, 8192, 128, 256, 32768, 8192, 8192, 8192, 1073741824],[2, 0, 0, 1, 1073741824, 64, 8192, 1073741824, 524290, 4096, 1073741824, 64, 524288, 67108864, 67149824, 262144, 1073741824, 16777216, 8192, 32768, 67379200, 4096, 1073741824, 64, 8192, 1073741824, 8192, 4096, 1073741824, 64, 1073741824],1073741824⟩,
.last 34 (4,true),
.cycle 14 20 true (0),
.cycle 0 34 true (0),
.cycle 1 33 true (0),
.cycle 2 32 true (0),
.cycle 0 57 true (0),
.cycle 13 21 true (0),
.cycle 14 21 true (0)
])
theorem kid04_part847_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part847) = true := by rfl

def kid04_part848 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 11 3 false (1),
.last 14 (2,true),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 1 false (0),
.cycle 10 4 true (0),
.cycle 9 4 true (0)
])
theorem kid04_part848_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part848) = true := by rfl

def kid04_part849 : Audit := .split 11 (2,true) (byMove [
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (0),
.last 15 (4,true),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 0 35 true (0),
.cycle 15 18 true (0),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 18 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 30 true (0),
.last 13 (4,true),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (0)
])
theorem kid04_part849_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part849) = true := by rfl

def kid04_part850 : Audit := .split 34 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 295170, 256, 256, 128, 256, 32768, 524290, 4096, 4096, 128, 256, 2097152, 33024, 524288, 524288, 128, 256, 8, 262400, 256, 256, 16777216],[2, 32768, 256, 1, 16777216, 512, 8192, 16777216, 256, 4096, 16777216, 512, 524288, 128, 256, 262144, 16777216, 512, 2, 256, 256, 1, 16777216, 512, 16777216],16777216⟩,
.cycle 7 28 true (0),
.cycle 44 1 false (0),
.cycle 0 36 true (0),
.last 35 (4,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 4096, 4096, 33554432, 67108864, 2097152, 256, 524290, 524290, 128, 256, 32768, 524290, 256, 256, 33554432, 67108864, 134217728, 1326227842, 1326227842, 1326227842, 1073741824],[2, 0, 0, 1, 1073741824, 512, 8192, 1073741824, 524290, 4096, 1073741824, 512, 524288, 33587200, 33587200, 262144, 1073741824, 134217728, 8192, 256, 256, 4096, 1073741824, 512, 33554432, 1326227842, 1326227842, 16777216, 1073741824, 134217728, 1073741824],2130721792⟩,
.cycle 0 35 true (0),
.cycle 5 41 true (0),
.cycle 0 59 true (0),
.cycle 15 20 true (0),
.cycle 8 27 true (0),
.cycle 9 27 true (0),
.cycle 5 36 true (0),
.cycle 27 8 true (0),
.far false 7 ⟨0,[0, 5, 3, 1, 2, 4, 6, 4, 2, 4, 3, 1, 3, 5],[2147483648, 4294967296, 8, 0, 0, 0, 128, 256, 2097152, 137438953472, 262144, 262144, 33554432, 67108864, 32768, 4610750722306, 4610750722306, 4610750722306, 33554432, 67108864, 549755813888, 4294967296, 137438953474, 137438953474, 33554432, 67108864, 32768, 532480, 4096, 4096, 128, 256, 2097152, 137438953474, 262144, 262144, 2147483648, 4294967296, 2097152, 137438953474, 4294967296, 4294967296, 4398046511104],[2, 0, 1, 1, 4398046511104, 8589934592, 524288, 4398046511104, 141733920770, 262144, 4398046511104, 512, 8192, 4610750722306, 4096, 4096, 4398046511104, 134217728, 137438953472, 35651584, 68719476736, 68719476736, 4398046511104, 134217728, 8192, 4398046511104, 4610750722306, 4096, 4398046511104, 134217728, 524288, 4398046511104, 137438953474, 262144, 4398046511104, 512, 524288, 4294967296, 262144, 262144, 4398046511104, 8589934592, 4398046511104],4450644130816⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 4096, 4096, 33554432, 67108864, 2097152, 256, 524290, 524290, 128, 256, 32768, 524290, 256, 256, 33554432, 67108864, 134217728, 1326227842, 1326227842, 1326227842, 1073741824],[2, 0, 0, 1, 1073741824, 512, 8192, 1073741824, 524290, 4096, 1073741824, 512, 524288, 33587200, 256, 262144, 1073741824, 134217728, 8192, 256, 524290, 4096, 1073741824, 512, 33554432, 1326227842, 1326227842, 16777216, 1073741824, 134217728, 1073741824],2130721792⟩,
.last 35 (4,true),
.cycle 0 37 true (0),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 2 33 true (0),
.cycle 11 25 true (0),
.cycle 0 38 true (0),
.cycle 0 38 true (0)
])
theorem kid04_part850_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part850) = true := by rfl

def kid04_part851 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 14 1 false (-2),
.cycle 10 4 true (0),
.last 34 (2,true),
.last 33 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 9 8 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 14 1 false (-2),
.cycle 10 2 true (0),
.cycle 0 30 true (0),
.cycle 1 13 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 14 3 true (2)
])
theorem kid04_part851_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part851) = true := by rfl

def kid04_part852 : Audit := .cycle 11 3 true (1)
theorem kid04_part852_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part852) = true := by rfl

def kid04_part828 : Audit := .split 10 (5,true) (byMove [(kid04_part829),(kid04_part830),(kid04_part831),(kid04_part832),(kid04_part833),(kid04_part834),(kid04_part835),(kid04_part836),(kid04_part837),(kid04_part838),(kid04_part839),(kid04_part840),(kid04_part841),(kid04_part842),(kid04_part843),(kid04_part844),(kid04_part845),(kid04_part846),(kid04_part847),(kid04_part848),(kid04_part849),(kid04_part850),(kid04_part851),(kid04_part852)])

theorem kid04_part828_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part828) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part829),(kid04_part830),(kid04_part831),(kid04_part832),(kid04_part833),(kid04_part834),(kid04_part835),(kid04_part836),(kid04_part837),(kid04_part838),(kid04_part839),(kid04_part840),(kid04_part841),(kid04_part842),(kid04_part843),(kid04_part844),(kid04_part845),(kid04_part846),(kid04_part847),(kid04_part848),(kid04_part849),(kid04_part850),(kid04_part851),(kid04_part852)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part829_checked

  · exact kid04_part835_checked

  · exact kid04_part841_checked

  · exact kid04_part847_checked

  · exact kid04_part830_checked

  · exact kid04_part836_checked

  · exact kid04_part842_checked

  · exact kid04_part848_checked

  · exact kid04_part831_checked

  · exact kid04_part837_checked

  · exact kid04_part843_checked

  · exact kid04_part849_checked

  · exact kid04_part832_checked

  · exact kid04_part838_checked

  · exact kid04_part844_checked

  · exact kid04_part850_checked

  · exact kid04_part833_checked

  · exact kid04_part839_checked

  · exact kid04_part845_checked

  · exact kid04_part851_checked

  · exact kid04_part834_checked

  · exact kid04_part840_checked

  · exact kid04_part846_checked

  · exact kid04_part852_checked

def kid04_part853 : Audit := .cycle 1 10 true (1)
theorem kid04_part853_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part853) = true := by rfl

def kid04_part854 : Audit := .split 11 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.cycle 1 13 false (3),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 18 1 false (0),
.cycle 1 13 true (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 28 1 false (2),
.last 14 (5,true),
.cycle 1 13 true (0)
]),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 1 24 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 17 false (3),
.cycle 1 13 false (3),
.cycle 0 13 true (0),
.cycle 1 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 1 17 false (3),
.cycle 1 13 true (0),
.cycle 1 16 false (3),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 42 (2,true),
.cycle 1 16 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 1 23 false (3),
.cycle 1 27 true (0),
.cycle 11 4 true (0),
.cycle 1 13 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 16 3 false (0),
.split 18 (2,true) (byMove [
.cycle 12 14 true (-3),
.cycle 12 7 false (0),
.cycle 21 1 false (-3),
.cycle 17 30 true (-3),
.cycle 16 3 false (-2),
.last 19 (5,true),
.last 36 (5,true),
.last 41 (5,true),
.cycle 12 13 false (0),
.cycle 12 11 false (0),
.cycle 8 11 false (2),
.last 36 (5,true),
.cycle 12 8 false (0),
.cycle 12 7 false (0),
.cycle 63 17 true (-1),
.cycle 54 15 true (2),
.cycle 16 3 false (-2),
.last 19 (5,true),
.cycle 36 7 false (0),
.last 1036 (5,true),
.cycle 2 17 false (3),
.cycle 22 16 true (0),
.last 20 (5,true),
.cycle 36 7 false (0)
]),
.split 12 (2,true) (byMove [
.cycle 0 30 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 11 false (1),
.last 16 (5,true),
.cycle 0 27 true (0),
.cycle 0 20 true (-2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.last 13 (5,true),
.cycle 0 23 true (-2),
.cycle 0 39 true (-4),
.cycle 0 29 true (-1),
.cycle 13 1 false (-1),
.cycle 0 29 true (-3),
.cycle 0 23 true (-2),
.cycle 0 27 true (0),
.cycle 0 17 true (-1),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.last 13 (5,true)
]),
.cycle 25 1 false (1),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.last 15 (2,true),
.cycle 22 3 false (3),
.cycle 15 3 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.cycle 1 14 true (0),
.cycle 14 3 false (0),
.last 14 (2,true),
.cycle 24 3 false (3),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 13 3 false (0),
.cycle 9 16 true (0),
.cycle 13 3 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.cycle 1 14 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.last 26 (2,true),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 14 6 false (1),
.cycle 0 19 true (-1),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 1 15 true (1),
.cycle 18 5 false (0),
.last 22 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 11 5 true (0),
.cycle 14 5 false (0),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 1 15 true (1)
]),
.cycle 1 12 true (1)
])
theorem kid04_part854_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part854) = true := by rfl

def kid04_part856 : Audit := .cycle 1 11 true (1)
theorem kid04_part856_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part856) = true := by rfl

def kid04_part857 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 19 4 false (1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 19 4 false (3),
.cycle 11 3 false (1),
.cycle 14 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 22 4 false (4),
.last 14 (5,true),
.cycle 2 12 true (0)
])
theorem kid04_part857_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part857) = true := by rfl

def kid04_part858 : Audit := .cycle 14 1 false (0)
theorem kid04_part858_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part858) = true := by rfl

def kid04_part859 : Audit := .cycle 0 12 true (0)
theorem kid04_part859_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part859) = true := by rfl

def kid04_part860 : Audit := .split 11 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 2 11 true (1),
.cycle 17 3 false (-1),
.cycle 15 3 false (-1),
.cycle 10 11 false (2),
.cycle 25 1 false (1),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 2 11 true (1)
])
theorem kid04_part860_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part860) = true := by rfl

def kid04_part861 : Audit := .split 11 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 11 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 2 11 true (1),
.last 20 (4,true),
.cycle 15 3 false (-1),
.cycle 0 16 true (-1),
.cycle 25 1 false (1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 2 11 true (1)
])
theorem kid04_part861_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part861) = true := by rfl

def kid04_part862 : Audit := .cycle 0 11 true (0)
theorem kid04_part862_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part862) = true := by rfl

def kid04_part863 : Audit := .cycle 1 10 true (1)
theorem kid04_part863_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part863) = true := by rfl

def kid04_part864 : Audit := .cycle 0 23 true (0)
theorem kid04_part864_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part864) = true := by rfl

def kid04_part865 : Audit := .cycle 3 8 true (1)
theorem kid04_part865_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part865) = true := by rfl

def kid04_part866 : Audit := .cycle 8 3 true (1)
theorem kid04_part866_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part866) = true := by rfl

def kid04_part867 : Audit := .cycle 2 10 true (1)
theorem kid04_part867_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part867) = true := by rfl

def kid04_part868 : Audit := .split 14 (5,true) (byMove [
.cycle 10 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 0 18 true (-1),
.cycle 21 5 false (4),
.cycle 15 5 false (1),
.last 18 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 21 5 false (4),
.last 17 (4,true),
.cycle 16 5 false (0),
.cycle 23 5 false (4),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (0),
.cycle 6 20 true (0),
.last 16 (4,true),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 2 15 true (0)
])
theorem kid04_part868_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part868) = true := by rfl

def kid04_part869 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 19 4 false (1),
.cycle 0 16 true (0),
.cycle 14 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 13 4 false (2),
.cycle 11 3 false (1),
.cycle 14 4 false (0),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 16 true (0),
.cycle 10 4 true (0),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.last 14 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part869_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part869) = true := by rfl

def kid04_part870 : Audit := .cycle 14 14 true (-1)
theorem kid04_part870_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part870) = true := by rfl

def kid04_part871 : Audit := .cycle 1 12 true (1)
theorem kid04_part871_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part871) = true := by rfl

def kid04_part872 : Audit := .split 11 (4,true) (byMove [
.cycle 10 8 true (0),
.cycle 7 17 false (3),
.cycle 18 1 false (-2),
.cycle 16 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 8 5 true (1),
.last 12 (5,true),
.cycle 17 3 false (-1),
.cycle 15 3 false (-1),
.cycle 32 14 true (-1),
.cycle 19 1 false (-1),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid04_part872_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part872) = true := by rfl

def kid04_part873 : Audit := .split 11 (5,true) (byMove [
.cycle 10 8 true (0),
.cycle 7 17 false (3),
.cycle 17 1 false (-1),
.last 15 (4,true),
.last 12 (4,true),
.last 29 (4,true),
.cycle 1 12 true (1),
.cycle 14 5 false (1),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 12 true (1),
.last 20 (4,true),
.cycle 15 3 false (-1),
.cycle 28 14 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.last 13 (4,true),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 12 true (1)
])
theorem kid04_part873_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part873) = true := by rfl

def kid04_part874 : Audit := .cycle 0 11 true (0)
theorem kid04_part874_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part874) = true := by rfl

def kid04_part875 : Audit := .cycle 1 10 true (1)
theorem kid04_part875_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part875) = true := by rfl

def kid04_part876 : Audit := .cycle 2 9 true (1)
theorem kid04_part876_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part876) = true := by rfl

def kid04_part877 : Audit := .cycle 1 13 true (1)
theorem kid04_part877_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part877) = true := by rfl

def kid04_part878 : Audit := .split 12 (5,true) (byMove [
.cycle 10 5 true (1),
.last 14 (4,true),
.cycle 20 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 13 13 false (1),
.cycle 1 13 true (1),
.cycle 14 9 false (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 13 true (1),
.last 19 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 17 (4,true),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 13 true (1)
])
theorem kid04_part878_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part878) = true := by rfl

def kid04_part879 : Audit := .cycle 2 10 true (1)
theorem kid04_part879_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part879) = true := by rfl

def kid04_part855 : Audit := .split 10 (2,true) (byMove [(kid04_part856),(kid04_part857),(kid04_part858),(kid04_part859),(kid04_part860),(kid04_part861),(kid04_part862),(kid04_part863),(kid04_part864),(kid04_part865),(kid04_part866),(kid04_part867),(kid04_part868),(kid04_part869),(kid04_part870),(kid04_part871),(kid04_part872),(kid04_part873),(kid04_part874),(kid04_part875),(kid04_part876),(kid04_part877),(kid04_part878),(kid04_part879)])

theorem kid04_part855_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part855) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid04_part856),(kid04_part857),(kid04_part858),(kid04_part859),(kid04_part860),(kid04_part861),(kid04_part862),(kid04_part863),(kid04_part864),(kid04_part865),(kid04_part866),(kid04_part867),(kid04_part868),(kid04_part869),(kid04_part870),(kid04_part871),(kid04_part872),(kid04_part873),(kid04_part874),(kid04_part875),(kid04_part876),(kid04_part877),(kid04_part878),(kid04_part879)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part856_checked

  · exact kid04_part862_checked

  · exact kid04_part868_checked

  · exact kid04_part874_checked

  · exact kid04_part857_checked

  · exact kid04_part863_checked

  · exact kid04_part869_checked

  · exact kid04_part875_checked

  · exact kid04_part858_checked

  · exact kid04_part864_checked

  · exact kid04_part870_checked

  · exact kid04_part876_checked

  · exact kid04_part859_checked

  · exact kid04_part865_checked

  · exact kid04_part871_checked

  · exact kid04_part877_checked

  · exact kid04_part860_checked

  · exact kid04_part866_checked

  · exact kid04_part872_checked

  · exact kid04_part878_checked

  · exact kid04_part861_checked

  · exact kid04_part867_checked

  · exact kid04_part873_checked

  · exact kid04_part879_checked

def kid04_part880 : Audit := .cycle 0 11 true (0)
theorem kid04_part880_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part880) = true := by rfl

def kid04_part882 : Audit := .cycle 1 11 true (1)
theorem kid04_part882_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part882) = true := by rfl

def kid04_part883 : Audit := .cycle 19 4 false (1)
theorem kid04_part883_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part883) = true := by rfl

def kid04_part884 : Audit := .split 11 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.last 14 (5,true),
.cycle 22 1 false (-2),
.cycle 11 7 false (1),
.cycle 0 29 true (-1),
.cycle 25 1 false (1),
.cycle 14 1 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.last 14 (5,true)
])
theorem kid04_part884_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part884) = true := by rfl

def kid04_part885 : Audit := .cycle 0 12 true (0)
theorem kid04_part885_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part885) = true := by rfl

def kid04_part886 : Audit := .cycle 11 4 false (1)
theorem kid04_part886_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part886) = true := by rfl

def kid04_part887 : Audit := .split 11 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 11 4 true (1),
.cycle 17 6 false (-1),
.last 18 (2,true),
.last 12 (2,true),
.cycle 25 1 false (1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 11 4 true (1)
])
theorem kid04_part887_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part887) = true := by rfl

def kid04_part888 : Audit := .cycle 0 11 true (0)
theorem kid04_part888_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part888) = true := by rfl

def kid04_part889 : Audit := .cycle 1 10 true (1)
theorem kid04_part889_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part889) = true := by rfl

def kid04_part890 : Audit := .cycle 0 23 true (0)
theorem kid04_part890_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part890) = true := by rfl

def kid04_part891 : Audit := .cycle 3 8 true (1)
theorem kid04_part891_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part891) = true := by rfl

def kid04_part892 : Audit := .cycle 8 3 true (1)
theorem kid04_part892_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part892) = true := by rfl

def kid04_part893 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 9 14 true (1),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 18 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3),
.cycle 9 8 true (1),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 9 12 true (1),
.cycle 17 6 false (1),
.cycle 9 8 true (1),
.cycle 1 14 true (1),
.cycle 10 5 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3)
])
theorem kid04_part893_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part893) = true := by rfl

def kid04_part894 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 13 3 false (1),
.cycle 21 5 false (4),
.cycle 15 5 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 13 4 true (0),
.cycle 15 3 false (0),
.last 16 (2,true),
.cycle 23 5 false (4),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (0),
.cycle 6 20 true (0),
.cycle 15 3 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.cycle 13 4 true (0)
])
theorem kid04_part894_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part894) = true := by rfl

def kid04_part895 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (-1),
.cycle 15 4 false (-1),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 0 20 true (-1),
.last 29 (5,true),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 8 7 false (2),
.last 19 (5,true),
.cycle 16 4 false (0),
.cycle 15 4 false (-1),
.cycle 31 4 false (5),
.cycle 27 4 false (5),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 10 7 false (2),
.cycle 30 4 false (0),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.last 16 (5,true),
.cycle 18 4 false (0)
])
theorem kid04_part895_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part895) = true := by rfl

def kid04_part896 : Audit := .split 11 (2,true) (byMove [
.cycle 13 15 true (1),
.cycle 0 27 true (-3),
.cycle 14 1 false (0),
.cycle 0 18 true (0),
.cycle 0 20 true (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 14 (5,true),
.cycle 42 1 false (8),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 12 (5,true),
.last 34 (5,true),
.cycle 11 7 false (1),
.cycle 14 14 true (-1),
.cycle 19 1 false (-1),
.cycle 17 4 false (1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 0 19 true (-1),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true)
])
theorem kid04_part896_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part896) = true := by rfl

def kid04_part897 : Audit := .cycle 1 12 true (1)
theorem kid04_part897_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part897) = true := by rfl

def kid04_part898 : Audit := .cycle 11 4 false (1)
theorem kid04_part898_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part898) = true := by rfl

def kid04_part899 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.last 22 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.cycle 11 4 true (1),
.cycle 15 6 false (0),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.cycle 13 5 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 11 4 true (1)
])
theorem kid04_part899_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part899) = true := by rfl

def kid04_part900 : Audit := .cycle 0 11 true (0)
theorem kid04_part900_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part900) = true := by rfl

def kid04_part901 : Audit := .cycle 1 10 true (1)
theorem kid04_part901_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part901) = true := by rfl

def kid04_part902 : Audit := .cycle 2 9 true (1)
theorem kid04_part902_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part902) = true := by rfl

def kid04_part903 : Audit := .cycle 1 13 true (1)
theorem kid04_part903_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part903) = true := by rfl

def kid04_part904 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 28 true (-1),
.last 13 (2,true),
.last 23 (2,true),
.cycle 13 8 false (2),
.cycle 14 3 false (0),
.cycle 1 13 true (1),
.cycle 14 9 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 4 true (2),
.cycle 15 5 false (1),
.last 18 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 10 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 10 4 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 4 true (2)
])
theorem kid04_part904_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part904) = true := by rfl

def kid04_part905 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 15 12 false (3),
.last 14 (2,true),
.cycle 10 7 true (2),
.cycle 9 6 true (1),
.cycle 16 3 false (0),
.cycle 1 14 true (1),
.cycle 15 13 false (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 9 12 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 13 2 true (2),
.cycle 14 5 false (2),
.cycle 1 14 true (1),
.cycle 10 5 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3)
])
theorem kid04_part905_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part905) = true := by rfl

def kid04_part881 : Audit := .split 10 (4,true) (byMove [(kid04_part882),(kid04_part883),(kid04_part884),(kid04_part885),(kid04_part886),(kid04_part887),(kid04_part888),(kid04_part889),(kid04_part890),(kid04_part891),(kid04_part892),(kid04_part893),(kid04_part894),(kid04_part895),(kid04_part896),(kid04_part897),(kid04_part898),(kid04_part899),(kid04_part900),(kid04_part901),(kid04_part902),(kid04_part903),(kid04_part904),(kid04_part905)])

theorem kid04_part881_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part881) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid04_part882),(kid04_part883),(kid04_part884),(kid04_part885),(kid04_part886),(kid04_part887),(kid04_part888),(kid04_part889),(kid04_part890),(kid04_part891),(kid04_part892),(kid04_part893),(kid04_part894),(kid04_part895),(kid04_part896),(kid04_part897),(kid04_part898),(kid04_part899),(kid04_part900),(kid04_part901),(kid04_part902),(kid04_part903),(kid04_part904),(kid04_part905)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part882_checked

  · exact kid04_part888_checked

  · exact kid04_part894_checked

  · exact kid04_part900_checked

  · exact kid04_part883_checked

  · exact kid04_part889_checked

  · exact kid04_part895_checked

  · exact kid04_part901_checked

  · exact kid04_part884_checked

  · exact kid04_part890_checked

  · exact kid04_part896_checked

  · exact kid04_part902_checked

  · exact kid04_part885_checked

  · exact kid04_part891_checked

  · exact kid04_part897_checked

  · exact kid04_part903_checked

  · exact kid04_part886_checked

  · exact kid04_part892_checked

  · exact kid04_part898_checked

  · exact kid04_part904_checked

  · exact kid04_part887_checked

  · exact kid04_part893_checked

  · exact kid04_part899_checked

  · exact kid04_part905_checked

def kid04_part907 : Audit := .cycle 1 11 true (1)
theorem kid04_part907_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part907) = true := by rfl

def kid04_part908 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 1 true (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 13 1 true (1),
.cycle 11 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 22 4 false (4),
.cycle 0 18 true (-1),
.cycle 13 1 true (1)
])
theorem kid04_part908_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part908) = true := by rfl

def kid04_part909 : Audit := .split 11 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 12 1 true (2),
.last 20 (4,true),
.cycle 11 7 false (1),
.cycle 0 29 true (-1),
.cycle 25 1 false (1),
.last 12 (4,true),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 18 1 false (0),
.cycle 12 1 true (2)
])
theorem kid04_part909_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part909) = true := by rfl

def kid04_part910 : Audit := .cycle 0 12 true (0)
theorem kid04_part910_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part910) = true := by rfl

def kid04_part911 : Audit := .split 11 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.cycle 17 1 true (-3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 12 1 true (2),
.cycle 17 3 false (-1),
.last 18 (2,true),
.last 12 (2,true),
.cycle 25 1 false (1),
.cycle 12 4 false (0),
.cycle 14 3 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 6 false (1),
.cycle 12 1 true (2)
])
theorem kid04_part911_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part911) = true := by rfl

def kid04_part912 : Audit := .cycle 13 1 true (-1)
theorem kid04_part912_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part912) = true := by rfl

def kid04_part913 : Audit := .cycle 0 11 true (0)
theorem kid04_part913_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part913) = true := by rfl

def kid04_part914 : Audit := .cycle 1 10 true (1)
theorem kid04_part914_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part914) = true := by rfl

def kid04_part915 : Audit := .cycle 0 23 true (0)
theorem kid04_part915_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part915) = true := by rfl

def kid04_part916 : Audit := .cycle 3 8 true (1)
theorem kid04_part916_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part916) = true := by rfl

def kid04_part917 : Audit := .cycle 8 3 true (1)
theorem kid04_part917_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part917) = true := by rfl

def kid04_part918 : Audit := .cycle 11 1 true (3)
theorem kid04_part918_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part918) = true := by rfl

def kid04_part919 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (-2),
.cycle 23 5 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 18 5 false (-2),
.cycle 25 5 false (-1),
.cycle 0 21 true (-1),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (1),
.cycle 15 3 false (0),
.last 19 (2,true),
.cycle 0 25 true (-2),
.cycle 18 1 false (-2),
.cycle 18 5 false (-2),
.cycle 18 5 false (-1),
.last 48 (2,true),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 20 5 false (1),
.cycle 13 5 false (1),
.cycle 9 9 false (2)
])
theorem kid04_part919_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part919) = true := by rfl

def kid04_part920 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 21 (2,true),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 13 4 false (2),
.cycle 11 3 false (1),
.last 14 (2,true),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.last 16 (2,true),
.cycle 9 4 true (0)
])
theorem kid04_part920_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part920) = true := by rfl

def kid04_part921 : Audit := .split 11 (2,true) (byMove [
.cycle 13 15 true (1),
.last 24 (4,true),
.cycle 14 1 false (0),
.last 15 (4,true),
.last 12 (4,true),
.last 17 (4,true),
.cycle 1 12 true (1),
.cycle 24 5 false (4),
.cycle 42 1 false (8),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 15 true (0),
.last 20 (4,true),
.cycle 11 7 false (1),
.cycle 14 14 true (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 18 3 false (1),
.cycle 1 12 true (1),
.last 13 (4,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1)
])
theorem kid04_part921_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part921) = true := by rfl

def kid04_part922 : Audit := .cycle 1 12 true (1)
theorem kid04_part922_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part922) = true := by rfl

def kid04_part923 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.last 22 (2,true),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 12 4 false (0),
.cycle 9 9 false (2),
.cycle 1 12 true (1),
.cycle 15 5 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (1),
.cycle 14 5 false (0),
.cycle 17 3 false (-1),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 12 4 false (0),
.cycle 14 3 false (-1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 5 true (1),
.cycle 10 2 true (1)
])
theorem kid04_part923_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part923) = true := by rfl

def kid04_part924 : Audit := .cycle 11 3 false (1)
theorem kid04_part924_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part924) = true := by rfl

def kid04_part925 : Audit := .cycle 0 11 true (0)
theorem kid04_part925_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part925) = true := by rfl

def kid04_part926 : Audit := .cycle 1 10 true (1)
theorem kid04_part926_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part926) = true := by rfl

def kid04_part927 : Audit := .cycle 2 9 true (1)
theorem kid04_part927_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part927) = true := by rfl

def kid04_part928 : Audit := .cycle 1 13 true (1)
theorem kid04_part928_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part928) = true := by rfl

def kid04_part929 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 16 15 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 8 false (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 27 (2,true),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 14 1 true (4),
.cycle 16 13 false (2),
.last 26 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 6 false (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (2),
.cycle 14 1 true (4)
])
theorem kid04_part929_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part929) = true := by rfl

def kid04_part930 : Audit := .cycle 11 1 true (3)
theorem kid04_part930_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part930) = true := by rfl

def kid04_part906 : Audit := .split 10 (5,true) (byMove [(kid04_part907),(kid04_part908),(kid04_part909),(kid04_part910),(kid04_part911),(kid04_part912),(kid04_part913),(kid04_part914),(kid04_part915),(kid04_part916),(kid04_part917),(kid04_part918),(kid04_part919),(kid04_part920),(kid04_part921),(kid04_part922),(kid04_part923),(kid04_part924),(kid04_part925),(kid04_part926),(kid04_part927),(kid04_part928),(kid04_part929),(kid04_part930)])

theorem kid04_part906_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part906) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part907),(kid04_part908),(kid04_part909),(kid04_part910),(kid04_part911),(kid04_part912),(kid04_part913),(kid04_part914),(kid04_part915),(kid04_part916),(kid04_part917),(kid04_part918),(kid04_part919),(kid04_part920),(kid04_part921),(kid04_part922),(kid04_part923),(kid04_part924),(kid04_part925),(kid04_part926),(kid04_part927),(kid04_part928),(kid04_part929),(kid04_part930)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part907_checked

  · exact kid04_part913_checked

  · exact kid04_part919_checked

  · exact kid04_part925_checked

  · exact kid04_part908_checked

  · exact kid04_part914_checked

  · exact kid04_part920_checked

  · exact kid04_part926_checked

  · exact kid04_part909_checked

  · exact kid04_part915_checked

  · exact kid04_part921_checked

  · exact kid04_part927_checked

  · exact kid04_part910_checked

  · exact kid04_part916_checked

  · exact kid04_part922_checked

  · exact kid04_part928_checked

  · exact kid04_part911_checked

  · exact kid04_part917_checked

  · exact kid04_part923_checked

  · exact kid04_part929_checked

  · exact kid04_part912_checked

  · exact kid04_part918_checked

  · exact kid04_part924_checked

  · exact kid04_part930_checked

def kid04_part618 : Audit := .split 9 (5,false) (byMove [(kid04_part619),(kid04_part644),(kid04_part669),(kid04_part670),(kid04_part671),(kid04_part672),(kid04_part697),(kid04_part698),(kid04_part723),(kid04_part724),(kid04_part725),(kid04_part726),(kid04_part727),(kid04_part752),(kid04_part777),(kid04_part802),(kid04_part803),(kid04_part828),(kid04_part853),(kid04_part854),(kid04_part855),(kid04_part880),(kid04_part881),(kid04_part906)])

theorem kid04_part618_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (kid04_part618) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part619),(kid04_part644),(kid04_part669),(kid04_part670),(kid04_part671),(kid04_part672),(kid04_part697),(kid04_part698),(kid04_part723),(kid04_part724),(kid04_part725),(kid04_part726),(kid04_part727),(kid04_part752),(kid04_part777),(kid04_part802),(kid04_part803),(kid04_part828),(kid04_part853),(kid04_part854),(kid04_part855),(kid04_part880),(kid04_part881),(kid04_part906)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part619_checked

  · exact kid04_part697_checked

  · exact kid04_part727_checked

  · exact kid04_part853_checked

  · exact kid04_part644_checked

  · exact kid04_part698_checked

  · exact kid04_part752_checked

  · exact kid04_part854_checked

  · exact kid04_part669_checked

  · exact kid04_part723_checked

  · exact kid04_part777_checked

  · exact kid04_part855_checked

  · exact kid04_part670_checked

  · exact kid04_part724_checked

  · exact kid04_part802_checked

  · exact kid04_part880_checked

  · exact kid04_part671_checked

  · exact kid04_part725_checked

  · exact kid04_part803_checked

  · exact kid04_part881_checked

  · exact kid04_part672_checked

  · exact kid04_part726_checked

  · exact kid04_part828_checked

  · exact kid04_part906_checked

def kid04_part931 : Audit := .cycle 0 9 true (0)
theorem kid04_part931_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,0⟩)) (kid04_part931) = true := by rfl

def kid04_part932 : Audit := .cycle 1 8 true (1)
theorem kid04_part932_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,1⟩)) (kid04_part932) = true := by rfl

def kid04_part933 : Audit := .cycle 2 7 true (1)
theorem kid04_part933_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,2⟩)) (kid04_part933) = true := by rfl

def kid04_part934 : Audit := .cycle 1 11 true (1)
theorem kid04_part934_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,3⟩)) (kid04_part934) = true := by rfl

def kid04_part935 : Audit := .cycle 8 1 true (2)
theorem kid04_part935_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,4⟩)) (kid04_part935) = true := by rfl

def kid04_part937 : Audit := .cycle 1 10 true (1)
theorem kid04_part937_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part937) = true := by rfl

def kid04_part938 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 22 3 false (0),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.cycle 22 3 false (2),
.cycle 13 3 false (1),
.split 16 (2,true) (byMove [
.cycle 24 3 false (2),
.cycle 17 3 false (-1),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 8 9 false (3),
.cycle 1 17 false (3),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.cycle 27 3 false (3),
.cycle 25 3 false (3),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 30 7 false (2),
.cycle 31 3 false (-1),
.cycle 2 15 false (3),
.cycle 7 25 false (4),
.cycle 21 3 false (-1),
.cycle 12 5 false (2)
]),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.split 16 (5,true) (byMove [
.cycle 24 3 false (2),
.cycle 17 3 false (-1),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 14 3 false (0),
.cycle 25 3 false (-1),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 8 9 false (3),
.cycle 1 17 false (3),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.last 17 (2,true),
.cycle 25 3 false (3),
.cycle 14 3 false (0),
.cycle 7 31 false (3),
.cycle 37 21 false (2),
.cycle 29 5 false (1),
.cycle 2 15 false (3),
.cycle 7 25 false (4),
.cycle 20 5 false (0),
.cycle 12 5 false (2)
]),
.cycle 0 19 true (-2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 24 3 false (4),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
])
theorem kid04_part938_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part938) = true := by rfl

def kid04_part939 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.cycle 17 1 false (1),
.cycle 14 3 false (0),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 3 false (2),
.cycle 25 3 false (4),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 20 1 false (2),
.cycle 8 3 true (2),
.cycle 24 1 false (2),
.split 13 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 29 1 false (1),
.cycle 19 3 false (0),
.cycle 14 10 false (0),
.cycle 0 25 true (-2),
.cycle 29 1 false (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 19 11 false (2),
.cycle 19 5 false (1)
]),
.split 14 (4,true) (byMove [
.cycle 0 19 true (-1),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.cycle 17 1 false (-1),
.cycle 0 18 true (0),
.cycle 15 6 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.last 16 (5,true),
.cycle 17 1 false (1),
.cycle 13 3 false (1),
.cycle 15 6 false (0),
.cycle 0 22 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 17 1 false (-1),
.cycle 0 18 true (0),
.cycle 11 4 true (0),
.cycle 0 17 true (0),
.cycle 18 6 false (2),
.last 16 (5,true),
.cycle 15 6 false (1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 2 12 true (1),
.last 18 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.last 15 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (2),
.cycle 9 2 true (2)
])
theorem kid04_part939_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part939) = true := by rfl

def kid04_part940 : Audit := .cycle 0 11 true (0)
theorem kid04_part940_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part940) = true := by rfl

def kid04_part941 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 14 3 false (0),
.cycle 11 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 20 1 false (2),
.cycle 8 3 true (2),
.cycle 8 4 true (2),
.cycle 18 3 false (0),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 14 6 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 17 3 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 18 10 false (1),
.cycle 18 7 false (0),
.cycle 14 6 false (0),
.cycle 16 16 true (-1),
.cycle 1 14 true (1),
.cycle 17 3 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 25 (5,true),
.cycle 16 8 false (1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 14 6 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.cycle 13 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 32, 0, 64],[2, 0, 64, 1, 32, 32, 64],64⟩,
.cycle 18 7 false (0),
.cycle 14 6 false (0),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 14 3 false (0),
.cycle 13 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 16 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 32, 0, 64],[2, 0, 64, 1, 32, 32, 64],64⟩
]),
.cycle 11 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (2),
.cycle 9 2 true (2)
])
theorem kid04_part941_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part941) = true := by rfl

def kid04_part942 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.cycle 15 1 false (1),
.cycle 14 3 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 3 false (2),
.cycle 25 3 false (4),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 36 1 false (8),
.cycle 20 1 false (2),
.cycle 8 3 true (2),
.cycle 15 1 false (1),
.split 13 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 20 1 false (0),
.cycle 19 3 false (0),
.last 22 (2,true),
.last 14 (2,true),
.cycle 29 1 false (1),
.cycle 14 10 false (0),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 19 11 false (2),
.cycle 19 5 false (1)
]),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 3 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 18 5 false (0),
.cycle 18 7 false (0),
.last 14 (4,true),
.cycle 16 16 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 3 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 17 (4,true),
.last 16 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.last 26 (2,true),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 17 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (1),
.cycle 10 4 true (1),
.cycle 21 3 false (-1),
.last 22 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.cycle 18 1 false (-2),
.cycle 1 14 true (1),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 5 true (1),
.cycle 12 2 true (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (2),
.cycle 9 2 true (2)
])
theorem kid04_part942_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part942) = true := by rfl

def kid04_part943 : Audit := .cycle 0 10 true (0)
theorem kid04_part943_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part943) = true := by rfl

def kid04_part944 : Audit := .cycle 1 9 true (1)
theorem kid04_part944_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part944) = true := by rfl

def kid04_part945 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (2),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 4, 1, 4096, 4096, 2, 4096, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 11 9 true (2),
.cycle 8 12 true (2),
.split 33 (5,true) (byMove [
.cycle 0 50 true (0),
.cycle 0 37 true (0),
.cycle 10 35 true (2),
.cycle 0 43 true (0),
.cycle 17 17 true (3),
.cycle 0 37 true (0),
.cycle 1 34 true (1),
.cycle 7 27 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 32, 1, 4096, 4, 2, 4096, 32, 1, 4096, 4, 4096],4096⟩,
.cycle 0 35 true (0),
.last 34 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 32, 1, 4096, 32, 2, 4096, 32, 1, 4096, 32, 4096],4096⟩,
.last 36 (4,true),
.cycle 35 15 true (7),
.cycle 1 36 true (1),
.cycle 12 31 true (2),
.last 36 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 32, 1, 4096, 32, 2, 4096, 32, 1, 4096, 32, 4096],4096⟩,
.cycle 1 34 true (1),
.last 35 (4,true),
.cycle 2 46 true (1),
.cycle 0 35 true (0),
.last 34 (4,true),
.cycle 9 26 true (2)
]),
.split 22 (4,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 53 1 false (1),
.cycle 0 24 true (0),
.cycle 8 16 true (2),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 10 13 true (2),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 32, 64, 64],64⟩,
.cycle 6 17 true (2),
.cycle 0 47 true (-1),
.cycle 0 34 true (0),
.cycle 1 24 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 8 15 true (2),
.cycle 9 14 true (2)
]),
.split 23 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 12 14 true (2),
.cycle 39 1 false (1),
.cycle 45 1 false (1),
.cycle 0 28 true (0),
.cycle 42 1 false (2),
.cycle 0 27 true (0),
.cycle 16 10 true (3),
.cycle 0 26 true (0),
.cycle 38 1 false (2),
.last 25 (5,true),
.cycle 16 12 true (3),
.cycle 46 3 false (2),
.cycle 34 10 false (1),
.cycle 0 31 true (0),
.cycle 36 1 false (0),
.last 25 (5,true),
.last 36 (5,true),
.cycle 0 27 true (0),
.cycle 20 4 true (3),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.last 25 (5,true),
.cycle 18 6 true (3)
]),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.split 21 (5,true) (byMove [
.cycle 1 22 true (1),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 42 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 10 12 true (2),
.cycle 3 19 true (1),
.cycle 8 14 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 32, 1, 4096, 32, 2, 4096, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 6 16 true (2),
.last 23 (4,true),
.last 23 (4,true),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 33 5 false (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 8 14 true (2),
.cycle 9 13 true (2)
]),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (2),
.cycle 9 11 true (2)
])
theorem kid04_part945_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part945) = true := by rfl

def kid04_part946 : Audit := .cycle 3 7 true (1)
theorem kid04_part946_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part946) = true := by rfl

def kid04_part947 : Audit := .cycle 8 2 true (2)
theorem kid04_part947_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part947) = true := by rfl

def kid04_part948 : Audit := .cycle 9 1 true (3)
theorem kid04_part948_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part948) = true := by rfl

def kid04_part949 : Audit := .cycle 6 4 true (2)
theorem kid04_part949_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part949) = true := by rfl

def kid04_part951 : Audit := .cycle 32 32 true (-1)
theorem kid04_part951_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part951) = true := by rfl

def kid04_part952 : Audit := .cycle 21 3 false (1)
theorem kid04_part952_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part952) = true := by rfl

def kid04_part953 : Audit := .cycle 16 1 false (0)
theorem kid04_part953_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part953) = true := by rfl

def kid04_part954 : Audit := .cycle 15 1 false (-1)
theorem kid04_part954_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part954) = true := by rfl

def kid04_part955 : Audit := .cycle 15 3 false (0)
theorem kid04_part955_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part955) = true := by rfl

def kid04_part956 : Audit := .split 17 (2,true) (byMove [
.cycle 25 3 false (1),
.cycle 18 3 false (-2),
.cycle 20 1 false (-2),
.last 47 (5,true),
.cycle 14 4 false (0),
.last 18 (5,true),
.last 42 (5,true),
.cycle 45 3 false (-1),
.cycle 24 3 false (0),
.cycle 22 3 false (0),
.cycle 8 10 false (3),
.last 24 (5,true),
.cycle 19 3 false (-1),
.cycle 18 3 false (-2),
.cycle 38 22 true (-3),
.cycle 36 20 true (-2),
.cycle 14 4 false (0),
.last 18 (5,true),
.last 39 (5,true),
.last 45 (5,true),
.cycle 2 16 false (3),
.cycle 16 32 true (-2),
.last 22 (5,true),
.cycle 12 6 false (2)
])
theorem kid04_part956_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part956) = true := by rfl

def kid04_part957 : Audit := .cycle 0 21 true (0)
theorem kid04_part957_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part957) = true := by rfl

def kid04_part958 : Audit := .split 16 (2,true) (byMove [
.cycle 27 3 false (5),
.cycle 17 3 false (1),
.cycle 19 1 false (1),
.cycle 27 3 false (5),
.cycle 27 3 false (5),
.last 17 (5,true),
.cycle 6 45 true (0),
.cycle 10 33 true (0),
.cycle 25 3 false (3),
.cycle 0 18 true (0),
.cycle 7 45 true (0),
.last 17 (5,true),
.cycle 18 3 false (2),
.cycle 17 3 false (1),
.cycle 21 3 false (3),
.cycle 19 3 false (3),
.cycle 18 3 false (2),
.last 17 (5,true),
.cycle 0 45 true (0),
.cycle 1 41 true (0),
.cycle 2 16 true (0),
.cycle 0 18 true (0),
.cycle 39 6 true (4),
.last 17 (5,true)
])
theorem kid04_part958_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part958) = true := by rfl

def kid04_part959 : Audit := .cycle 24 3 false (6)
theorem kid04_part959_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part959) = true := by rfl

def kid04_part960 : Audit := .cycle 15 1 false (1)
theorem kid04_part960_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part960) = true := by rfl

def kid04_part961 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 17 3 false (1),
.last 17 (2,true),
.cycle 21 3 false (4),
.cycle 21 3 false (4),
.last 20 (2,true),
.cycle 6 45 true (0),
.cycle 10 33 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 2048, 4096, 128, 256, 8, 2, 2048, 16, 4096],[2, 16, 4096, 1, 16, 16, 2, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.last 20 (2,true),
.cycle 18 3 false (2),
.cycle 17 3 false (1),
.last 17 (2,true),
.cycle 19 3 false (3),
.cycle 20 3 false (5),
.last 20 (2,true),
.cycle 0 45 true (0),
.cycle 8 11 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 8 10 true (0),
.cycle 17 5 true (2)
])
theorem kid04_part961_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part961) = true := by rfl

def kid04_part962 : Audit := .split 17 (2,true) (byMove [
.cycle 31 3 false (5),
.cycle 18 3 false (0),
.cycle 20 1 false (0),
.cycle 0 33 true (0),
.cycle 14 4 true (0),
.last 18 (5,true),
.cycle 6 12 true (0),
.cycle 10 8 true (0),
.cycle 28 3 false (2),
.cycle 32 16 true (0),
.last 19 (5,true),
.last 18 (5,true),
.cycle 19 3 false (1),
.cycle 18 3 false (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.last 19 (5,true),
.last 18 (5,true),
.cycle 10 39 true (0),
.cycle 1 27 true (0),
.cycle 2 18 true (0),
.cycle 5 51 true (0),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid04_part962_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part962) = true := by rfl

def kid04_part963 : Audit := .cycle 13 3 false (1)
theorem kid04_part963_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part963) = true := by rfl

def kid04_part964 : Audit := .split 16 (2,true) (byMove [
.cycle 34 18 true (-1),
.cycle 17 3 false (-1),
.cycle 19 1 false (-1),
.cycle 0 28 true (-1),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 0 27 true (-1),
.cycle 10 39 true (-1),
.cycle 32 19 false (4),
.cycle 21 3 false (1),
.last 18 (5,true),
.last 20 (5,true),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.cycle 27 3 false (3),
.cycle 23 3 false (3),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 13 7 false (2),
.cycle 23 3 false (-1),
.cycle 43 3 false (-1),
.cycle 4 13 false (3),
.last 18 (5,true),
.cycle 12 5 false (2)
])
theorem kid04_part964_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part964) = true := by rfl

def kid04_part965 : Audit := .cycle 0 27 true (-1)
theorem kid04_part965_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part965) = true := by rfl

def kid04_part966 : Audit := .cycle 15 1 false (-1)
theorem kid04_part966_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part966) = true := by rfl

def kid04_part967 : Audit := .split 16 (5,true) (byMove [
.cycle 34 18 true (-1),
.cycle 17 3 false (-1),
.last 17 (2,true),
.last 20 (2,true),
.cycle 14 3 false (0),
.last 20 (2,true),
.cycle 0 27 true (-1),
.last 18 (2,true),
.cycle 32 19 false (4),
.cycle 21 3 false (1),
.cycle 14 18 true (-1),
.last 19 (2,true),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.last 17 (2,true),
.last 20 (2,true),
.cycle 14 3 false (0),
.last 20 (2,true),
.last 35 (2,true),
.last 18 (2,true),
.last 46 (2,true),
.cycle 4 13 false (3),
.cycle 21 5 false (1),
.cycle 12 5 false (2)
])
theorem kid04_part967_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part967) = true := by rfl

def kid04_part968 : Audit := .split 17 (2,true) (byMove [
.cycle 38 22 true (-2),
.cycle 18 3 false (-2),
.cycle 20 1 false (-2),
.cycle 13 7 false (1),
.cycle 14 4 false (0),
.last 18 (5,true),
.cycle 6 57 true (-2),
.cycle 10 8 false (2),
.cycle 34 24 false (4),
.cycle 0 33 true (-2),
.cycle 19 3 false (-1),
.last 18 (5,true),
.cycle 19 3 false (-1),
.cycle 18 3 false (-2),
.cycle 22 3 false (0),
.cycle 20 3 false (0),
.cycle 14 4 false (0),
.last 18 (5,true),
.last 39 (5,true),
.last 20 (5,true),
.last 45 (5,true),
.cycle 12 10 false (2),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid04_part968_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part968) = true := by rfl

def kid04_part969 : Audit := .cycle 0 21 true (0)
theorem kid04_part969_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part969) = true := by rfl

def kid04_part970 : Audit := .split 16 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 2, 64, 64],64⟩,
.cycle 0 22 true (0),
.cycle 20 1 false (0),
.cycle 1 20 true (0),
.cycle 1 20 true (0),
.last 17 (5,true),
.cycle 6 45 true (0),
.cycle 10 33 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 32, 4, 64],[2, 4, 4, 1, 2, 64, 64],64⟩,
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 17 (5,true),
.cycle 10 8 true (0),
.cycle 13 4 true (0),
.cycle 22 3 false (2),
.cycle 5 12 true (0),
.cycle 1 24 true (0),
.last 17 (5,true),
.cycle 0 45 true (0),
.cycle 1 18 true (0),
.cycle 2 16 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 17 (5,true)
])
theorem kid04_part970_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part970) = true := by rfl

def kid04_part971 : Audit := .cycle 30 14 true (0)
theorem kid04_part971_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part971) = true := by rfl

def kid04_part972 : Audit := .cycle 18 3 false (2)
theorem kid04_part972_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part972) = true := by rfl

def kid04_part973 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 11 8 true (0),
.last 17 (2,true),
.cycle 0 28 true (0),
.cycle 17 7 true (1),
.last 21 (2,true),
.cycle 6 45 true (0),
.cycle 10 33 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 8 16 true (0),
.last 20 (2,true),
.cycle 10 8 true (0),
.cycle 13 4 true (0),
.last 17 (2,true),
.cycle 5 12 true (0),
.cycle 18 8 true (2),
.last 21 (2,true),
.cycle 0 45 true (0),
.cycle 1 24 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 18 6 true (3),
.cycle 17 5 true (2)
])
theorem kid04_part973_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part973) = true := by rfl

def kid04_part974 : Audit := .cycle 15 3 false (1)
theorem kid04_part974_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part974) = true := by rfl

def kid04_part950 : Audit := .split 14 (4,true) (byMove [(kid04_part951),(kid04_part952),(kid04_part953),(kid04_part954),(kid04_part955),(kid04_part956),(kid04_part957),(kid04_part958),(kid04_part959),(kid04_part960),(kid04_part961),(kid04_part962),(kid04_part963),(kid04_part964),(kid04_part965),(kid04_part966),(kid04_part967),(kid04_part968),(kid04_part969),(kid04_part970),(kid04_part971),(kid04_part972),(kid04_part973),(kid04_part974)])

theorem kid04_part950_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part950) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 14 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some mv)) (byMove [(kid04_part951),(kid04_part952),(kid04_part953),(kid04_part954),(kid04_part955),(kid04_part956),(kid04_part957),(kid04_part958),(kid04_part959),(kid04_part960),(kid04_part961),(kid04_part962),(kid04_part963),(kid04_part964),(kid04_part965),(kid04_part966),(kid04_part967),(kid04_part968),(kid04_part969),(kid04_part970),(kid04_part971),(kid04_part972),(kid04_part973),(kid04_part974)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part951_checked

  · exact kid04_part957_checked

  · exact kid04_part963_checked

  · exact kid04_part969_checked

  · exact kid04_part952_checked

  · exact kid04_part958_checked

  · exact kid04_part964_checked

  · exact kid04_part970_checked

  · exact kid04_part953_checked

  · exact kid04_part959_checked

  · exact kid04_part965_checked

  · exact kid04_part971_checked

  · exact kid04_part954_checked

  · exact kid04_part960_checked

  · exact kid04_part966_checked

  · exact kid04_part972_checked

  · exact kid04_part955_checked

  · exact kid04_part961_checked

  · exact kid04_part967_checked

  · exact kid04_part973_checked

  · exact kid04_part956_checked

  · exact kid04_part962_checked

  · exact kid04_part968_checked

  · exact kid04_part974_checked

def kid04_part976 : Audit := .cycle 1 14 true (1)
theorem kid04_part976_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid04_part976) = true := by rfl

def kid04_part977 : Audit := .cycle 0 14 true (0)
theorem kid04_part977_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid04_part977) = true := by rfl

def kid04_part978 : Audit := .cycle 21 1 false (1)
theorem kid04_part978_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid04_part978) = true := by rfl

def kid04_part979 : Audit := .cycle 0 17 true (0)
theorem kid04_part979_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid04_part979) = true := by rfl

def kid04_part980 : Audit := .split 14 (4,true) (byMove [
.cycle 33 32 true (-1),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.last 22 (5,true),
.cycle 0 21 true (0),
.cycle 28 3 false (5),
.cycle 25 3 false (6),
.cycle 15 1 false (1),
.last 16 (5,true),
.cycle 20 3 false (3),
.cycle 14 3 false (0),
.cycle 13 3 false (1),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 40 3 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 31 14 true (0),
.cycle 19 3 false (2),
.last 16 (5,true),
.cycle 15 3 false (1)
])
theorem kid04_part980_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid04_part980) = true := by rfl

def kid04_part981 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 false (3),
.cycle 11 16 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 11 9 false (1),
.cycle 0 26 true (-2),
.last 22 (5,true),
.cycle 0 22 true (-2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 29 (5,true),
.cycle 0 28 true (-2),
.cycle 16 3 false (1),
.last 21 (5,true),
.last 24 (5,true),
.cycle 19 1 false (-1),
.last 20 (5,true),
.cycle 0 26 true (-2),
.last 22 (5,true),
.cycle 0 22 true (-2),
.cycle 0 36 true (-2),
.last 24 (5,true),
.last 22 (5,true),
.cycle 11 8 true (-2)
])
theorem kid04_part981_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid04_part981) = true := by rfl

def kid04_part982 : Audit := .cycle 1 11 true (1)
theorem kid04_part982_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid04_part982) = true := by rfl

def kid04_part983 : Audit := .cycle 7 4 true (2)
theorem kid04_part983_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid04_part983) = true := by rfl

def kid04_part984 : Audit := .cycle 29 1 false (7)
theorem kid04_part984_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid04_part984) = true := by rfl

def kid04_part985 : Audit := .cycle 0 12 true (0)
theorem kid04_part985_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid04_part985) = true := by rfl

def kid04_part986 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (9),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 23 3 false (1),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part986_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid04_part986) = true := by rfl

def kid04_part987 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 31 true (0),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part987_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid04_part987) = true := by rfl

def kid04_part988 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 14 13 false (0),
.cycle 19 1 false (-1),
.cycle 31 1 false (-1),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 15 (5,true),
.cycle 1 17 true (1),
.cycle 19 3 false (0),
.cycle 14 10 false (0),
.cycle 0 53 true (-2),
.cycle 26 1 false (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 20 15 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 19 5 false (1)
])
theorem kid04_part988_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid04_part988) = true := by rfl

def kid04_part989 : Audit := .split 14 (4,true) (byMove [
.cycle 32 17 false (4),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.cycle 11 8 true (-2),
.cycle 0 21 true (0),
.cycle 15 6 false (2),
.cycle 24 6 false (6),
.cycle 15 1 false (1),
.last 16 (5,true),
.cycle 19 6 false (3),
.cycle 13 3 false (1),
.cycle 15 6 false (0),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 19 6 false (2),
.cycle 0 21 true (0),
.cycle 11 4 true (0),
.cycle 39 6 false (1),
.cycle 18 6 false (2),
.last 16 (5,true),
.cycle 15 6 false (1)
])
theorem kid04_part989_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid04_part989) = true := by rfl

def kid04_part990 : Audit := .cycle 1 13 true (1)
theorem kid04_part990_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid04_part990) = true := by rfl

def kid04_part991 : Audit := .cycle 18 1 false (0)
theorem kid04_part991_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid04_part991) = true := by rfl

def kid04_part992 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 22 true (-2),
.cycle 1 13 true (1),
.last 17 (4,true),
.cycle 10 18 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 17 true (0),
.last 18 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 13 11 false (1),
.cycle 1 13 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid04_part992_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid04_part992) = true := by rfl

def kid04_part993 : Audit := .cycle 11 8 true (-2)
theorem kid04_part993_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid04_part993) = true := by rfl

def kid04_part994 : Audit := .cycle 1 11 true (1)
theorem kid04_part994_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid04_part994) = true := by rfl

def kid04_part995 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 5 false (0),
.cycle 0 20 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 0 16 true (0),
.cycle 21 3 false (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 39 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 9 4 true (2)
])
theorem kid04_part995_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid04_part995) = true := by rfl

def kid04_part996 : Audit := .cycle 2 10 true (1)
theorem kid04_part996_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid04_part996) = true := by rfl

def kid04_part997 : Audit := .cycle 0 12 true (0)
theorem kid04_part997_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid04_part997) = true := by rfl

def kid04_part998 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 5 false (1),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 17 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 22 (5,true),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part998_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid04_part998) = true := by rfl

def kid04_part999 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.last 18 (4,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 20 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 18 (4,true),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 13 10 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part999_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid04_part999) = true := by rfl

def kid04_part975 : Audit := .split 10 (2,true) (byMove [(kid04_part976),(kid04_part977),(kid04_part978),(kid04_part979),(kid04_part980),(kid04_part981),(kid04_part982),(kid04_part983),(kid04_part984),(kid04_part985),(kid04_part986),(kid04_part987),(kid04_part988),(kid04_part989),(kid04_part990),(kid04_part991),(kid04_part992),(kid04_part993),(kid04_part994),(kid04_part995),(kid04_part996),(kid04_part997),(kid04_part998),(kid04_part999)])

theorem kid04_part975_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part975) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid04_part976),(kid04_part977),(kid04_part978),(kid04_part979),(kid04_part980),(kid04_part981),(kid04_part982),(kid04_part983),(kid04_part984),(kid04_part985),(kid04_part986),(kid04_part987),(kid04_part988),(kid04_part989),(kid04_part990),(kid04_part991),(kid04_part992),(kid04_part993),(kid04_part994),(kid04_part995),(kid04_part996),(kid04_part997),(kid04_part998),(kid04_part999)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part976_checked

  · exact kid04_part982_checked

  · exact kid04_part988_checked

  · exact kid04_part994_checked

  · exact kid04_part977_checked

  · exact kid04_part983_checked

  · exact kid04_part989_checked

  · exact kid04_part995_checked

  · exact kid04_part978_checked

  · exact kid04_part984_checked

  · exact kid04_part990_checked

  · exact kid04_part996_checked

  · exact kid04_part979_checked

  · exact kid04_part985_checked

  · exact kid04_part991_checked

  · exact kid04_part997_checked

  · exact kid04_part980_checked

  · exact kid04_part986_checked

  · exact kid04_part992_checked

  · exact kid04_part998_checked

  · exact kid04_part981_checked

  · exact kid04_part987_checked

  · exact kid04_part993_checked

  · exact kid04_part999_checked

def kid04_part1000 : Audit := .cycle 1 11 true (1)
theorem kid04_part1000_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part1000) = true := by rfl

def kid04_part1002 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 0 32 true (0),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 2048, 4096, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 4, 1, 256, 4096, 2, 8, 4, 1, 256, 4096, 4096],4128⟩,
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.last 16 (5,true),
.cycle 6 16 true (1),
.cycle 0 20 true (0),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.cycle 10 8 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (2),
.cycle 12 5 true (2)
])
theorem kid04_part1002_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part1002) = true := by rfl

def kid04_part1003 : Audit := .cycle 0 14 true (0)
theorem kid04_part1003_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part1003) = true := by rfl

def kid04_part1004 : Audit := .cycle 21 1 false (1)
theorem kid04_part1004_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part1004) = true := by rfl

def kid04_part1005 : Audit := .split 15 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 17 1 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 34 1 false (2),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 8 8 true (0),
.last 18 (5,true),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 30 1 false (4),
.cycle 28 1 false (4),
.cycle 17 1 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 38 1 false (2),
.cycle 36 1 false (4),
.cycle 22 1 false (2)
])
theorem kid04_part1005_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part1005) = true := by rfl

def kid04_part1006 : Audit := .cycle 14 3 false (0)
theorem kid04_part1006_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part1006) = true := by rfl

def kid04_part1007 : Audit := .split 15 (5,true) (byMove [
.cycle 0 44 true (-2),
.cycle 11 7 false (1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 10 8 false (2),
.last 17 (2,true),
.cycle 0 55 true (-2),
.cycle 11 11 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 23 3 true (3),
.cycle 11 8 false (1),
.cycle 11 7 false (1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 24 true (-2),
.last 17 (2,true),
.cycle 15 20 true (-1),
.cycle 4 12 false (3),
.cycle 17 6 true (1),
.cycle 11 8 false (1)
])
theorem kid04_part1007_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part1007) = true := by rfl

def kid04_part1008 : Audit := .cycle 1 11 true (1)
theorem kid04_part1008_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part1008) = true := by rfl

def kid04_part1009 : Audit := .cycle 7 4 true (2)
theorem kid04_part1009_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part1009) = true := by rfl

def kid04_part1010 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 48 1 false (8),
.cycle 32 7 false (6),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1010_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part1010) = true := by rfl

def kid04_part1011 : Audit := .cycle 0 12 true (0)
theorem kid04_part1011_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part1011) = true := by rfl

def kid04_part1012 : Audit := .cycle 8 4 true (2)
theorem kid04_part1012_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part1012) = true := by rfl

def kid04_part1013 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.cycle 11 3 true (3),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1013_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part1013) = true := by rfl

def kid04_part1014 : Audit := .cycle 18 3 false (0)
theorem kid04_part1014_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part1014) = true := by rfl

def kid04_part1015 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 14 6 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.cycle 17 3 false (-1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 27 10 false (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 399, 2048, 4096, 128, 256, 8, 2, 2048, 399, 4096],[2, 399, 4, 1, 4, 4096, 2, 399, 4, 1, 399, 4096, 4096],4128⟩,
.cycle 0 14 true (0),
.cycle 8 8 true (1),
.last 13 (5,true),
.cycle 18 7 false (0),
.cycle 14 6 false (0),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.cycle 17 3 false (-1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 37 8 false (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 28 (5,true),
.last 13 (5,true)
])
theorem kid04_part1015_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part1015) = true := by rfl

def kid04_part1016 : Audit := .cycle 1 13 true (1)
theorem kid04_part1016_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part1016) = true := by rfl

def kid04_part1017 : Audit := .cycle 18 1 false (0)
theorem kid04_part1017_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part1017) = true := by rfl

def kid04_part1018 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 14 6 false (0),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 14 3 false (0),
.cycle 13 4 false (1),
.cycle 1 13 true (1),
.cycle 17 7 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 8 true (1),
.cycle 13 3 true (3),
.cycle 18 7 false (0),
.cycle 14 6 false (0),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.cycle 13 4 false (1),
.cycle 1 13 true (1),
.cycle 15 5 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid04_part1018_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part1018) = true := by rfl

def kid04_part1019 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 11 7 false (1),
.last 16 (2,true),
.cycle 12 7 false (0),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 6 10 false (3),
.cycle 11 12 false (1),
.last 16 (2,true),
.cycle 25 15 true (0),
.cycle 10 6 false (2),
.cycle 19 3 true (3),
.cycle 11 8 false (1),
.cycle 11 7 false (1),
.last 16 (2,true),
.cycle 11 9 false (1),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 15 6 true (-1),
.cycle 12 8 false (0),
.last 16 (2,true),
.cycle 5 20 false (3),
.cycle 15 2 true (-1),
.cycle 17 5 true (1)
])
theorem kid04_part1019_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part1019) = true := by rfl

def kid04_part1020 : Audit := .cycle 1 11 true (1)
theorem kid04_part1020_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part1020) = true := by rfl

def kid04_part1021 : Audit := .cycle 1 12 true (1)
theorem kid04_part1021_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part1021) = true := by rfl

def kid04_part1022 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 24 5 false (2),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 2048, 4096, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 4, 1, 256, 4096, 2, 8, 4, 1, 256, 4096, 4096],4128⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 38 20 true (0),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1022_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part1022) = true := by rfl

def kid04_part1023 : Audit := .cycle 0 12 true (0)
theorem kid04_part1023_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part1023) = true := by rfl

def kid04_part1024 : Audit := .cycle 8 4 true (2)
theorem kid04_part1024_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part1024) = true := by rfl

def kid04_part1025 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 19 5 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 11 3 true (3),
.cycle 6 6 true (2),
.cycle 19 5 false (1),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1025_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part1025) = true := by rfl

def kid04_part1001 : Audit := .split 10 (4,true) (byMove [(kid04_part1002),(kid04_part1003),(kid04_part1004),(kid04_part1005),(kid04_part1006),(kid04_part1007),(kid04_part1008),(kid04_part1009),(kid04_part1010),(kid04_part1011),(kid04_part1012),(kid04_part1013),(kid04_part1014),(kid04_part1015),(kid04_part1016),(kid04_part1017),(kid04_part1018),(kid04_part1019),(kid04_part1020),(kid04_part1021),(kid04_part1022),(kid04_part1023),(kid04_part1024),(kid04_part1025)])

theorem kid04_part1001_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part1001) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part1002),(kid04_part1003),(kid04_part1004),(kid04_part1005),(kid04_part1006),(kid04_part1007),(kid04_part1008),(kid04_part1009),(kid04_part1010),(kid04_part1011),(kid04_part1012),(kid04_part1013),(kid04_part1014),(kid04_part1015),(kid04_part1016),(kid04_part1017),(kid04_part1018),(kid04_part1019),(kid04_part1020),(kid04_part1021),(kid04_part1022),(kid04_part1023),(kid04_part1024),(kid04_part1025)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1002_checked

  · exact kid04_part1008_checked

  · exact kid04_part1014_checked

  · exact kid04_part1020_checked

  · exact kid04_part1003_checked

  · exact kid04_part1009_checked

  · exact kid04_part1015_checked

  · exact kid04_part1021_checked

  · exact kid04_part1004_checked

  · exact kid04_part1010_checked

  · exact kid04_part1016_checked

  · exact kid04_part1022_checked

  · exact kid04_part1005_checked

  · exact kid04_part1011_checked

  · exact kid04_part1017_checked

  · exact kid04_part1023_checked

  · exact kid04_part1006_checked

  · exact kid04_part1012_checked

  · exact kid04_part1018_checked

  · exact kid04_part1024_checked

  · exact kid04_part1007_checked

  · exact kid04_part1013_checked

  · exact kid04_part1019_checked

  · exact kid04_part1025_checked

def kid04_part1027 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 15 (4,true),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 4, 1, 4096, 256, 2, 4096, 4, 1, 4096, 256, 4096],4096⟩,
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 0 21 true (0),
.cycle 6 16 true (1),
.last 15 (4,true),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 10 8 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (2),
.cycle 12 5 true (2)
])
theorem kid04_part1027_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1027) = true := by rfl

def kid04_part1028 : Audit := .cycle 0 14 true (0)
theorem kid04_part1028_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1028) = true := by rfl

def kid04_part1029 : Audit := .cycle 21 1 false (1)
theorem kid04_part1029_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1029) = true := by rfl

def kid04_part1030 : Audit := .split 15 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 34 1 false (2),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 8 8 true (0),
.cycle 19 1 false (1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 30 1 false (4),
.cycle 28 1 false (4),
.last 16 (4,true),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 38 1 false (2),
.last 22 (4,true),
.last 21 (4,true)
])
theorem kid04_part1030_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1030) = true := by rfl

def kid04_part1031 : Audit := .split 14 (4,true) (byMove [
.cycle 33 32 true (-1),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 21 true (0),
.last 16 (2,true),
.cycle 25 3 false (6),
.cycle 15 1 false (1),
.cycle 21 3 false (4),
.cycle 15 1 false (1),
.cycle 14 3 false (0),
.last 16 (2,true),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 0 21 true (0),
.last 16 (2,true),
.cycle 31 14 true (0),
.cycle 19 3 false (2),
.cycle 16 7 true (1),
.cycle 15 3 false (1)
])
theorem kid04_part1031_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1031) = true := by rfl

def kid04_part1032 : Audit := .cycle 13 1 false (-1)
theorem kid04_part1032_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1032) = true := by rfl

def kid04_part1033 : Audit := .cycle 1 11 true (1)
theorem kid04_part1033_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1033) = true := by rfl

def kid04_part1034 : Audit := .cycle 7 4 true (2)
theorem kid04_part1034_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1034) = true := by rfl

def kid04_part1035 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.cycle 22 1 false (6),
.last 14 (4,true),
.last 22 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 16 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1035_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1035) = true := by rfl

def kid04_part1036 : Audit := .cycle 0 12 true (0)
theorem kid04_part1036_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1036) = true := by rfl

def kid04_part1037 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 36 1 false (8),
.cycle 8 4 true (2),
.cycle 25 1 false (7),
.cycle 23 3 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 8 6 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1037_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1037) = true := by rfl

def kid04_part1038 : Audit := .cycle 21 1 false (5)
theorem kid04_part1038_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1038) = true := by rfl

def kid04_part1039 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.last 17 (2,true),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 0 17 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 6 10 true (1),
.cycle 20 1 false (0),
.cycle 19 3 false (0),
.last 22 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.cycle 14 10 false (0),
.cycle 18 1 false (-2),
.cycle 0 17 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 20 15 false (2),
.cycle 19 5 false (1)
])
theorem kid04_part1039_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1039) = true := by rfl

def kid04_part1040 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 17 3 false (-1),
.cycle 1 13 true (1),
.last 18 (4,true),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 1, 2, 3],[128, 256, 8, 4, 2048, 16777220, 524288, 1048576, 32768, 2, 8388608, 4, 128, 256, 8, 4, 2048, 16777220, 524288, 1048576, 32768, 2, 8388608, 16777220, 16777216],[2, 4, 4, 1, 16777216, 16384, 8192, 16777216, 16384, 4096, 16777216, 16777220, 2, 16777220, 4, 1, 16777216, 16384, 8192, 16777216, 16384, 4096, 16777216, 16777216, 16777216],29492256⟩,
.cycle 0 14 true (0),
.last 13 (4,true),
.last 20 (4,true),
.cycle 18 7 false (0),
.last 14 (4,true),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 17 3 false (-1),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid04_part1040_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1040) = true := by rfl

def kid04_part1041 : Audit := .cycle 1 13 true (1)
theorem kid04_part1041_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1041) = true := by rfl

def kid04_part1042 : Audit := .cycle 18 1 false (0)
theorem kid04_part1042_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1042) = true := by rfl

def kid04_part1043 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.last 26 (2,true),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 6 8 true (1),
.cycle 17 7 false (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 8 8 true (1),
.cycle 10 4 true (1),
.cycle 21 3 false (-1),
.last 22 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.cycle 18 1 false (-2),
.cycle 12 6 true (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 6 true (1),
.cycle 12 2 true (1)
])
theorem kid04_part1043_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1043) = true := by rfl

def kid04_part1044 : Audit := .cycle 13 1 false (-1)
theorem kid04_part1044_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1044) = true := by rfl

def kid04_part1045 : Audit := .cycle 1 11 true (1)
theorem kid04_part1045_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1045) = true := by rfl

def kid04_part1046 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 5 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 19 1 false (1),
.cycle 21 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 1 14 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (2),
.cycle 9 4 true (2)
])
theorem kid04_part1046_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1046) = true := by rfl

def kid04_part1047 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 18 (4,true),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 4, 4, 1, 4096, 256, 2, 4096, 4, 1, 4096, 256, 4096],4096⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 2 15 true (1),
.cycle 6 6 true (2),
.last 18 (4,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1047_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1047) = true := by rfl

def kid04_part1048 : Audit := .cycle 0 12 true (0)
theorem kid04_part1048_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1048) = true := by rfl

def kid04_part1049 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 5 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 17 5 false (1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 8 9 true (2),
.cycle 6 6 true (2),
.last 20 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 16 5 false (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part1049_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1049) = true := by rfl

def kid04_part1050 : Audit := .cycle 9 3 true (2)
theorem kid04_part1050_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1050) = true := by rfl

def kid04_part1026 : Audit := .split 10 (5,true) (byMove [(kid04_part1027),(kid04_part1028),(kid04_part1029),(kid04_part1030),(kid04_part1031),(kid04_part1032),(kid04_part1033),(kid04_part1034),(kid04_part1035),(kid04_part1036),(kid04_part1037),(kid04_part1038),(kid04_part1039),(kid04_part1040),(kid04_part1041),(kid04_part1042),(kid04_part1043),(kid04_part1044),(kid04_part1045),(kid04_part1046),(kid04_part1047),(kid04_part1048),(kid04_part1049),(kid04_part1050)])

theorem kid04_part1026_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part1026) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part1027),(kid04_part1028),(kid04_part1029),(kid04_part1030),(kid04_part1031),(kid04_part1032),(kid04_part1033),(kid04_part1034),(kid04_part1035),(kid04_part1036),(kid04_part1037),(kid04_part1038),(kid04_part1039),(kid04_part1040),(kid04_part1041),(kid04_part1042),(kid04_part1043),(kid04_part1044),(kid04_part1045),(kid04_part1046),(kid04_part1047),(kid04_part1048),(kid04_part1049),(kid04_part1050)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1027_checked

  · exact kid04_part1033_checked

  · exact kid04_part1039_checked

  · exact kid04_part1045_checked

  · exact kid04_part1028_checked

  · exact kid04_part1034_checked

  · exact kid04_part1040_checked

  · exact kid04_part1046_checked

  · exact kid04_part1029_checked

  · exact kid04_part1035_checked

  · exact kid04_part1041_checked

  · exact kid04_part1047_checked

  · exact kid04_part1030_checked

  · exact kid04_part1036_checked

  · exact kid04_part1042_checked

  · exact kid04_part1048_checked

  · exact kid04_part1031_checked

  · exact kid04_part1037_checked

  · exact kid04_part1043_checked

  · exact kid04_part1049_checked

  · exact kid04_part1032_checked

  · exact kid04_part1038_checked

  · exact kid04_part1044_checked

  · exact kid04_part1050_checked

def kid04_part1051 : Audit := .cycle 0 10 true (0)
theorem kid04_part1051_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part1051) = true := by rfl

def kid04_part1052 : Audit := .cycle 1 9 true (1)
theorem kid04_part1052_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part1052) = true := by rfl

def kid04_part1053 : Audit := .cycle 2 8 true (1)
theorem kid04_part1053_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part1053) = true := by rfl

def kid04_part1054 : Audit := .cycle 1 12 true (1)
theorem kid04_part1054_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part1054) = true := by rfl

def kid04_part1055 : Audit := .cycle 8 2 true (2)
theorem kid04_part1055_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part1055) = true := by rfl

def kid04_part1056 : Audit := .cycle 9 1 true (3)
theorem kid04_part1056_checked : zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part1056) = true := by rfl

def kid04_part936 : Audit := .split 9 (5,false) (byMove [(kid04_part937),(kid04_part938),(kid04_part939),(kid04_part940),(kid04_part941),(kid04_part942),(kid04_part943),(kid04_part944),(kid04_part945),(kid04_part946),(kid04_part947),(kid04_part948),(kid04_part949),(kid04_part950),(kid04_part975),(kid04_part1000),(kid04_part1001),(kid04_part1026),(kid04_part1051),(kid04_part1052),(kid04_part1053),(kid04_part1054),(kid04_part1055),(kid04_part1056)])

theorem kid04_part936_checked : zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (kid04_part936) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part937),(kid04_part938),(kid04_part939),(kid04_part940),(kid04_part941),(kid04_part942),(kid04_part943),(kid04_part944),(kid04_part945),(kid04_part946),(kid04_part947),(kid04_part948),(kid04_part949),(kid04_part950),(kid04_part975),(kid04_part1000),(kid04_part1001),(kid04_part1026),(kid04_part1051),(kid04_part1052),(kid04_part1053),(kid04_part1054),(kid04_part1055),(kid04_part1056)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part937_checked

  · exact kid04_part943_checked

  · exact kid04_part949_checked

  · exact kid04_part1051_checked

  · exact kid04_part938_checked

  · exact kid04_part944_checked

  · exact kid04_part950_checked

  · exact kid04_part1052_checked

  · exact kid04_part939_checked

  · exact kid04_part945_checked

  · exact kid04_part975_checked

  · exact kid04_part1053_checked

  · exact kid04_part940_checked

  · exact kid04_part946_checked

  · exact kid04_part1000_checked

  · exact kid04_part1054_checked

  · exact kid04_part941_checked

  · exact kid04_part947_checked

  · exact kid04_part1001_checked

  · exact kid04_part1055_checked

  · exact kid04_part942_checked

  · exact kid04_part948_checked

  · exact kid04_part1026_checked

  · exact kid04_part1056_checked

def kid04 : Audit := .split 8 (4,false) (byMove [(kid04_part1),(kid04_part2),(kid04_part3),(kid04_part4),(kid04_part5),(kid04_part54),(kid04_part199),(kid04_part200),(kid04_part201),(kid04_part202),(kid04_part203),(kid04_part204),(kid04_part301),(kid04_part374),(kid04_part495),(kid04_part496),(kid04_part497),(kid04_part618),(kid04_part931),(kid04_part932),(kid04_part933),(kid04_part934),(kid04_part935),(kid04_part936)])

theorem check04 : zipCheck 1271 (child ⟨false,false,4⟩) (kid04) = true := by

  change (zipQueryOK 1271 (child ⟨false,false,4⟩) 8 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (child ⟨false,false,4⟩) (4,false) (some mv)) (byMove [(kid04_part1),(kid04_part2),(kid04_part3),(kid04_part4),(kid04_part5),(kid04_part54),(kid04_part199),(kid04_part200),(kid04_part201),(kid04_part202),(kid04_part203),(kid04_part204),(kid04_part301),(kid04_part374),(kid04_part495),(kid04_part496),(kid04_part497),(kid04_part618),(kid04_part931),(kid04_part932),(kid04_part933),(kid04_part934),(kid04_part935),(kid04_part936)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1_checked

  · exact kid04_part199_checked

  · exact kid04_part301_checked

  · exact kid04_part931_checked

  · exact kid04_part2_checked

  · exact kid04_part200_checked

  · exact kid04_part374_checked

  · exact kid04_part932_checked

  · exact kid04_part3_checked

  · exact kid04_part201_checked

  · exact kid04_part495_checked

  · exact kid04_part933_checked

  · exact kid04_part4_checked

  · exact kid04_part202_checked

  · exact kid04_part496_checked

  · exact kid04_part934_checked

  · exact kid04_part5_checked

  · exact kid04_part203_checked

  · exact kid04_part497_checked

  · exact kid04_part935_checked

  · exact kid04_part54_checked

  · exact kid04_part204_checked

  · exact kid04_part618_checked

  · exact kid04_part936_checked

end BB6.Agent11Raw39B0RB
