import Raw39RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid04_part1 : Audit := .cycle 0 9 true (0)
theorem kid04_part1_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,0⟩)) (kid04_part1) = true := by rfl

def kid04_part2 : Audit := .cycle 1 8 true (1)
theorem kid04_part2_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,1⟩)) (kid04_part2) = true := by rfl

def kid04_part3 : Audit := .cycle 17 1 false (1)
theorem kid04_part3_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,2⟩)) (kid04_part3) = true := by rfl

def kid04_part4 : Audit := .cycle 13 1 false (3)
theorem kid04_part4_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,3⟩)) (kid04_part4) = true := by rfl

def kid04_part6 : Audit := .cycle 0 11 false (3)
theorem kid04_part6_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part6) = true := by rfl

def kid04_part7 : Audit := .cycle 18 1 false (0)
theorem kid04_part7_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part7) = true := by rfl

def kid04_part8 : Audit := .cycle 12 1 false (0)
theorem kid04_part8_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part8) = true := by rfl

def kid04_part9 : Audit := .cycle 11 1 false (-1)
theorem kid04_part9_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part9) = true := by rfl

def kid04_part10 : Audit := .cycle 11 1 false (-1)
theorem kid04_part10_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part10) = true := by rfl

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
.split 13 (1,true) (byMove [
.cycle 16 1 false (0),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 0 15 false (3),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 28 1 false (-2),
.cycle 8 14 false (2),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 8 6 false (2),
.cycle 11 3 true (-2),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (1),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 25 (5,true),
.last 24 (5,true),
.cycle 2 12 false (3),
.cycle 25 1 false (-1),
.last 16 (5,true),
.cycle 9 8 false (1)
]),
.cycle 10 4 false (0),
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
.last 25 (1,true),
.cycle 10 16 false (3),
.cycle 0 26 true (-2),
.cycle 24 1 false (-2),
.cycle 24 1 false (-2),
.cycle 33 1 false (-1),
.cycle 12 12 true (-1),
.cycle 1 23 false (3),
.cycle 30 1 false (0),
.cycle 28 1 false (2),
.cycle 9 15 false (3),
.cycle 11 13 true (-1)
]),
.cycle 1 11 false (3),
.cycle 18 1 false (0),
.cycle 16 1 false (2),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
])
theorem kid04_part11_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part11) = true := by rfl

def kid04_part12 : Audit := .cycle 0 11 true (0)
theorem kid04_part12_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part12) = true := by rfl

def kid04_part13 : Audit := .cycle 18 1 false (2)
theorem kid04_part13_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part13) = true := by rfl

def kid04_part14 : Audit := .cycle 12 1 false (2)
theorem kid04_part14_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part14) = true := by rfl

def kid04_part15 : Audit := .cycle 11 1 false (1)
theorem kid04_part15_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part15) = true := by rfl

def kid04_part16 : Audit := .cycle 11 1 false (1)
theorem kid04_part16_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part16) = true := by rfl

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
.split 13 (1,true) (byMove [
.cycle 16 1 false (2),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
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
.cycle 10 7 false (1),
.cycle 15 1 false (-1),
.cycle 17 1 false (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 25 1 false (1),
.cycle 9 5 true (0),
.cycle 9 8 true (0)
]),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid04_part17_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part17) = true := by rfl

def kid04_part18 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
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
.cycle 11 3 false (0),
.cycle 10 6 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 27 1 false (-1),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 9 5 false (1),
.last 14 (5,false)
]),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 5 false (2),
.split 13 (5,false) (byMove [
.cycle 27 1 false (-1),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 9 5 false (1),
.last 15 (5,true),
.cycle 0 14 true (-1),
.cycle 8 15 false (4),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 8 7 false (2),
.cycle 13 1 true (1),
.cycle 11 3 true (-1),
.cycle 19 1 false (-1),
.cycle 0 16 true (-1),
.cycle 18 1 false (0),
.cycle 9 5 false (1),
.last 15 (5,true),
.cycle 6 19 false (5),
.cycle 1 13 true (-1),
.cycle 8 13 false (3),
.cycle 26 1 false (0),
.cycle 9 5 true (-1),
.cycle 13 1 true (1)
]),
.cycle 15 1 false (-1),
.cycle 10 6 false (0),
.cycle 14 1 false (-2),
.cycle 16 1 false (2),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 20 1 false (-2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 16 1 false (2),
.last 15 (5,false),
.cycle 15 1 false (-1),
.cycle 0 15 true (-1),
.cycle 10 4 true (-1),
.last 15 (5,false),
.cycle 11 3 false (0),
.cycle 10 6 false (0),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 22 1 false (0),
.cycle 12 2 true (-1),
.cycle 10 5 false (0),
.cycle 0 15 true (-1),
.cycle 17 1 false (-1),
.last 15 (5,false)
]),
.cycle 9 17 false (4),
.cycle 25 1 false (-1),
.cycle 2 11 false (3),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 22 1 false (0),
.cycle 12 2 true (0),
.cycle 10 5 false (1),
.cycle 0 15 true (-1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 27 1 false (-1),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 19 1 false (-1),
.cycle 13 1 true (1),
.cycle 9 7 false (1),
.last 15 (5,true),
.cycle 10 5 false (1),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 31 1 false (-1),
.cycle 9 17 false (4),
.cycle 25 1 false (-1),
.cycle 69 1 false (-3),
.cycle 9 9 false (2),
.cycle 13 1 true (1)
])
])
theorem kid04_part18_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part18) = true := by rfl

def kid04_part19 : Audit := .cycle 10 3 false (0)
theorem kid04_part19_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part19) = true := by rfl

def kid04_part20 : Audit := .cycle 0 13 true (-1)
theorem kid04_part20_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part20) = true := by rfl

def kid04_part21 : Audit := .cycle 11 1 false (-1)
theorem kid04_part21_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part21) = true := by rfl

def kid04_part22 : Audit := .cycle 11 1 false (-1)
theorem kid04_part22_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part22) = true := by rfl

def kid04_part24 : Audit := .split 16 (5,true) (byMove [
.cycle 12 5 false (0),
.last 37 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.cycle 0 42 false (3),
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 18 1 false (-2),
.cycle 0 18 true (-2),
.cycle 10 7 false (0),
.cycle 0 19 false (3),
.last 18 (1,true),
.cycle 10 9 false (0),
.cycle 21 1 false (1),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.cycle 11 6 false (0),
.cycle 25 1 false (-1),
.last 17 (1,true),
.cycle 10 8 false (0),
.cycle 0 33 true (-2),
.cycle 15 2 true (-2),
.cycle 27 1 false (-1)
])
theorem kid04_part24_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part24) = true := by rfl

def kid04_part25 : Audit := .cycle 0 15 true (-2)
theorem kid04_part25_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part25) = true := by rfl

def kid04_part26 : Audit := .cycle 13 1 false (-1)
theorem kid04_part26_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part26) = true := by rfl

def kid04_part27 : Audit := .cycle 12 1 false (-2)
theorem kid04_part27_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part27) = true := by rfl

def kid04_part28 : Audit := .cycle 12 1 false (-2)
theorem kid04_part28_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part28) = true := by rfl

def kid04_part29 : Audit := .cycle 11 1 false (-1)
theorem kid04_part29_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part29) = true := by rfl

def kid04_part30 : Audit := .cycle 14 1 false (2)
theorem kid04_part30_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part30) = true := by rfl

def kid04_part31 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (1),
.cycle 0 13 true (-1),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.cycle 10 5 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.last 24 (5,true),
.cycle 1 12 true (-1),
.cycle 19 1 false (1),
.cycle 17 1 false (3),
.cycle 9 4 true (-1),
.cycle 8 14 true (-1)
])
theorem kid04_part31_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part31) = true := by rfl

def kid04_part32 : Audit := .cycle 13 1 false (-1)
theorem kid04_part32_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part32) = true := by rfl

def kid04_part33 : Audit := .cycle 0 13 true (-1)
theorem kid04_part33_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part33) = true := by rfl

def kid04_part34 : Audit := .cycle 10 2 true (-1)
theorem kid04_part34_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part34) = true := by rfl

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
.last 14 (1,true),
.cycle 10 5 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 33 1 false (1),
.cycle 1 12 true (-1),
.cycle 19 1 false (1),
.cycle 17 1 false (3),
.cycle 9 4 true (-1),
.cycle 13 1 true (1)
])
theorem kid04_part35_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part35) = true := by rfl

def kid04_part36 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-2),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 0 18 true (-2),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 23 1 false (-1),
.cycle 8 16 false (3),
.cycle 9 6 false (1),
.cycle 0 15 true (-2),
.cycle 18 1 false (-2),
.last 14 (5,true),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 3 14 false (3),
.last 25 (5,true),
.last 16 (5,true),
.last 39 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part36_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part36) = true := by rfl

def kid04_part37 : Audit := .cycle 10 4 false (0)
theorem kid04_part37_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part37) = true := by rfl

def kid04_part38 : Audit := .cycle 16 1 false (2)
theorem kid04_part38_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part38) = true := by rfl

def kid04_part39 : Audit := .cycle 12 1 false (-2)
theorem kid04_part39_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part39) = true := by rfl

def kid04_part40 : Audit := .cycle 12 1 false (-2)
theorem kid04_part40_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part40) = true := by rfl

def kid04_part41 : Audit := .cycle 11 1 false (-1)
theorem kid04_part41_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part41) = true := by rfl

def kid04_part42 : Audit := .cycle 20 1 false (0)
theorem kid04_part42_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part42) = true := by rfl

def kid04_part43 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 5 false (2),
.cycle 1 13 true (-1),
.cycle 15 1 false (-1),
.cycle 10 6 false (0),
.cycle 14 1 false (-2),
.cycle 16 1 false (2),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 24 (5,true),
.last 23 (5,true),
.cycle 2 11 false (3),
.cycle 24 1 false (0),
.last 15 (5,true),
.last 24 (5,true)
])
theorem kid04_part43_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part43) = true := by rfl

def kid04_part44 : Audit := .cycle 10 3 false (0)
theorem kid04_part44_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part44) = true := by rfl

def kid04_part45 : Audit := .cycle 0 13 true (-1)
theorem kid04_part45_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part45) = true := by rfl

def kid04_part46 : Audit := .split 13 (5,true) (byMove [
.cycle 12 5 false (0),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 9 6 false (1),
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 15 true (-1),
.cycle 10 4 true (-1),
.cycle 9 7 true (-1),
.last 15 (1,true),
.cycle 10 6 false (0),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (0),
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 10 5 false (0),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.cycle 12 5 true (-1)
])
theorem kid04_part46_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part46) = true := by rfl

def kid04_part47 : Audit := .split 12 (5,true) (byMove [
.cycle 15 1 false (1),
.last 13 (1,true),
.cycle 14 1 false (-2),
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
.last 13 (1,true),
.cycle 14 1 false (-2),
.cycle 16 1 false (2),
.cycle 10 3 false (0),
.cycle 11 3 false (0),
.cycle 0 42 true (-2),
.last 24 (1,true),
.cycle 2 11 false (3),
.cycle 24 1 false (0),
.cycle 14 2 true (-1),
.cycle 13 1 true (1)
])
theorem kid04_part47_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part47) = true := by rfl

def kid04_part23 : Audit := .split 11 (5,false) (byMove [(kid04_part24),(kid04_part25),(kid04_part26),(kid04_part27),(kid04_part28),(kid04_part29),(kid04_part30),(kid04_part31),(kid04_part32),(kid04_part33),(kid04_part34),(kid04_part35),(kid04_part36),(kid04_part37),(kid04_part38),(kid04_part39),(kid04_part40),(kid04_part41),(kid04_part42),(kid04_part43),(kid04_part44),(kid04_part45),(kid04_part46),(kid04_part47)])

theorem kid04_part23_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part23) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part24),(kid04_part25),(kid04_part26),(kid04_part27),(kid04_part28),(kid04_part29),(kid04_part30),(kid04_part31),(kid04_part32),(kid04_part33),(kid04_part34),(kid04_part35),(kid04_part36),(kid04_part37),(kid04_part38),(kid04_part39),(kid04_part40),(kid04_part41),(kid04_part42),(kid04_part43),(kid04_part44),(kid04_part45),(kid04_part46),(kid04_part47)] mv))) = true

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
theorem kid04_part48_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part48) = true := by rfl

def kid04_part49 : Audit := .cycle 1 10 true (0)
theorem kid04_part49_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part49) = true := by rfl

def kid04_part50 : Audit := .cycle 17 1 false (1)
theorem kid04_part50_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part50) = true := by rfl

def kid04_part51 : Audit := .cycle 15 1 false (3)
theorem kid04_part51_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part51) = true := by rfl

def kid04_part52 : Audit := .cycle 9 2 true (0)
theorem kid04_part52_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part52) = true := by rfl

def kid04_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 14 1 false (2),
.split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 10 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (3),
.cycle 9 4 true (0),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (-1),
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
.last 14 (1,true),
.cycle 10 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (3),
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
.split 12 (1,true) (byMove [
.cycle 0 22 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 6 false (1),
.cycle 15 1 false (3),
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.last 13 (5,true),
.cycle 17 1 false (-1),
.cycle 10 5 false (1),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 6 false (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.last 13 (5,true)
]),
.cycle 13 1 false (-1),
.cycle 15 1 false (3),
.split 13 (5,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 10 4 true (0),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 8 14 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 6 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (3),
.cycle 12 2 true (0),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 25 1 false (1),
.cycle 9 5 true (0),
.cycle 11 3 true (0)
]),
.split 12 (5,true) (byMove [
.cycle 0 22 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (3),
.last 13 (1,true),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.cycle 14 1 false (2),
.last 14 (1,true),
.cycle 10 5 false (1),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (1),
.last 13 (1,true),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 10 3 true (0),
.cycle 11 3 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 23 1 false (1),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid04_part53_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part53) = true := by rfl

def kid04_part5 : Audit := .split 10 (4,true) (byMove [(kid04_part6),(kid04_part7),(kid04_part8),(kid04_part9),(kid04_part10),(kid04_part11),(kid04_part12),(kid04_part13),(kid04_part14),(kid04_part15),(kid04_part16),(kid04_part17),(kid04_part18),(kid04_part19),(kid04_part20),(kid04_part21),(kid04_part22),(kid04_part23),(kid04_part48),(kid04_part49),(kid04_part50),(kid04_part51),(kid04_part52),(kid04_part53)])

theorem kid04_part5_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (kid04_part5) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part6),(kid04_part7),(kid04_part8),(kid04_part9),(kid04_part10),(kid04_part11),(kid04_part12),(kid04_part13),(kid04_part14),(kid04_part15),(kid04_part16),(kid04_part17),(kid04_part18),(kid04_part19),(kid04_part20),(kid04_part21),(kid04_part22),(kid04_part23),(kid04_part48),(kid04_part49),(kid04_part50),(kid04_part51),(kid04_part52),(kid04_part53)] mv))) = true

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

def kid04_part55 : Audit := .cycle 12 1 false (2)
theorem kid04_part55_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part55) = true := by rfl

def kid04_part56 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 false (3),
.cycle 11 9 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 9 false (-1),
.cycle 11 9 false (0),
.cycle 0 11 true (0),
.cycle 11 9 false (3),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 9 false (1),
.cycle 11 9 false (2),
.cycle 13 9 false (0),
.split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 14 9 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 9 false (-2),
.cycle 14 9 false (-1),
.cycle 0 14 true (-1),
.cycle 14 9 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 9 false (0),
.cycle 14 9 false (1),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 9 false (-2),
.last 45 (5,true),
.cycle 24 7 false (0),
.cycle 1 13 false (3),
.cycle 14 9 false (1),
.cycle 18 1 false (2),
.last 15 (5,true),
.cycle 9 5 false (1)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 9 false (-1),
.cycle 0 15 true (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 11 9 false (2),
.cycle 15 1 false (3),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 9 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 9 false (-1),
.cycle 13 9 false (0),
.cycle 0 13 true (0),
.cycle 13 9 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 9 false (1),
.cycle 13 9 false (2),
.cycle 17 9 false (0),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 9 false (-1),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 9 false (2),
.cycle 17 1 false (3),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid04_part56_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part56) = true := by rfl

def kid04_part57 : Audit := .cycle 14 1 false (-2)
theorem kid04_part57_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part57) = true := by rfl

def kid04_part58 : Audit := .cycle 0 11 true (0)
theorem kid04_part58_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part58) = true := by rfl

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
.split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 21 2 false (-1),
.cycle 14 2 false (-2),
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
.cycle 10 6 false (0),
.cycle 14 2 false (-2),
.cycle 16 1 false (2),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 27 (5,true),
.cycle 25 2 false (-1),
.cycle 2 11 false (3),
.cycle 24 2 false (0),
.last 14 (5,true),
.cycle 17 2 false (-1)
]),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 17 2 false (1),
.cycle 15 1 false (3),
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
.last 14 (1,true),
.cycle 10 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 2 false (1),
.cycle 17 1 false (3),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid04_part59_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part59) = true := by rfl

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
.split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
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
.last 16 (4,true),
.cycle 15 1 false (-3),
.cycle 16 1 false (2),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 10 17 false (4),
.cycle 26 1 false (-2),
.cycle 2 11 false (3),
.cycle 25 1 false (-1),
.cycle 18 1 false (-2),
.cycle 18 1 false (-2)
]),
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
.last 15 (1,true),
.cycle 11 3 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 25 (1,true),
.cycle 1 13 false (3),
.cycle 21 1 false (-1),
.cycle 18 1 false (2),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (3),
.cycle 10 2 true (0),
.cycle 9 2 true (0)
])
theorem kid04_part60_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part60) = true := by rfl

def kid04_part61 : Audit := .cycle 0 10 true (0)
theorem kid04_part61_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part61) = true := by rfl

def kid04_part62 : Audit := .cycle 1 9 true (1)
theorem kid04_part62_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part62) = true := by rfl

def kid04_part63 : Audit := .cycle 20 1 false (2)
theorem kid04_part63_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part63) = true := by rfl

def kid04_part64 : Audit := .cycle 17 1 false (1)
theorem kid04_part64_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part64) = true := by rfl

def kid04_part65 : Audit := .cycle 8 2 true (1)
theorem kid04_part65_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part65) = true := by rfl

def kid04_part66 : Audit := .cycle 9 1 true (1)
theorem kid04_part66_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part66) = true := by rfl

def kid04_part68 : Audit := .cycle 18 1 false (0)
theorem kid04_part68_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part68) = true := by rfl

def kid04_part69 : Audit := .cycle 10 12 false (1)
theorem kid04_part69_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part69) = true := by rfl

def kid04_part70 : Audit := .cycle 11 5 false (1)
theorem kid04_part70_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part70) = true := by rfl

def kid04_part71 : Audit := .cycle 0 17 false (3)
theorem kid04_part71_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part71) = true := by rfl

def kid04_part72 : Audit := .split 16 (4,true) (byMove [
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
.cycle 16 3 false (-2),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.last 30 (5,true),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 9 8 false (1)
])
theorem kid04_part72_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part72) = true := by rfl

def kid04_part73 : Audit := .split 16 (5,true) (byMove [
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
.last 19 (4,true),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 16 14 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 21 1 false (1),
.cycle 16 2 true (-2),
.cycle 9 8 false (1)
])
theorem kid04_part73_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part73) = true := by rfl

def kid04_part74 : Audit := .cycle 6 20 false (3)
theorem kid04_part74_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part74) = true := by rfl

def kid04_part75 : Audit := .cycle 10 11 true (-2)
theorem kid04_part75_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part75) = true := by rfl

def kid04_part76 : Audit := .cycle 10 11 false (1)
theorem kid04_part76_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part76) = true := by rfl

def kid04_part77 : Audit := .cycle 10 9 false (1)
theorem kid04_part77_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part77) = true := by rfl

def kid04_part78 : Audit := .cycle 8 8 false (2)
theorem kid04_part78_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part78) = true := by rfl

def kid04_part79 : Audit := .cycle 13 3 true (-2)
theorem kid04_part79_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part79) = true := by rfl

def kid04_part80 : Audit := .cycle 10 6 false (1)
theorem kid04_part80_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part80) = true := by rfl

def kid04_part81 : Audit := .split 19 (4,true) (byMove [
.cycle 34 16 false (1),
.cycle 10 15 false (1),
.cycle 21 1 false (-3),
.cycle 20 1 false (-4),
.cycle 12 8 false (0),
.cycle 13 7 false (-1),
.cycle 14 6 true (-3),
.cycle 10 18 true (-3),
.cycle 0 22 true (-3),
.cycle 20 1 false (-2),
.cycle 12 8 false (0),
.cycle 13 7 false (-1),
.cycle 14 6 false (-1),
.cycle 17 3 false (-2),
.cycle 14 8 true (-4),
.cycle 20 1 false (-4),
.cycle 12 8 false (0),
.cycle 13 7 false (-1),
.cycle 15 7 false (-1),
.last 35 (5,true),
.cycle 25 51 false (3),
.cycle 10 12 false (1),
.last 21 (5,true),
.cycle 9 11 false (1)
])
theorem kid04_part81_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part81) = true := by rfl

def kid04_part82 : Audit := .cycle 11 5 false (1)
theorem kid04_part82_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part82) = true := by rfl

def kid04_part83 : Audit := .cycle 19 1 false (1)
theorem kid04_part83_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part83) = true := by rfl

def kid04_part84 : Audit := .split 16 (4,true) (byMove [
.cycle 23 1 false (-1),
.last 77 (5,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 19 1 false (1),
.cycle 12 6 false (0),
.cycle 11 6 false (1),
.cycle 0 18 true (-2),
.cycle 12 6 true (-2),
.last 17 (5,true),
.cycle 14 3 false (-1),
.cycle 16 3 false (-2),
.cycle 21 1 false (1),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 10 13 false (1),
.cycle 15 2 true (-2),
.cycle 10 13 false (1),
.cycle 6 22 false (3),
.last 19 (5,true),
.last 17 (5,true)
])
theorem kid04_part84_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part84) = true := by rfl

def kid04_part85 : Audit := .split 16 (5,true) (byMove [
.last 20 (4,true),
.proven (BB6.Agent11Raw39RCCounter107.M1.table) (fun m hm => BB6.Agent11Raw39RCCounter107.M1.never m hm),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 19 1 false (1),
.cycle 13 5 false (-1),
.cycle 11 6 false (1),
.cycle 0 18 true (-2),
.last 17 (4,true),
.cycle 13 5 true (-2),
.cycle 14 3 false (-1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 10 13 false (1),
.cycle 15 2 true (-2),
.last 18 (4,true),
.cycle 6 22 false (3),
.last 17 (4,true),
.cycle 9 14 false (1)
])
theorem kid04_part85_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part85) = true := by rfl

def kid04_part86 : Audit := .split 29 (5,true) (byMove [
.cycle 32 1 false (0),
.cycle 10 40 false (3),
.cycle 11 19 false (3),
.cycle 0 31 false (3),
.last 30 (4,true),
.cycle 13 18 false (3),
.cycle 6 34 false (3),
.cycle 10 25 true (-2),
.last 44 (4,true),
.cycle 10 23 false (3),
.cycle 8 22 false (3),
.cycle 13 17 true (-2),
.cycle 10 20 false (3),
.last 46 (4,true),
.last 38 (4,true),
.cycle 33 1 false (1),
.last 30 (4,true),
.cycle 26 8 false (1),
.cycle 16 14 true (-1),
.cycle 1 42 false (3),
.cycle 2 28 false (3),
.last 48 (4,true),
.cycle 28 2 true (-1),
.cycle 9 26 false (3)
])
theorem kid04_part86_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part86) = true := by rfl

def kid04_part87 : Audit := .split 28 (5,true) (byMove [
.cycle 0 29 false (3),
.cycle 10 24 false (2),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 12 17 false (2),
.cycle 13 16 false (2),
.cycle 0 29 false (3),
.cycle 10 24 true (-2),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 12 17 false (2),
.cycle 13 16 true (-2),
.cycle 14 15 false (2),
.last 31 (4,true),
.cycle 0 31 false (3),
.cycle 29 1 false (-3),
.last 35 (4,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 256, 128, 128, 256, 32768, 1048580, 256, 32768, 33554432, 67108864, 2097152, 32768, 32768, 128, 33554432, 67108864, 134217728, 262144, 256, 33554432, 33554432, 67108864, 134217728, 1325694976, 1325695232, 1325694976, 1073741824],[4, 128, 32768, 1, 1073741824, 128, 16384, 128, 1073741824, 4096, 1073741824, 128, 1048576, 33554432, 32768, 262144, 1073741824, 262144, 67108864, 33554432, 32768, 16777216, 1073741824, 128, 67108864, 33554432, 1325694976, 16777216, 1073741824, 1325695104, 1073741824],2143056384⟩,
.cycle 16 14 true (-2),
.cycle 1 28 false (3),
.cycle 10 23 false (2),
.cycle 33 1 false (1),
.cycle 27 2 true (-2),
.cycle 9 20 false (2)
])
theorem kid04_part87_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part87) = true := by rfl

def kid04_part88 : Audit := .cycle 2 14 false (3)
theorem kid04_part88_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part88) = true := by rfl

def kid04_part89 : Audit := .cycle 24 32 true (-4)
theorem kid04_part89_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part89) = true := by rfl

def kid04_part90 : Audit := .split 17 (5,true) (byMove [
.cycle 20 1 false (0),
.cycle 10 16 false (1),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 13 6 false (0),
.cycle 6 22 false (3),
.cycle 10 13 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 8 10 false (2),
.cycle 13 5 true (-2),
.cycle 10 8 false (1),
.last 19 (4,true),
.cycle 11 7 false (1),
.cycle 21 1 false (1),
.last 18 (4,true),
.last 22 (4,true),
.cycle 16 14 true (-1),
.cycle 1 30 false (3),
.cycle 2 16 false (3),
.cycle 26 36 true (-4),
.cycle 16 2 true (-1),
.cycle 9 14 false (1)
])
theorem kid04_part90_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part90) = true := by rfl

def kid04_part91 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 false (3),
.cycle 10 16 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 12 9 false (0),
.cycle 13 8 false (0),
.cycle 0 21 false (3),
.cycle 10 16 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 12 9 false (0),
.cycle 13 8 true (-2),
.cycle 14 7 false (0),
.last 23 (4,true),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 12 9 false (0),
.cycle 20 6 false (-2),
.cycle 16 14 true (-2),
.cycle 1 20 false (3),
.cycle 10 15 false (1),
.cycle 25 1 false (1),
.cycle 19 2 true (-2),
.cycle 9 12 false (1)
])
theorem kid04_part91_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part91) = true := by rfl

def kid04_part67 : Audit := .split 15 (1,true) (byMove [(kid04_part68),(kid04_part69),(kid04_part70),(kid04_part71),(kid04_part72),(kid04_part73),(kid04_part74),(kid04_part75),(kid04_part76),(kid04_part77),(kid04_part78),(kid04_part79),(kid04_part80),(kid04_part81),(kid04_part82),(kid04_part83),(kid04_part84),(kid04_part85),(kid04_part86),(kid04_part87),(kid04_part88),(kid04_part89),(kid04_part90),(kid04_part91)])

theorem kid04_part67_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part67) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part68),(kid04_part69),(kid04_part70),(kid04_part71),(kid04_part72),(kid04_part73),(kid04_part74),(kid04_part75),(kid04_part76),(kid04_part77),(kid04_part78),(kid04_part79),(kid04_part80),(kid04_part81),(kid04_part82),(kid04_part83),(kid04_part84),(kid04_part85),(kid04_part86),(kid04_part87),(kid04_part88),(kid04_part89),(kid04_part90),(kid04_part91)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part68_checked

  · exact kid04_part74_checked

  · exact kid04_part80_checked

  · exact kid04_part86_checked

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

def kid04_part93 : Audit := .split 14 (4,true) (byMove [
.cycle 17 1 false (1),
.cycle 0 16 false (3),
.cycle 22 1 false (-4),
.cycle 0 16 true (-1),
.cycle 15 5 false (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 12 12 true (0),
.cycle 28 1 false (0),
.cycle 25 1 false (-1),
.cycle 8 7 false (2),
.cycle 12 4 true (0),
.cycle 26 1 false (-2),
.cycle 10 5 false (1),
.last 44 (5,true),
.cycle 18 1 false (2),
.cycle 15 5 false (-1),
.last 15 (5,true),
.cycle 0 29 true (-1),
.cycle 0 28 true (-1),
.cycle 2 13 false (3),
.cycle 35 1 false (1),
.last 16 (5,true),
.cycle 0 20 true (-1)
])
theorem kid04_part93_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part93) = true := by rfl

def kid04_part94 : Audit := .cycle 0 14 true (-1)
theorem kid04_part94_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part94) = true := by rfl

def kid04_part95 : Audit := .cycle 12 1 false (0)
theorem kid04_part95_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part95) = true := by rfl

def kid04_part96 : Audit := .cycle 11 1 false (-1)
theorem kid04_part96_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part96) = true := by rfl

def kid04_part97 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.cycle 11 12 false (-1),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 15 22 true (-3),
.cycle 11 12 true (-3),
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
.cycle 11 11 false (-1),
.cycle 20 1 false (0),
.last 17 (5,true),
.cycle 9 7 false (1)
])
theorem kid04_part97_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part97) = true := by rfl

def kid04_part98 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 11 12 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 84825604096, 1048576, 128, 524288, 1048576, 32768, 4, 68719476736, 128, 128, 256, 8, 134217728, 1048576, 128, 2147483648, 4294967296, 134217728, 4, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 134217728, 68719476736, 84825604096, 2147483648, 4294967296, 8589934592, 84825604096, 84825604096, 84825604096, 68719476736],[4, 1048576, 134217728, 1, 1, 68719476736, 16384, 68719476736, 128, 4096, 4096, 68719476736, 4, 1048576, 68719476736, 1, 1, 68719476736, 67108864, 68719476736, 128, 16777216, 16777216, 68719476736, 4294967296, 68719476736, 68719476736, 1073741824, 1073741824, 68719476736, 4294967296, 84825604096, 84825604096, 1073741824, 1073741824, 68719476736, 68719476736],137303443020⟩,
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (-1),
.cycle 11 4 true (-2),
.last 17 (5,true),
.cycle 12 3 false (-1),
.last 54 (5,true),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 30 (5,true),
.cycle 0 18 true (-2),
.cycle 11 11 false (0),
.cycle 0 20 true (-2),
.last 16 (5,true),
.cycle 9 6 false (1)
])
theorem kid04_part98_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part98) = true := by rfl

def kid04_part99 : Audit := .cycle 13 1 false (3)
theorem kid04_part99_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part99) = true := by rfl

def kid04_part100 : Audit := .split 23 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 12 false (4),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 19 5 false (3),
.cycle 20 4 false (2),
.cycle 0 24 true (0),
.cycle 12 12 true (1),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 19 5 false (3),
.cycle 20 4 true (1),
.cycle 17 21 false (4),
.cycle 21 3 false (2),
.cycle 0 26 true (0),
.cycle 24 1 false (0),
.cycle 19 5 false (3),
.cycle 20 4 false (2),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 13 11 false (4),
.cycle 28 1 false (4),
.last 25 (5,true),
.cycle 9 15 true (0)
])
theorem kid04_part100_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part100) = true := by rfl

def kid04_part101 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 12 5 false (0),
.cycle 13 4 true (-2),
.cycle 11 14 false (1),
.cycle 14 3 false (-1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.last 30 (5,true),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 9 8 false (1)
])
theorem kid04_part101_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part101) = true := by rfl

def kid04_part102 : Audit := .cycle 0 12 true (0)
theorem kid04_part102_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part102) = true := by rfl

def kid04_part103 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 11 12 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 0 12 true (0),
.cycle 11 12 true (1),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 5 false (2),
.cycle 11 4 true (1),
.cycle 8 6 true (0),
.cycle 11 3 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 11 11 false (3),
.cycle 16 1 false (4),
.last 13 (5,true),
.cycle 9 3 true (0)
])
theorem kid04_part103_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part103) = true := by rfl

def kid04_part104 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.last 23 (4,true),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.last 23 (4,true),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 16 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.last 22 (4,true),
.cycle 16 1 false (4),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part104_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part104) = true := by rfl

def kid04_part105 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 false (3),
.cycle 13 12 false (0),
.cycle 21 1 false (-3),
.cycle 20 1 false (-4),
.cycle 15 5 false (-1),
.cycle 16 4 false (-2),
.last 73 (5,true),
.cycle 13 12 true (-3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 15 5 false (-1),
.cycle 16 4 true (-3),
.cycle 11 9 false (0),
.cycle 17 3 false (-2),
.cycle 40 21 false (3),
.cycle 20 1 false (-4),
.cycle 15 5 false (-1),
.cycle 16 4 false (-2),
.last 45 (5,true),
.cycle 1 19 false (3),
.cycle 13 11 false (0),
.cycle 24 1 false (0),
.last 21 (5,true),
.cycle 9 11 false (1)
])
theorem kid04_part105_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part105) = true := by rfl

def kid04_part106 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.cycle 11 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 5 false (0),
.cycle 11 4 false (0),
.cycle 10 6 true (-1),
.cycle 14 12 true (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 11 5 false (0),
.cycle 11 4 true (-1),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 10 8 true (-2),
.cycle 14 1 false (-2),
.cycle 11 5 false (0),
.cycle 11 4 false (0),
.cycle 10 7 false (1),
.far true 1 ⟨0,[0, 0],[10, 10, 10, 8, 32, 2, 64],[42, 2, 16, 10, 10, 64, 64],64⟩,
.cycle 0 16 true (-1),
.cycle 27 1 false (1),
.last 15 (5,true),
.cycle 9 5 false (1)
])
theorem kid04_part106_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part106) = true := by rfl

def kid04_part107 : Audit := .cycle 15 1 false (3)
theorem kid04_part107_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part107) = true := by rfl

def kid04_part108 : Audit := .cycle 11 1 false (-1)
theorem kid04_part108_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part108) = true := by rfl

def kid04_part109 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.cycle 11 12 false (-1),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 61 (5,true),
.cycle 24 12 true (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 5 false (-1),
.cycle 12 4 true (-3),
.cycle 15 3 false (-3),
.cycle 13 3 false (-2),
.cycle 3 42 false (3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 38 (5,true),
.cycle 3 21 false (3),
.cycle 11 11 false (-1),
.cycle 23 1 false (3),
.last 17 (5,true),
.cycle 9 7 false (1)
])
theorem kid04_part109_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part109) = true := by rfl

def kid04_part110 : Audit := .split 14 (4,true) (byMove [
.cycle 3 21 false (3),
.cycle 11 12 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 17 (5,true),
.cycle 18 12 true (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 11 5 false (-1),
.cycle 11 4 true (-2),
.last 17 (5,true),
.cycle 12 3 false (-1),
.last 19 (5,true),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 17 (5,true),
.last 31 (5,true),
.cycle 22 11 false (0),
.cycle 28 1 false (0),
.last 16 (5,true),
.cycle 9 6 false (1)
])
theorem kid04_part110_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part110) = true := by rfl

def kid04_part111 : Audit := .split 23 (4,true) (byMove [
.cycle 0 24 false (3),
.cycle 14 12 false (2),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.cycle 19 5 false (1),
.cycle 20 4 false (0),
.cycle 0 28 true (-1),
.cycle 14 12 true (-1),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 19 5 false (1),
.cycle 20 4 true (-1),
.cycle 0 30 true (-2),
.cycle 21 3 false (0),
.cycle 0 30 true (-2),
.cycle 24 1 false (-2),
.cycle 19 5 false (1),
.cycle 20 4 false (0),
.cycle 0 28 true (-1),
.cycle 1 23 false (3),
.cycle 14 11 false (2),
.cycle 28 1 false (2),
.last 25 (5,true),
.cycle 9 15 false (3)
])
theorem kid04_part111_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part111) = true := by rfl

def kid04_part112 : Audit := .cycle 1 11 true (0)
theorem kid04_part112_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part112) = true := by rfl

def kid04_part113 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 11 12 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 0 13 true (0),
.cycle 11 12 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 11 5 false (1),
.cycle 11 4 true (0),
.cycle 2 13 false (3),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 11 11 false (2),
.cycle 17 1 false (3),
.last 14 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part113_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part113) = true := by rfl

def kid04_part114 : Audit := .cycle 0 12 true (0)
theorem kid04_part114_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part114) = true := by rfl

def kid04_part115 : Audit := .split 11 (4,true) (byMove [
.cycle 14 1 false (2),
.last 14 (5,true),
.cycle 19 1 false (-3),
.cycle 0 13 true (0),
.cycle 12 5 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 11 12 true (1),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 4 true (0),
.cycle 11 4 true (1),
.last 22 (5,true),
.cycle 10 2 true (0),
.last 48 (5,true),
.cycle 15 1 false (3),
.cycle 12 5 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 32 1 false (2),
.last 13 (5,true),
.cycle 9 3 true (0)
])
theorem kid04_part115_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part115) = true := by rfl

def kid04_part116 : Audit := .split 11 (5,true) (byMove [
.cycle 14 1 false (2),
.cycle 9 4 true (0),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.last 23 (4,true),
.last 23 (4,true),
.last 21 (4,true),
.cycle 8 4 true (0),
.last 15 (4,true),
.last 18 (4,true),
.cycle 10 2 true (0),
.last 17 (4,true),
.cycle 15 1 false (3),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.last 27 (4,true),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part116_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part116) = true := by rfl

def kid04_part92 : Audit := .split 10 (1,true) (byMove [(kid04_part93),(kid04_part94),(kid04_part95),(kid04_part96),(kid04_part97),(kid04_part98),(kid04_part99),(kid04_part100),(kid04_part101),(kid04_part102),(kid04_part103),(kid04_part104),(kid04_part105),(kid04_part106),(kid04_part107),(kid04_part108),(kid04_part109),(kid04_part110),(kid04_part111),(kid04_part112),(kid04_part113),(kid04_part114),(kid04_part115),(kid04_part116)])

theorem kid04_part92_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part92) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part93),(kid04_part94),(kid04_part95),(kid04_part96),(kid04_part97),(kid04_part98),(kid04_part99),(kid04_part100),(kid04_part101),(kid04_part102),(kid04_part103),(kid04_part104),(kid04_part105),(kid04_part106),(kid04_part107),(kid04_part108),(kid04_part109),(kid04_part110),(kid04_part111),(kid04_part112),(kid04_part113),(kid04_part114),(kid04_part115),(kid04_part116)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part93_checked

  · exact kid04_part99_checked

  · exact kid04_part105_checked

  · exact kid04_part111_checked

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

def kid04_part118 : Audit := .cycle 21 1 false (1)
theorem kid04_part118_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part118) = true := by rfl

def kid04_part119 : Audit := .split 19 (1,true) (byMove [
.cycle 0 20 false (3),
.cycle 0 31 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 24 false (3),
.cycle 0 23 false (3),
.cycle 0 20 true (-3),
.cycle 0 31 true (-3),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 0 24 true (-3),
.cycle 0 23 true (-3),
.cycle 0 28 false (3),
.cycle 0 34 false (3),
.cycle 0 22 true (-3),
.cycle 20 1 false (-2),
.cycle 7 33 false (3),
.cycle 25 1 false (1),
.cycle 10 28 true (-3),
.cycle 1 19 false (3),
.cycle 0 30 true (-3),
.cycle 24 1 false (2),
.last 21 (5,true),
.cycle 9 11 false (1)
])
theorem kid04_part119_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part119) = true := by rfl

def kid04_part120 : Audit := .cycle 0 24 false (3)
theorem kid04_part120_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part120) = true := by rfl

def kid04_part121 : Audit := .cycle 0 20 true (-3)
theorem kid04_part121_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part121) = true := by rfl

def kid04_part122 : Audit := .cycle 0 24 false (3)
theorem kid04_part122_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part122) = true := by rfl

def kid04_part123 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 false (3),
.cycle 0 31 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 24 false (3),
.cycle 0 23 false (3),
.cycle 0 20 true (-3),
.cycle 0 31 true (-3),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 0 24 true (-3),
.cycle 0 23 true (-3),
.last 21 (1,true),
.cycle 0 26 false (3),
.cycle 0 22 true (-3),
.cycle 20 1 false (-2),
.last 25 (1,true),
.cycle 25 1 false (1),
.cycle 12 20 true (-3),
.cycle 1 19 false (3),
.cycle 0 30 true (-3),
.cycle 24 1 false (2),
.cycle 19 2 true (-1),
.cycle 9 11 false (1)
])
theorem kid04_part123_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part123) = true := by rfl

def kid04_part124 : Audit := .split 31 (5,true) (byMove [
.last 71 (1,true),
.last 63 (1,true),
.cycle 33 1 false (-1),
.cycle 32 1 false (-2),
.last 75 (1,true),
.last 55 (1,true),
.cycle 15 17 true (-1),
.last 77 (1,true),
.cycle 33 1 false (1),
.cycle 32 1 false (0),
.cycle 11 21 true (-3),
.last 36 (1,true),
.last 33 (1,true),
.last 55 (1,true),
.cycle 13 19 true (-3),
.cycle 32 1 false (-2),
.last 37 (1,true),
.cycle 37 1 false (1),
.cycle 15 17 true (-1),
.last 51 (1,true),
.cycle 10 27 true (-3),
.cycle 0 37 true (-3),
.cycle 30 2 true (-1),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 128, 1, 524288, 1048576, 32768, 17592186044420, 128, 128, 128, 256, 134217728, 18603736743018496, 1048576, 16777216, 137438953472, 274877906944, 8589934592, 67108864, 18014398509481984, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 18603736741970048, 8796093022208, 4398046511104, 137438953472, 274877906944, 35184372088832, 8589934592, 18014398509481984, 4398046511104, 562949953421312, 1125899906842624, 549755813888, 22263942231359488, 22263942231359488, 22263942231359488, 8796093022208, 17592186044416, 549755813888, 18608409666387968, 18608203507957760, 18608203507957760, 137438953472, 274877906944, 2251799813685248, 22263942231359488, 22263942231359488, 22263942231359488, 18014398509481984],[4, 18014398509481984, 1048576, 1, 1, 2048, 16384, 18014398509481984, 8796093022336, 4096, 4096, 8388608, 67108864, 18014398509481984, 1048576, 16777216, 16777216, 2048, 4294967296, 18014398509481984, 128, 1073741824, 1073741824, 2199023255552, 17592186044416, 18014398509481984, 8589934592, 4398046511104, 4398046511104, 140737488355328, 17592186044416, 18014398509481984, 18014398509481984, 4398046511104, 4398046511104, 2199023255552, 274877906944, 18014398509481984, 22263942231359488, 68719476736, 68719476736, 9007199254740992, 274877906944, 18014398509481984, 18603736741969920, 68719476736, 68719476736, 140737488355328, 1125899906842624, 18014398509481984, 22263942231359488, 281474976710656, 281474976710656, 2199023255552, 18014398509481984],36028788427907906⟩
])
theorem kid04_part124_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part124) = true := by rfl

def kid04_part125 : Audit := .far true 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[66304, 768, 512, 512, 32, 256, 1073741824, 768, 768, 512, 131072, 256, 66304, 1820394240, 512, 134217728, 8388608, 67108864, 2088829696, 768, 134217728, 512, 131072, 256, 2088829696, 2088829696, 1275069184, 134217728, 536870912, 67108864, 1073741824],[512, 1073741824, 16, 8389376, 768, 1073741824, 8388640, 1073741824, 65536, 768, 1073741824, 1073741824, 134218496, 1073741824, 4194304, 1820328704, 768, 1073741824, 512, 1073741824, 65536, 8389376, 1283457792, 1073741824, 1812071168, 1073741824, 268435456, 1820328704, 1820328704, 1073741824, 1073741824],2001085504⟩
theorem kid04_part125_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part125) = true := by rfl

def kid04_part126 : Audit := .cycle 10 15 true (-3)
theorem kid04_part126_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part126) = true := by rfl

def kid04_part127 : Audit := .cycle 0 28 true (-3)
theorem kid04_part127_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part127) = true := by rfl

def kid04_part128 : Audit := .cycle 8 11 false (2)
theorem kid04_part128_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part128) = true := by rfl

def kid04_part129 : Audit := .far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 3, 3],[128, 256, 8, 261, 128, 1, 128, 256, 32768, 4, 16777216, 261, 524288, 1048576, 8, 261, 32904, 1, 524288, 1048576, 2097152, 18088197, 19431560, 18088197, 16777216],[4, 16777216, 261, 1, 32, 16777216, 16384, 16777216, 1, 4096, 131072, 16777216, 4, 16777216, 16777216, 1, 32, 16777216, 1048576, 16777216, 18088197, 262144, 8388608, 16777216, 16777216],33305600⟩
theorem kid04_part129_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part129) = true := by rfl

def kid04_part130 : Audit := .cycle 0 25 false (3)
theorem kid04_part130_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part130) = true := by rfl

def kid04_part131 : Audit := .split 19 (1,true) (byMove [
.cycle 15 5 false (1),
.last 105 (5,true),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 11 9 false (1),
.last 25 (5,true),
.cycle 22 1 false (2),
.cycle 0 32 true (-3),
.cycle 0 25 false (3),
.cycle 0 21 true (-3),
.cycle 20 3 false (0),
.last 20 (5,true),
.cycle 10 13 false (1),
.cycle 20 3 false (-1),
.cycle 24 1 false (2),
.cycle 20 1 false (-2),
.cycle 26 3 false (-2),
.cycle 0 29 false (3),
.cycle 10 17 true (-3),
.cycle 30 3 false (0),
.cycle 20 3 false (0),
.last 33 (5,true),
.cycle 18 2 true (-1),
.last 20 (5,true)
])
theorem kid04_part131_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part131) = true := by rfl

def kid04_part132 : Audit := .cycle 10 9 false (1)
theorem kid04_part132_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part132) = true := by rfl

def kid04_part133 : Audit := .cycle 22 1 false (2)
theorem kid04_part133_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part133) = true := by rfl

def kid04_part134 : Audit := .split 25 (1,true) (byMove [
.cycle 0 29 true (-4),
.cycle 10 23 false (1),
.cycle 105 61 false (-1),
.cycle 0 30 true (-4),
.cycle 19 7 false (-1),
.last 26 (5,true),
.cycle 0 53 true (-4),
.proven (BB6.Agent11Raw39RCPumps.M8.table) (fun m hm => BB6.Agent11Raw39RCPumps.M8.never m hm),
.last 28 (5,true),
.cycle 75 24 false (-1),
.last 28 (5,true),
.last 26 (5,true),
.cycle 10 17 false (1),
.cycle 19 10 false (-1),
.cycle 10 16 false (1),
.cycle 0 33 false (3),
.cycle 19 7 false (-1),
.last 26 (5,true),
.cycle 3 26 false (3),
.far true 2 ⟨0,[0, 1, 0, 1],[1808, 784, 512, 512, 32, 256, 1808, 1024, 768, 512, 32, 256, 4096],[768, 1808, 16, 800, 1024, 4096, 32, 1808, 16, 768, 1024, 4096, 4096],4096⟩,
.cycle 17 9 false (1),
.last 39 (5,true),
.cycle 18 9 false (0),
.last 26 (5,true)
])
theorem kid04_part134_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part134) = true := by rfl

def kid04_part135 : Audit := .split 19 (5,true) (byMove [
.cycle 15 5 false (1),
.cycle 13 59 true (-5),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 11 9 false (1),
.last 24 (1,true),
.cycle 22 1 false (2),
.last 20 (1,true),
.cycle 0 25 false (3),
.cycle 0 21 true (-3),
.cycle 26 1 false (2),
.cycle 0 24 true (-3),
.last 21 (1,true),
.cycle 0 29 true (-4),
.cycle 24 1 false (2),
.cycle 20 1 false (-2),
.last 25 (1,true),
.cycle 0 29 false (3),
.cycle 10 17 true (-3),
.last 20 (1,true),
.cycle 27 1 false (1),
.cycle 0 39 true (-3),
.cycle 18 2 true (-1),
.cycle 0 30 true (-3)
])
theorem kid04_part135_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part135) = true := by rfl

def kid04_part136 : Audit := .split 32 (1,true) (byMove [
.cycle 0 228 true (-5),
.cycle 0 47 false (4),
.cycle 17 16 true (0),
.last 46 (5,true),
.cycle 18 15 true (0),
.last 33 (5,true),
.last 45 (5,true),
.last 79 (5,true),
.proven (BB6.Agent11Raw39RCPumps.M10.table) (fun m hm => BB6.Agent11Raw39RCPumps.M10.never m hm),
.cycle 3 41 false (4),
.cycle 27 6 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 3, 3],[128, 256, 8, 16941445, 128, 1, 128, 256, 32768, 4, 16777216, 131201, 524288, 1048576, 8, 33152, 385, 1, 524288, 1048576, 2097152, 29262221, 29262221, 29262221, 16777216],[4, 32, 33152, 1, 64, 16777216, 16384, 131072, 128, 4096, 64, 16777216, 4, 32, 16777216, 1, 262144, 16777216, 1048576, 8388608, 29262221, 262144, 262144, 16777216, 16777216],33322508⟩,
.last 36 (5,true),
.cycle 33 7 false (1),
.cycle 29 4 true (0),
.cycle 107 191 true (-4),
.proven (BB6.Agent11Raw39RCPumps.M12.table) (fun m hm => BB6.Agent11Raw39RCPumps.M12.never m hm),
.last 33 (5,true),
.cycle 19 14 true (0),
.cycle 20 13 true (0),
.cycle 21 12 true (0),
.cycle 29 181 true (-4),
.last 34 (5,true),
.cycle 28 5 true (0)
])
theorem kid04_part136_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part136) = true := by rfl

def kid04_part137 : Audit := .cycle 16 14 true (-1)
theorem kid04_part137_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part137) = true := by rfl

def kid04_part138 : Audit := .cycle 2 17 false (3)
theorem kid04_part138_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part138) = true := by rfl

def kid04_part139 : Audit := .cycle 4 34 true (-3)
theorem kid04_part139_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part139) = true := by rfl

def kid04_part140 : Audit := .split 20 (5,true) (byMove [
.cycle 23 1 false (1),
.last 21 (1,true),
.cycle 0 26 false (3),
.cycle 0 22 true (-3),
.cycle 0 28 false (3),
.cycle 0 25 false (3),
.cycle 15 19 true (-1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 256, 128, 1, 128, 256, 32768, 4, 256, 257, 128, 256, 8, 256, 32896, 1, 262144],[4, 262144, 256, 1, 1024, 2, 16384, 262144, 256, 4096, 1024, 8192, 4, 262144, 32768, 1, 1024, 2, 262144],262144⟩,
.cycle 10 17 true (-3),
.cycle 0 30 true (-3),
.cycle 8 13 false (2),
.far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 3, 3],[128, 256, 8, 261, 128, 1, 128, 256, 32768, 4, 1, 261, 524288, 1048576, 8, 261, 32904, 1, 524288, 1048576, 2097152, 20742541, 20742541, 20742541, 16777216],[4, 16777216, 261, 1, 1024, 32, 16384, 16777216, 1, 4096, 1024, 131072, 4, 16777216, 128, 1, 4194304, 32, 1048576, 16777216, 20742541, 262144, 4194304, 8388608, 16777216],33304576⟩,
.cycle 0 27 false (3),
.last 21 (1,true),
.cycle 10 11 false (1),
.cycle 24 1 false (2),
.cycle 18 4 true (-1),
.cycle 0 31 false (3),
.last 36 (1,true),
.cycle 16 18 true (-1),
.cycle 2 19 false (3),
.cycle 4 38 true (-3),
.cycle 19 2 true (0),
.cycle 9 17 false (1)
])
theorem kid04_part140_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part140) = true := by rfl

def kid04_part141 : Audit := .cycle 9 13 false (1)
theorem kid04_part141_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part141) = true := by rfl

def kid04_part117 : Audit := .split 18 (4,true) (byMove [(kid04_part118),(kid04_part119),(kid04_part120),(kid04_part121),(kid04_part122),(kid04_part123),(kid04_part124),(kid04_part125),(kid04_part126),(kid04_part127),(kid04_part128),(kid04_part129),(kid04_part130),(kid04_part131),(kid04_part132),(kid04_part133),(kid04_part134),(kid04_part135),(kid04_part136),(kid04_part137),(kid04_part138),(kid04_part139),(kid04_part140),(kid04_part141)])

theorem kid04_part117_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part117) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some mv)) (byMove [(kid04_part118),(kid04_part119),(kid04_part120),(kid04_part121),(kid04_part122),(kid04_part123),(kid04_part124),(kid04_part125),(kid04_part126),(kid04_part127),(kid04_part128),(kid04_part129),(kid04_part130),(kid04_part131),(kid04_part132),(kid04_part133),(kid04_part134),(kid04_part135),(kid04_part136),(kid04_part137),(kid04_part138),(kid04_part139),(kid04_part140),(kid04_part141)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part118_checked

  · exact kid04_part124_checked

  · exact kid04_part130_checked

  · exact kid04_part136_checked

  · exact kid04_part119_checked

  · exact kid04_part125_checked

  · exact kid04_part131_checked

  · exact kid04_part137_checked

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

def kid04_part142 : Audit := .cycle 13 1 false (3)
theorem kid04_part142_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part142) = true := by rfl

def kid04_part143 : Audit := .split 10 (4,true) (byMove [
.cycle 17 1 false (1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 13 1 false (3),
.split 11 (1,true) (byMove [
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
.cycle 16 2 false (0),
.cycle 22 2 false (2),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 2 false (2),
.cycle 16 1 false (4),
.last 13 (5,true),
.cycle 9 3 true (0)
]),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 12 2 false (2),
.split 11 (5,true) (byMove [
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
.last 13 (1,true),
.cycle 15 2 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 2 false (2),
.cycle 16 1 false (4),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
]),
.split 12 (1,true) (byMove [
.cycle 0 16 true (-1),
.cycle 21 2 false (-1),
.cycle 14 2 false (-2),
.cycle 0 17 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 22 2 false (0),
.last 44 (5,true),
.last 15 (5,true),
.cycle 0 14 true (-1),
.cycle 21 2 false (-1),
.last 13 (5,true),
.cycle 15 2 false (-1),
.cycle 10 6 false (0),
.cycle 14 2 false (-2),
.cycle 16 2 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 3 13 false (3),
.last 27 (5,true),
.cycle 17 2 false (-1),
.cycle 0 14 true (-1),
.last 17 (5,true),
.last 13 (5,true)
]),
.cycle 10 3 false (0),
.cycle 15 1 false (3),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 19 2 false (1),
.split 11 (1,true) (byMove [
.cycle 14 1 false (2),
.cycle 20 2 false (0),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.last 22 (5,true),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 8 4 true (0),
.last 14 (5,true),
.cycle 14 2 false (0),
.far false 5 ⟨0,[0, 1, 2, 1, 1, 3, 4, 1, 3, 3],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 1048836, 1073741824, 320, 524288, 1048576, 512, 256, 32896, 1073741824, 128, 256, 134217728, 1140867072, 1073741824, 320, 524288, 1048576, 2097152, 1073741824, 32896, 1073741824, 1073741824],[4, 256, 0, 1, 128, 1073741824, 16384, 256, 256, 4096, 128, 1073741824, 256, 256, 1073741824, 64, 524288, 1073741824, 67108864, 256, 256, 16777216, 128, 1073741824, 1048576, 256, 1073741824, 262144, 524288, 1073741824, 1073741824],1852990976⟩,
.cycle 13 2 false (-1),
.cycle 15 1 false (3),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 23 2 false (1),
.last 13 (5,true),
.cycle 9 3 true (0)
]),
.cycle 19 2 false (1),
.cycle 0 12 true (0),
.split 13 (5,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 17 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 14 true (0),
.cycle 37 2 false (3),
.cycle 21 2 false (1),
.cycle 19 2 false (1),
.cycle 8 6 true (0),
.cycle 17 2 false (1),
.cycle 16 2 false (0),
.last 14 (1,true),
.cycle 15 2 false (-1),
.cycle 17 1 false (3),
.cycle 10 4 true (0),
.cycle 15 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 25 2 false (1),
.cycle 12 2 true (1),
.cycle 9 5 true (0)
]),
.split 11 (5,true) (byMove [
.cycle 14 1 false (2),
.last 12 (1,true),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 9 4 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 9 17 true (0),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 8 4 true (0),
.cycle 15 2 false (1),
.cycle 14 2 false (0),
.last 12 (1,true),
.cycle 13 2 false (-1),
.cycle 15 1 false (3),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 23 2 false (1),
.cycle 11 2 true (1),
.cycle 9 3 true (0)
])
])
theorem kid04_part143_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part143) = true := by rfl

def kid04_part145 : Audit := .split 14 (4,true) (byMove [
.cycle 17 1 false (1),
.last 15 (1,true),
.cycle 17 1 false (-3),
.cycle 0 16 true (-1),
.cycle 17 1 false (-3),
.cycle 0 16 false (3),
.cycle 0 15 true (-1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 260, 32776, 260, 128, 256, 32768, 4, 33028, 261, 2, 4, 8, 260, 32904, 260, 262144],[4, 262144, 260, 1, 2, 264, 16384, 262144, 260, 4096, 8192, 8, 4, 262144, 33036, 1, 2, 256, 262144],262144⟩,
.cycle 23 1 false (-1),
.cycle 21 1 false (-1),
.cycle 8 7 false (2),
.cycle 9 7 false (1),
.cycle 18 1 false (-2),
.last 15 (1,true),
.cycle 17 1 false (-3),
.cycle 18 1 false (2),
.cycle 17 1 false (-3),
.cycle 10 5 false (1),
.cycle 0 29 true (-1),
.cycle 0 28 true (-1),
.cycle 2 13 false (3),
.cycle 27 1 false (-1),
.cycle 19 1 false (1),
.cycle 0 20 true (-1)
])
theorem kid04_part145_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part145) = true := by rfl

def kid04_part146 : Audit := .cycle 0 14 true (-1)
theorem kid04_part146_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part146) = true := by rfl

def kid04_part147 : Audit := .cycle 12 1 false (0)
theorem kid04_part147_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part147) = true := by rfl

def kid04_part148 : Audit := .cycle 11 1 false (-1)
theorem kid04_part148_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part148) = true := by rfl

def kid04_part149 : Audit := .cycle 12 1 false (-2)
theorem kid04_part149_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part149) = true := by rfl

def kid04_part150 : Audit := .cycle 11 1 false (-1)
theorem kid04_part150_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part150) = true := by rfl

def kid04_part151 : Audit := .cycle 13 1 false (3)
theorem kid04_part151_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part151) = true := by rfl

def kid04_part152 : Audit := .split 11 (1,true) (byMove [
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
.cycle 17 1 false (-1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 16 1 false (4),
.cycle 22 1 false (2),
.cycle 9 3 true (0)
])
theorem kid04_part152_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part152) = true := by rfl

def kid04_part153 : Audit := .cycle 13 1 false (-1)
theorem kid04_part153_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part153) = true := by rfl

def kid04_part154 : Audit := .cycle 0 12 true (0)
theorem kid04_part154_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part154) = true := by rfl

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
.last 13 (1,true),
.cycle 11 3 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 16 1 false (4),
.cycle 15 1 false (1),
.cycle 9 3 true (0)
])
theorem kid04_part155_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part155) = true := by rfl

def kid04_part156 : Audit := .cycle 12 1 false (2)
theorem kid04_part156_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part156) = true := by rfl

def kid04_part157 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (-1),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 0 17 true (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 23 1 false (-1),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 2, 4, 2, 4],[262144, 2048, 2097152, 512, 32, 2048, 16777216, 1073741824, 16777216, 2097152, 131072, 8388608, 1761775616, 1761775616, 1761775616, 32768, 131072, 131072, 16777216, 1073741824, 134217728, 134217728, 131072, 536870912, 16777216, 1073741824, 8519680, 134217728, 131072, 536870912, 1073741824],[134217728, 8388608, 16, 16777216, 1073741824, 64, 32, 536870912, 65536, 134217728, 1073741824, 262144, 1761775616, 1761775616, 65536, 1761775616, 1073741824, 4096, 131072, 536870912, 65536, 2048, 1073741824, 16777216, 131072, 536870912, 65536, 131072, 1073741824, 16777216, 1073741824],1107849344⟩,
.cycle 26 1 false (-2),
.cycle 0 14 true (-1),
.last 13 (4,true),
.cycle 22 1 false (-2),
.cycle 16 1 false (-2),
.last 16 (4,true),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 3 13 false (3),
.cycle 0 33 true (-2),
.last 14 (4,true),
.cycle 0 14 true (-1),
.last 13 (4,true),
.cycle 25 1 false (-3)
])
theorem kid04_part157_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part157) = true := by rfl

def kid04_part158 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 15 (1,true),
.cycle 25 1 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (1,true),
.cycle 11 3 false (0),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 15 (1,true),
.last 27 (1,true),
.cycle 0 16 true (-1),
.cycle 19 1 false (-1),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
])
theorem kid04_part158_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part158) = true := by rfl

def kid04_part159 : Audit := .cycle 15 1 false (3)
theorem kid04_part159_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part159) = true := by rfl

def kid04_part160 : Audit := .cycle 11 1 false (-1)
theorem kid04_part160_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part160) = true := by rfl

def kid04_part161 : Audit := .cycle 12 1 false (-2)
theorem kid04_part161_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part161) = true := by rfl

def kid04_part162 : Audit := .cycle 11 1 false (-1)
theorem kid04_part162_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part162) = true := by rfl

def kid04_part163 : Audit := .cycle 20 1 false (0)
theorem kid04_part163_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part163) = true := by rfl

def kid04_part164 : Audit := .split 11 (1,true) (byMove [
.cycle 14 1 false (2),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (0),
.cycle 0 12 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 13, 256, 2, 128, 256, 8, 4, 256, 2, 4096],[4, 2, 8, 1, 4096, 128, 4, 2, 4096, 1, 4096, 128, 4096],4096⟩,
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 4 true (0),
.cycle 1 16 true (0),
.cycle 15 1 false (-1),
.last 15 (4,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (3),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 24 1 false (0),
.cycle 1 13 true (0),
.cycle 9 3 true (0)
])
theorem kid04_part164_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part164) = true := by rfl

def kid04_part165 : Audit := .split 12 (4,true) (byMove [
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
.last 14 (1,true),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 17 1 false (3),
.cycle 22 1 false (0),
.cycle 9 4 true (0)
])
theorem kid04_part165_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part165) = true := by rfl

def kid04_part166 : Audit := .cycle 0 12 true (0)
theorem kid04_part166_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part166) = true := by rfl

def kid04_part167 : Audit := .split 11 (4,true) (byMove [
.cycle 14 1 false (2),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.cycle 12 2 true (0),
.cycle 0 12 true (0),
.last 24 (1,true),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 4 true (0),
.cycle 16 2 true (2),
.cycle 15 1 false (-1),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (3),
.cycle 14 1 false (-2),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 24 1 false (0),
.cycle 12 2 true (1),
.cycle 9 3 true (0)
])
theorem kid04_part167_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part167) = true := by rfl

def kid04_part168 : Audit := .cycle 9 3 true (0)
theorem kid04_part168_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part168) = true := by rfl

def kid04_part144 : Audit := .split 10 (5,true) (byMove [(kid04_part145),(kid04_part146),(kid04_part147),(kid04_part148),(kid04_part149),(kid04_part150),(kid04_part151),(kid04_part152),(kid04_part153),(kid04_part154),(kid04_part155),(kid04_part156),(kid04_part157),(kid04_part158),(kid04_part159),(kid04_part160),(kid04_part161),(kid04_part162),(kid04_part163),(kid04_part164),(kid04_part165),(kid04_part166),(kid04_part167),(kid04_part168)])

theorem kid04_part144_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part144) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part145),(kid04_part146),(kid04_part147),(kid04_part148),(kid04_part149),(kid04_part150),(kid04_part151),(kid04_part152),(kid04_part153),(kid04_part154),(kid04_part155),(kid04_part156),(kid04_part157),(kid04_part158),(kid04_part159),(kid04_part160),(kid04_part161),(kid04_part162),(kid04_part163),(kid04_part164),(kid04_part165),(kid04_part166),(kid04_part167),(kid04_part168)] mv))) = true

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
theorem kid04_part169_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part169) = true := by rfl

def kid04_part170 : Audit := .cycle 1 9 true (1)
theorem kid04_part170_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part170) = true := by rfl

def kid04_part171 : Audit := .cycle 2 8 true (1)
theorem kid04_part171_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part171) = true := by rfl

def kid04_part172 : Audit := .cycle 30 1 false (6)
theorem kid04_part172_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part172) = true := by rfl

def kid04_part174 : Audit := .cycle 14 1 false (2)
theorem kid04_part174_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part174) = true := by rfl

def kid04_part175 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.cycle 13 11 false (0),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (1),
.cycle 13 11 false (2),
.cycle 15 11 false (0),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 17 1 false (3),
.cycle 13 11 false (1),
.cycle 9 4 true (0)
])
theorem kid04_part175_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part175) = true := by rfl

def kid04_part176 : Audit := .cycle 18 1 false (-2)
theorem kid04_part176_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part176) = true := by rfl

def kid04_part177 : Audit := .cycle 0 13 true (0)
theorem kid04_part177_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part177) = true := by rfl

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
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 15 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 4 false (1),
.cycle 17 1 false (3),
.cycle 13 4 false (1),
.cycle 9 4 true (0)
])
theorem kid04_part178_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part178) = true := by rfl

def kid04_part179 : Audit := .cycle 12 3 false (0)
theorem kid04_part179_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part179) = true := by rfl

def kid04_part180 : Audit := .cycle 0 12 true (0)
theorem kid04_part180_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part180) = true := by rfl

def kid04_part181 : Audit := .cycle 1 11 true (1)
theorem kid04_part181_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part181) = true := by rfl

def kid04_part182 : Audit := .cycle 24 1 false (2)
theorem kid04_part182_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part182) = true := by rfl

def kid04_part183 : Audit := .cycle 21 1 false (1)
theorem kid04_part183_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part183) = true := by rfl

def kid04_part184 : Audit := .cycle 8 4 true (1)
theorem kid04_part184_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part184) = true := by rfl

def kid04_part185 : Audit := .cycle 9 3 true (1)
theorem kid04_part185_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part185) = true := by rfl

def kid04_part186 : Audit := .split 19 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 12 14 false (1),
.cycle 13 7 false (1),
.cycle 0 21 false (3),
.last 20 (4,true),
.cycle 17 3 false (-1),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 8 12 false (2),
.cycle 15 5 true (-2),
.cycle 12 8 false (1),
.last 23 (4,true),
.cycle 13 7 false (1),
.cycle 23 1 false (1),
.last 20 (4,true),
.cycle 17 3 false (-1),
.cycle 10 24 false (3),
.cycle 16 17 false (2),
.cycle 2 18 false (3),
.cycle 28 36 true (-4),
.cycle 10 10 false (2),
.cycle 16 9 false (1)
])
theorem kid04_part186_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part186) = true := by rfl

def kid04_part187 : Audit := .split 12 (1,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 15 1 false (3),
.last 27 (4,true),
.last 20 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true),
.last 23 (4,true),
.last 15 (4,true),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 14 (4,true),
.last 27 (4,true),
.cycle 1 13 true (0),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (0)
])
theorem kid04_part187_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part187) = true := by rfl

def kid04_part188 : Audit := .split 22 (4,true) (byMove [
.cycle 25 1 false (1),
.last 23 (1,true),
.cycle 0 30 false (3),
.cycle 0 24 true (-3),
.cycle 0 30 false (3),
.cycle 0 26 true (-3),
.cycle 15 21 true (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 10, 16, 64],[4, 64, 4, 1, 2, 5, 64],64⟩,
.cycle 12 17 true (-3),
.cycle 0 34 true (-3),
.cycle 8 15 false (2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 17445, 128, 1024, 8192, 16384, 8, 4, 128, 65536, 33554432, 67108864, 2097152, 4, 128, 268435456, 33554432, 67108864, 2097152, 17445, 2134131885, 268435456, 33554432, 67108864, 134217728, 2134131885, 2134131885, 268435456, 1073741824],[4, 1073741824, 16384, 1, 32, 1, 4, 1073741824, 1024, 1, 32, 1024, 1048576, 1073741824, 1024, 262144, 8388608, 32, 1048576, 1073741824, 2134131885, 262144, 8388608, 262144, 67108864, 1073741824, 2134131885, 16777216, 536870912, 2134131885, 1073741824],2144219200⟩,
.cycle 0 31 false (3),
.last 23 (1,true),
.cycle 12 11 false (1),
.cycle 26 1 false (2),
.last 31 (1,true),
.cycle 28 1 false (2),
.last 38 (1,true),
.cycle 20 16 true (-1),
.cycle 2 21 false (3),
.cycle 4 40 true (-3),
.cycle 10 13 false (2),
.cycle 22 7 true (-1)
])
theorem kid04_part188_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part188) = true := by rfl

def kid04_part189 : Audit := .cycle 15 1 false (3)
theorem kid04_part189_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part189) = true := by rfl

def kid04_part190 : Audit := .split 12 (4,true) (byMove [
.cycle 19 1 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 15 1 false (3),
.last 13 (1,true),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 14 4 false (2),
.cycle 13 4 false (1),
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 15 4 false (-1),
.cycle 21 4 false (1),
.last 13 (1,true),
.cycle 21 4 false (1),
.cycle 0 14 true (0),
.cycle 10 4 true (0),
.cycle 11 2 true (0)
])
theorem kid04_part190_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part190) = true := by rfl

def kid04_part191 : Audit := .split 14 (4,true) (byMove [
.cycle 0 18 true (-1),
.last 15 (1,true),
.cycle 12 7 false (0),
.last 17 (1,true),
.cycle 12 7 false (0),
.cycle 12 3 false (0),
.last 35 (1,true),
.last 15 (1,true),
.cycle 16 13 false (1),
.cycle 0 16 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 0, 16, 64],[4, 64, 0, 1, 16, 16, 64],64⟩,
.cycle 15 5 true (0),
.cycle 12 8 false (0),
.last 15 (1,true),
.cycle 12 7 false (0),
.cycle 27 1 false (1),
.cycle 12 7 false (0),
.cycle 12 3 false (0),
.cycle 3 15 false (3),
.last 15 (1,true),
.cycle 2 15 false (3),
.cycle 0 16 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 0, 16, 64],[4, 64, 0, 1, 16, 16, 64],64⟩,
.cycle 11 5 false (1)
])
theorem kid04_part191_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part191) = true := by rfl

def kid04_part192 : Audit := .cycle 0 12 true (0)
theorem kid04_part192_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part192) = true := by rfl

def kid04_part193 : Audit := .cycle 1 11 true (1)
theorem kid04_part193_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part193) = true := by rfl

def kid04_part194 : Audit := .cycle 2 10 true (1)
theorem kid04_part194_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part194) = true := by rfl

def kid04_part195 : Audit := .cycle 34 1 false (6)
theorem kid04_part195_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part195) = true := by rfl

def kid04_part196 : Audit := .cycle 10 2 true (1)
theorem kid04_part196_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part196) = true := by rfl

def kid04_part197 : Audit := .cycle 9 3 true (1)
theorem kid04_part197_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part197) = true := by rfl

def kid04_part173 : Audit := .split 11 (5,true) (byMove [(kid04_part174),(kid04_part175),(kid04_part176),(kid04_part177),(kid04_part178),(kid04_part179),(kid04_part180),(kid04_part181),(kid04_part182),(kid04_part183),(kid04_part184),(kid04_part185),(kid04_part186),(kid04_part187),(kid04_part188),(kid04_part189),(kid04_part190),(kid04_part191),(kid04_part192),(kid04_part193),(kid04_part194),(kid04_part195),(kid04_part196),(kid04_part197)])

theorem kid04_part173_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part173) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some mv)) (byMove [(kid04_part174),(kid04_part175),(kid04_part176),(kid04_part177),(kid04_part178),(kid04_part179),(kid04_part180),(kid04_part181),(kid04_part182),(kid04_part183),(kid04_part184),(kid04_part185),(kid04_part186),(kid04_part187),(kid04_part188),(kid04_part189),(kid04_part190),(kid04_part191),(kid04_part192),(kid04_part193),(kid04_part194),(kid04_part195),(kid04_part196),(kid04_part197)] mv))) = true

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
theorem kid04_part198_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part198) = true := by rfl

def kid04_part54 : Audit := .split 9 (5,false) (byMove [(kid04_part55),(kid04_part56),(kid04_part57),(kid04_part58),(kid04_part59),(kid04_part60),(kid04_part61),(kid04_part62),(kid04_part63),(kid04_part64),(kid04_part65),(kid04_part66),(kid04_part67),(kid04_part92),(kid04_part117),(kid04_part142),(kid04_part143),(kid04_part144),(kid04_part169),(kid04_part170),(kid04_part171),(kid04_part172),(kid04_part173),(kid04_part198)])

theorem kid04_part54_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (kid04_part54) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part55),(kid04_part56),(kid04_part57),(kid04_part58),(kid04_part59),(kid04_part60),(kid04_part61),(kid04_part62),(kid04_part63),(kid04_part64),(kid04_part65),(kid04_part66),(kid04_part67),(kid04_part92),(kid04_part117),(kid04_part142),(kid04_part143),(kid04_part144),(kid04_part169),(kid04_part170),(kid04_part171),(kid04_part172),(kid04_part173),(kid04_part198)] mv))) = true

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

  · exact kid04_part92_checked

  · exact kid04_part170_checked

  · exact kid04_part57_checked

  · exact kid04_part63_checked

  · exact kid04_part117_checked

  · exact kid04_part171_checked

  · exact kid04_part58_checked

  · exact kid04_part64_checked

  · exact kid04_part142_checked

  · exact kid04_part172_checked

  · exact kid04_part59_checked

  · exact kid04_part65_checked

  · exact kid04_part143_checked

  · exact kid04_part173_checked

  · exact kid04_part60_checked

  · exact kid04_part66_checked

  · exact kid04_part144_checked

  · exact kid04_part198_checked

def kid04_part199 : Audit := .cycle 0 9 true (0)
theorem kid04_part199_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,0⟩)) (kid04_part199) = true := by rfl

def kid04_part200 : Audit := .cycle 1 8 true (1)
theorem kid04_part200_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,1⟩)) (kid04_part200) = true := by rfl

def kid04_part201 : Audit := .cycle 22 1 false (6)
theorem kid04_part201_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,2⟩)) (kid04_part201) = true := by rfl

def kid04_part202 : Audit := .cycle 16 1 false (2)
theorem kid04_part202_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,3⟩)) (kid04_part202) = true := by rfl

def kid04_part203 : Audit := .cycle 8 1 true (2)
theorem kid04_part203_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,4⟩)) (kid04_part203) = true := by rfl

def kid04_part205 : Audit := .cycle 0 10 true (0)
theorem kid04_part205_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part205) = true := by rfl

def kid04_part206 : Audit := .cycle 1 9 true (1)
theorem kid04_part206_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part206) = true := by rfl

def kid04_part207 : Audit := .cycle 20 1 false (2)
theorem kid04_part207_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part207) = true := by rfl

def kid04_part208 : Audit := .cycle 17 1 false (1)
theorem kid04_part208_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part208) = true := by rfl

def kid04_part209 : Audit := .cycle 8 2 true (2)
theorem kid04_part209_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part209) = true := by rfl

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
.split 14 (1,true) (byMove [
.cycle 17 1 false (1),
.cycle 24 1 false (0),
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
.last 18 (4,true),
.cycle 17 1 false (-1),
.cycle 18 1 false (2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 10 21 false (4),
.cycle 30 1 false (0),
.cycle 2 13 false (3),
.cycle 27 1 false (1),
.cycle 22 1 false (0),
.cycle 20 1 false (0)
]),
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
.last 17 (1,true),
.cycle 13 3 false (0),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 12 5 false (0),
.cycle 16 1 false (-2),
.last 29 (1,true),
.cycle 1 15 false (3),
.cycle 23 1 false (1),
.cycle 20 1 false (2),
.cycle 10 7 false (2),
.cycle 11 5 false (1)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 17 1 false (3),
.cycle 10 4 true (0),
.cycle 11 2 true (0)
])
theorem kid04_part210_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part210) = true := by rfl

def kid04_part211 : Audit := .cycle 0 10 true (0)
theorem kid04_part211_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part211) = true := by rfl

def kid04_part212 : Audit := .cycle 1 9 true (1)
theorem kid04_part212_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part212) = true := by rfl

def kid04_part213 : Audit := .cycle 31 1 false (7)
theorem kid04_part213_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part213) = true := by rfl

def kid04_part214 : Audit := .cycle 22 1 false (6)
theorem kid04_part214_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part214) = true := by rfl

def kid04_part215 : Audit := .cycle 8 2 true (2)
theorem kid04_part215_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part215) = true := by rfl

def kid04_part216 : Audit := .cycle 9 1 true (3)
theorem kid04_part216_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part216) = true := by rfl

def kid04_part218 : Audit := .cycle 30 1 false (6)
theorem kid04_part218_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part218) = true := by rfl

def kid04_part219 : Audit := .cycle 1 12 true (1)
theorem kid04_part219_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part219) = true := by rfl

def kid04_part220 : Audit := .split 18 (4,true) (byMove [
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
.cycle 19 5 false (0),
.cycle 17 3 false (1),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.last 20 (5,true),
.cycle 19 5 false (-1),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 24 5 false (2),
.cycle 23 1 false (3),
.cycle 13 6 true (0),
.cycle 21 5 false (1)
])
theorem kid04_part220_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part220) = true := by rfl

def kid04_part221 : Audit := .cycle 0 13 true (0)
theorem kid04_part221_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part221) = true := by rfl

def kid04_part222 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 18 5 false (0),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.cycle 21 3 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 8 5 true (2),
.cycle 6 8 true (2)
])
theorem kid04_part222_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part222) = true := by rfl

def kid04_part223 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 18 (4,true),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 8 5 true (2),
.cycle 6 8 true (2)
])
theorem kid04_part223_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part223) = true := by rfl

def kid04_part224 : Audit := .cycle 0 12 true (0)
theorem kid04_part224_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part224) = true := by rfl

def kid04_part225 : Audit := .cycle 1 11 true (1)
theorem kid04_part225_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part225) = true := by rfl

def kid04_part226 : Audit := .cycle 7 16 true (2)
theorem kid04_part226_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part226) = true := by rfl

def kid04_part227 : Audit := .cycle 3 9 true (1)
theorem kid04_part227_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part227) = true := by rfl

def kid04_part228 : Audit := .cycle 8 4 true (2)
theorem kid04_part228_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part228) = true := by rfl

def kid04_part229 : Audit := .cycle 9 3 true (2)
theorem kid04_part229_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part229) = true := by rfl

def kid04_part230 : Audit := .cycle 6 6 true (2)
theorem kid04_part230_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part230) = true := by rfl

def kid04_part231 : Audit := .split 15 (4,true) (byMove [
.cycle 18 1 false (2),
.cycle 16 15 false (0),
.cycle 26 1 false (-2),
.cycle 0 22 true (0),
.cycle 16 8 false (0),
.last 16 (5,true),
.cycle 10 6 true (1),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.last 17 (5,true),
.cycle 19 7 false (1),
.cycle 20 6 false (1),
.cycle 17 3 false (0),
.cycle 19 8 true (-3),
.cycle 0 20 true (0),
.last 18 (5,true),
.last 16 (5,true),
.cycle 18 7 false (2),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 23 11 false (1)
])
theorem kid04_part231_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part231) = true := by rfl

def kid04_part232 : Audit := .split 18 (4,true) (byMove [
.cycle 68 1 false (0),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (0),
.cycle 19 5 false (-1),
.cycle 19 5 false (2),
.cycle 31 5 false (5),
.cycle 23 1 false (5),
.cycle 19 1 false (1),
.last 20 (5,true),
.cycle 19 5 false (1),
.cycle 19 5 false (0),
.cycle 17 3 false (1),
.cycle 21 5 false (2),
.cycle 19 1 false (-1),
.last 20 (5,true),
.cycle 19 5 false (-1),
.cycle 15 4 true (0),
.cycle 1 24 true (0),
.cycle 30 5 false (2),
.cycle 22 5 false (2),
.last 20 (5,true),
.cycle 21 5 false (1)
])
theorem kid04_part232_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part232) = true := by rfl

def kid04_part233 : Audit := .cycle 51 1 false (7)
theorem kid04_part233_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part233) = true := by rfl

def kid04_part234 : Audit := .split 12 (4,true) (byMove [
.cycle 36 1 false (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 18 5 false (0),
.cycle 17 4 false (1),
.cycle 51 1 false (7),
.last 15 (5,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.last 13 (5,true),
.cycle 20 3 false (1),
.last 18 (5,true),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 17 4 false (1),
.cycle 6 20 true (2),
.cycle 11 2 true (2),
.cycle 2 13 true (1),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.last 13 (5,true)
])
theorem kid04_part234_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part234) = true := by rfl

def kid04_part235 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 18 (4,true),
.cycle 17 4 false (1),
.cycle 51 1 false (7),
.cycle 23 5 false (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 5 true (2),
.cycle 20 3 false (1),
.last 15 (4,true),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 17 4 false (1),
.cycle 6 20 true (2),
.cycle 11 2 true (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 6 9 true (2)
])
theorem kid04_part235_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part235) = true := by rfl

def kid04_part236 : Audit := .cycle 0 12 true (0)
theorem kid04_part236_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part236) = true := by rfl

def kid04_part237 : Audit := .cycle 1 11 true (1)
theorem kid04_part237_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part237) = true := by rfl

def kid04_part238 : Audit := .cycle 2 10 true (1)
theorem kid04_part238_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part238) = true := by rfl

def kid04_part239 : Audit := .cycle 13 14 true (2)
theorem kid04_part239_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part239) = true := by rfl

def kid04_part240 : Audit := .cycle 8 4 true (2)
theorem kid04_part240_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part240) = true := by rfl

def kid04_part241 : Audit := .cycle 6 7 true (2)
theorem kid04_part241_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part241) = true := by rfl

def kid04_part217 : Audit := .split 11 (1,true) (byMove [(kid04_part218),(kid04_part219),(kid04_part220),(kid04_part221),(kid04_part222),(kid04_part223),(kid04_part224),(kid04_part225),(kid04_part226),(kid04_part227),(kid04_part228),(kid04_part229),(kid04_part230),(kid04_part231),(kid04_part232),(kid04_part233),(kid04_part234),(kid04_part235),(kid04_part236),(kid04_part237),(kid04_part238),(kid04_part239),(kid04_part240),(kid04_part241)])

theorem kid04_part217_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part217) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part218),(kid04_part219),(kid04_part220),(kid04_part221),(kid04_part222),(kid04_part223),(kid04_part224),(kid04_part225),(kid04_part226),(kid04_part227),(kid04_part228),(kid04_part229),(kid04_part230),(kid04_part231),(kid04_part232),(kid04_part233),(kid04_part234),(kid04_part235),(kid04_part236),(kid04_part237),(kid04_part238),(kid04_part239),(kid04_part240),(kid04_part241)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part218_checked

  · exact kid04_part224_checked

  · exact kid04_part230_checked

  · exact kid04_part236_checked

  · exact kid04_part219_checked

  · exact kid04_part225_checked

  · exact kid04_part231_checked

  · exact kid04_part237_checked

  · exact kid04_part220_checked

  · exact kid04_part226_checked

  · exact kid04_part232_checked

  · exact kid04_part238_checked

  · exact kid04_part221_checked

  · exact kid04_part227_checked

  · exact kid04_part233_checked

  · exact kid04_part239_checked

  · exact kid04_part222_checked

  · exact kid04_part228_checked

  · exact kid04_part234_checked

  · exact kid04_part240_checked

  · exact kid04_part223_checked

  · exact kid04_part229_checked

  · exact kid04_part235_checked

  · exact kid04_part241_checked

def kid04_part242 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 18 5 false (0),
.split 14 (1,true) (byMove [
.last 19 (5,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 4 false (0),
.cycle 15 4 false (-1),
.cycle 17 1 false (3),
.cycle 24 4 false (4),
.cycle 17 4 false (1),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.last 15 (5,true),
.cycle 20 4 false (0),
.cycle 15 4 false (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 4 false (-1),
.cycle 24 4 false (2),
.cycle 1 15 true (0),
.cycle 15 4 false (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 9 4 true (2),
.split 14 (1,true) (byMove [
.cycle 32 1 false (2),
.cycle 15 15 false (1),
.cycle 15 8 false (1),
.cycle 0 16 true (0),
.cycle 22 3 false (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 22 13 false (2),
.cycle 22 9 false (1),
.cycle 15 6 false (1),
.cycle 15 8 false (1),
.cycle 38 1 false (6),
.cycle 22 3 false (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.cycle 22 21 false (3),
.last 17 (5,true)
]),
.split 16 (1,true) (byMove [
.cycle 13 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 3 false (0),
.cycle 18 3 false (-1),
.cycle 19 1 false (3),
.cycle 27 3 false (4),
.cycle 20 3 false (1),
.cycle 0 18 true (0),
.cycle 17 3 false (1),
.last 17 (5,true),
.cycle 23 3 false (0),
.cycle 17 3 false (0),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.last 18 (5,true),
.cycle 18 3 false (-1),
.cycle 27 3 false (2),
.cycle 1 17 true (0),
.cycle 17 3 false (1),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.last 17 (5,true)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 19 1 false (3),
.cycle 20 7 false (0),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 34 1 false (6),
.cycle 28 1 false (2),
.cycle 8 7 true (1),
.cycle 9 6 true (1),
.last 16 (1,true),
.cycle 18 5 false (0),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 13 2 true (1),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 71 1 false (7),
.cycle 19 4 true (1),
.last 16 (1,true)
]),
.split 14 (1,true) (byMove [
.last 19 (5,true),
.cycle 29 4 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 4 false (0),
.cycle 15 4 false (-1),
.cycle 18 4 false (2),
.cycle 25 4 false (5),
.cycle 17 4 false (1),
.cycle 18 1 false (4),
.cycle 15 4 false (1),
.last 15 (5,true),
.cycle 20 4 false (0),
.cycle 15 4 false (0),
.cycle 20 4 false (2),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 4 false (-1),
.last 22 (5,true),
.cycle 1 16 true (0),
.cycle 15 4 false (1),
.cycle 26 4 false (2),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 8 5 true (2),
.split 14 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 0 20 true (0),
.cycle 22 7 false (1),
.cycle 15 6 false (1),
.cycle 61 1 false (7),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.last 15 (5,true),
.cycle 25 11 false (1),
.cycle 20 5 false (0),
.cycle 71 1 false (7),
.cycle 26 1 false (0),
.last 16 (5,true),
.cycle 15 6 false (1),
.cycle 6 24 true (2),
.cycle 1 15 true (1),
.cycle 11 4 true (2),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.last 15 (5,true)
])
])
theorem kid04_part242_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part242) = true := by rfl

def kid04_part243 : Audit := .cycle 0 12 true (0)
theorem kid04_part243_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part243) = true := by rfl

def kid04_part244 : Audit := .cycle 17 1 false (1)
theorem kid04_part244_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part244) = true := by rfl

def kid04_part245 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.split 16 (4,true) (byMove [
.cycle 23 1 false (1),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.cycle 19 1 false (3),
.last 17 (1,true),
.cycle 19 3 false (1),
.cycle 0 18 true (0),
.cycle 19 3 false (3),
.cycle 17 3 false (1),
.last 18 (1,true),
.cycle 16 3 false (0),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 17 3 false (-1),
.cycle 26 3 false (2),
.last 17 (1,true),
.cycle 26 3 false (2),
.cycle 0 18 true (0),
.cycle 12 7 true (0),
.cycle 18 3 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.cycle 9 3 true (2),
.split 13 (1,true) (byMove [
.cycle 34 1 false (6),
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 23 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 9 5 true (2),
.cycle 6 8 true (2),
.last 17 (4,true),
.last 22 (4,true),
.cycle 61 1 false (7),
.last 14 (4,true),
.cycle 23 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 8 6 true (2),
.last 15 (4,true)
]),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 19 1 false (3),
.cycle 22 7 false (0),
.cycle 16 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 34 1 false (6),
.cycle 28 1 false (2),
.cycle 8 7 true (2),
.cycle 9 6 true (2),
.last 16 (1,true),
.last 18 (1,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 20 5 false (0),
.cycle 16 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 71 1 false (7),
.cycle 8 7 true (2),
.last 18 (1,true)
]),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.split 16 (4,true) (byMove [
.cycle 23 1 false (1),
.cycle 9 17 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 3 false (0),
.cycle 17 3 false (-1),
.cycle 20 3 false (2),
.last 17 (1,true),
.cycle 19 3 false (1),
.cycle 21 3 false (3),
.cycle 21 3 false (5),
.cycle 17 3 false (1),
.last 18 (1,true),
.cycle 16 3 false (0),
.cycle 22 3 false (2),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 17 3 false (-1),
.cycle 12 8 true (0),
.last 17 (1,true),
.cycle 32 3 false (2),
.cycle 5 12 true (0),
.cycle 17 8 true (1),
.cycle 18 3 false (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.split 13 (4,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 17 true (0),
.cycle 32 1 false (2),
.cycle 25 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 19 5 false (1),
.cycle 30 17 true (4),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 8 7 true (2),
.cycle 11 3 true (3),
.last 15 (1,true),
.last 20 (1,true),
.last 44 (1,true),
.cycle 5 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 16 5 true (2),
.cycle 11 15 true (3),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 0 15 true (0),
.cycle 8 7 true (2),
.cycle 11 3 true (3)
])
])
theorem kid04_part245_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part245) = true := by rfl

def kid04_part247 : Audit := .split 16 (4,true) (byMove [
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 0 28 true (-1),
.cycle 19 1 false (-1),
.cycle 0 18 false (3),
.last 18 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 5, 32, 5, 64],[4, 64, 5, 1, 2, 12, 64],64⟩,
.cycle 31 1 false (1),
.cycle 23 1 false (1),
.cycle 8 15 true (-1),
.cycle 10 7 false (2),
.cycle 20 1 false (0),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 23 1 false (5),
.cycle 12 7 false (1),
.cycle 12 5 false (1),
.last 18 (1,true),
.cycle 53 1 false (3),
.cycle 54 1 false (2),
.cycle 4 13 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 32, 45, 64],[4, 64, 45, 1, 16, 12, 64],64⟩,
.cycle 25 1 false (3)
])
theorem kid04_part247_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part247) = true := by rfl

def kid04_part248 : Audit := .cycle 9 11 false (3)
theorem kid04_part248_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part248) = true := by rfl

def kid04_part249 : Audit := .cycle 14 1 false (0)
theorem kid04_part249_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part249) = true := by rfl

def kid04_part250 : Audit := .cycle 13 1 false (-1)
theorem kid04_part250_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part250) = true := by rfl

def kid04_part251 : Audit := .cycle 14 1 false (0)
theorem kid04_part251_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part251) = true := by rfl

def kid04_part252 : Audit := .cycle 13 1 false (-1)
theorem kid04_part252_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part252) = true := by rfl

def kid04_part253 : Audit := .cycle 16 1 false (2)
theorem kid04_part253_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part253) = true := by rfl

def kid04_part254 : Audit := .split 13 (1,true) (byMove [
.last 17 (4,true),
.cycle 28 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.cycle 24 1 false (6),
.cycle 16 1 false (2),
.cycle 17 1 false (5),
.last 14 (4,true),
.cycle 16 1 false (4),
.cycle 19 1 false (1),
.last 16 (4,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 30 1 false (6),
.cycle 14 1 false (0),
.cycle 30 1 false (4),
.cycle 1 15 true (0),
.last 15 (4,true),
.cycle 25 1 false (3),
.last 14 (4,true),
.cycle 14 3 true (2)
])
theorem kid04_part254_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part254) = true := by rfl

def kid04_part255 : Audit := .cycle 15 1 false (1)
theorem kid04_part255_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part255) = true := by rfl

def kid04_part256 : Audit := .cycle 17 1 false (3)
theorem kid04_part256_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part256) = true := by rfl

def kid04_part257 : Audit := .split 13 (4,true) (byMove [
.cycle 20 1 false (2),
.cycle 28 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.last 14 (1,true),
.cycle 16 1 false (2),
.cycle 17 1 false (5),
.cycle 17 1 false (5),
.cycle 16 1 false (4),
.last 15 (1,true),
.cycle 13 3 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 23 1 false (5),
.cycle 14 1 false (0),
.cycle 30 1 false (4),
.last 14 (1,true),
.cycle 0 18 true (0),
.cycle 25 1 false (3),
.cycle 14 6 true (2),
.cycle 14 3 true (2)
])
theorem kid04_part257_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part257) = true := by rfl

def kid04_part258 : Audit := .cycle 16 1 false (4)
theorem kid04_part258_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part258) = true := by rfl

def kid04_part259 : Audit := .split 14 (1,true) (byMove [
.cycle 21 1 false (3),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 25 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 6 9 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2, 32, 2, 128, 256, 8, 4, 32, 2, 4096],[4, 2, 2, 1, 4096, 2, 4, 2, 4096, 1, 4096, 2, 4096],4096⟩,
.cycle 10 7 false (2),
.cycle 9 11 false (3),
.last 15 (4,true),
.cycle 36 1 false (0),
.cycle 18 1 false (0),
.last 18 (4,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 24 1 false (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 128, 32, 128, 128, 256, 8, 4, 32, 128, 4096],[4, 128, 128, 1, 4096, 128, 4, 128, 4096, 1, 4096, 128, 4096],4096⟩,
.last 16 (4,true),
.cycle 26 1 false (0),
.last 15 (4,true),
.cycle 10 9 false (2)
])
theorem kid04_part259_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part259) = true := by rfl

def kid04_part260 : Audit := .split 15 (4,true) (byMove [
.last 28 (1,true),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 17 (1,true),
.cycle 33 1 false (5),
.cycle 21 1 false (3),
.cycle 16 1 false (0),
.cycle 32 1 false (4),
.cycle 16 1 false (0),
.last 17 (1,true),
.cycle 13 3 false (0),
.last 19 (1,true),
.cycle 16 1 false (-2),
.cycle 12 5 false (0),
.cycle 16 1 false (-2),
.last 17 (1,true),
.last 37 (1,true),
.cycle 9 13 false (3),
.cycle 21 1 false (1),
.last 35 (1,true),
.cycle 11 5 false (1)
])
theorem kid04_part260_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part260) = true := by rfl

def kid04_part261 : Audit := .cycle 18 1 false (2)
theorem kid04_part261_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part261) = true := by rfl

def kid04_part262 : Audit := .cycle 13 1 false (-1)
theorem kid04_part262_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part262) = true := by rfl

def kid04_part263 : Audit := .cycle 12 2 true (-1)
theorem kid04_part263_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part263) = true := by rfl

def kid04_part264 : Audit := .cycle 13 1 false (-1)
theorem kid04_part264_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part264) = true := by rfl

def kid04_part265 : Audit := .cycle 10 6 true (0)
theorem kid04_part265_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part265) = true := by rfl

def kid04_part266 : Audit := .split 13 (1,true) (byMove [
.cycle 19 1 false (5),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 0 21 true (0),
.last 14 (4,true),
.last 17 (4,true),
.cycle 6 8 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2, 32, 2, 128, 256, 8, 4, 32, 2, 4096],[4, 2, 2, 1, 4096, 128, 4, 2, 4096, 1, 4096, 128, 4096],4096⟩,
.cycle 10 6 true (0),
.cycle 26 1 false (2),
.last 14 (4,true),
.cycle 1 20 true (0),
.cycle 17 1 false (1),
.last 17 (4,true),
.cycle 16 1 false (0),
.cycle 18 1 false (2),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 10 28 true (0),
.cycle 1 15 true (0),
.last 15 (4,true),
.cycle 5 34 true (0),
.last 14 (4,true),
.cycle 14 3 true (2)
])
theorem kid04_part266_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part266) = true := by rfl

def kid04_part267 : Audit := .split 14 (4,true) (byMove [
.cycle 52 1 false (0),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 29 1 false (5),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.cycle 20 1 false (4),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 13 3 false (1),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 30 1 false (2),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 1 20 true (0),
.cycle 28 1 false (2),
.cycle 20 1 false (2),
.cycle 22 20 true (2),
.cycle 11 4 true (0)
])
theorem kid04_part267_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part267) = true := by rfl

def kid04_part268 : Audit := .cycle 5 8 true (0)
theorem kid04_part268_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part268) = true := by rfl

def kid04_part269 : Audit := .split 13 (4,true) (byMove [
.cycle 19 1 false (5),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 16 (1,true),
.cycle 16 1 false (0),
.cycle 18 8 true (2),
.cycle 6 8 true (0),
.last 14 (1,true),
.cycle 10 6 true (0),
.cycle 26 1 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 48, 1, 16, 16, 64],64⟩,
.cycle 16 6 true (2),
.cycle 17 1 false (1),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 18 1 false (2),
.cycle 12 4 true (-1),
.cycle 12 2 true (0),
.cycle 10 28 true (0),
.last 14 (1,true),
.cycle 0 18 true (0),
.cycle 5 34 true (0),
.cycle 14 6 true (2),
.cycle 14 3 true (2)
])
theorem kid04_part269_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part269) = true := by rfl

def kid04_part270 : Audit := .cycle 14 3 true (2)
theorem kid04_part270_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part270) = true := by rfl

def kid04_part246 : Audit := .split 12 (5,true) (byMove [(kid04_part247),(kid04_part248),(kid04_part249),(kid04_part250),(kid04_part251),(kid04_part252),(kid04_part253),(kid04_part254),(kid04_part255),(kid04_part256),(kid04_part257),(kid04_part258),(kid04_part259),(kid04_part260),(kid04_part261),(kid04_part262),(kid04_part263),(kid04_part264),(kid04_part265),(kid04_part266),(kid04_part267),(kid04_part268),(kid04_part269),(kid04_part270)])

theorem kid04_part246_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part246) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part247),(kid04_part248),(kid04_part249),(kid04_part250),(kid04_part251),(kid04_part252),(kid04_part253),(kid04_part254),(kid04_part255),(kid04_part256),(kid04_part257),(kid04_part258),(kid04_part259),(kid04_part260),(kid04_part261),(kid04_part262),(kid04_part263),(kid04_part264),(kid04_part265),(kid04_part266),(kid04_part267),(kid04_part268),(kid04_part269),(kid04_part270)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part247_checked

  · exact kid04_part253_checked

  · exact kid04_part259_checked

  · exact kid04_part265_checked

  · exact kid04_part248_checked

  · exact kid04_part254_checked

  · exact kid04_part260_checked

  · exact kid04_part266_checked

  · exact kid04_part249_checked

  · exact kid04_part255_checked

  · exact kid04_part261_checked

  · exact kid04_part267_checked

  · exact kid04_part250_checked

  · exact kid04_part256_checked

  · exact kid04_part262_checked

  · exact kid04_part268_checked

  · exact kid04_part251_checked

  · exact kid04_part257_checked

  · exact kid04_part263_checked

  · exact kid04_part269_checked

  · exact kid04_part252_checked

  · exact kid04_part258_checked

  · exact kid04_part264_checked

  · exact kid04_part270_checked

def kid04_part271 : Audit := .cycle 0 10 true (0)
theorem kid04_part271_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part271) = true := by rfl

def kid04_part272 : Audit := .cycle 1 9 true (1)
theorem kid04_part272_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part272) = true := by rfl

def kid04_part273 : Audit := .cycle 2 8 true (1)
theorem kid04_part273_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part273) = true := by rfl

def kid04_part274 : Audit := .cycle 0 31 true (0)
theorem kid04_part274_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part274) = true := by rfl

def kid04_part275 : Audit := .cycle 8 2 true (2)
theorem kid04_part275_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part275) = true := by rfl

def kid04_part276 : Audit := .cycle 9 1 true (3)
theorem kid04_part276_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part276) = true := by rfl

def kid04_part204 : Audit := .split 9 (5,false) (byMove [(kid04_part205),(kid04_part206),(kid04_part207),(kid04_part208),(kid04_part209),(kid04_part210),(kid04_part211),(kid04_part212),(kid04_part213),(kid04_part214),(kid04_part215),(kid04_part216),(kid04_part217),(kid04_part242),(kid04_part243),(kid04_part244),(kid04_part245),(kid04_part246),(kid04_part271),(kid04_part272),(kid04_part273),(kid04_part274),(kid04_part275),(kid04_part276)])

theorem kid04_part204_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (kid04_part204) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part205),(kid04_part206),(kid04_part207),(kid04_part208),(kid04_part209),(kid04_part210),(kid04_part211),(kid04_part212),(kid04_part213),(kid04_part214),(kid04_part215),(kid04_part216),(kid04_part217),(kid04_part242),(kid04_part243),(kid04_part244),(kid04_part245),(kid04_part246),(kid04_part271),(kid04_part272),(kid04_part273),(kid04_part274),(kid04_part275),(kid04_part276)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part205_checked

  · exact kid04_part211_checked

  · exact kid04_part217_checked

  · exact kid04_part271_checked

  · exact kid04_part206_checked

  · exact kid04_part212_checked

  · exact kid04_part242_checked

  · exact kid04_part272_checked

  · exact kid04_part207_checked

  · exact kid04_part213_checked

  · exact kid04_part243_checked

  · exact kid04_part273_checked

  · exact kid04_part208_checked

  · exact kid04_part214_checked

  · exact kid04_part244_checked

  · exact kid04_part274_checked

  · exact kid04_part209_checked

  · exact kid04_part215_checked

  · exact kid04_part245_checked

  · exact kid04_part275_checked

  · exact kid04_part210_checked

  · exact kid04_part216_checked

  · exact kid04_part246_checked

  · exact kid04_part276_checked

def kid04_part278 : Audit := .cycle 24 1 false (2)
theorem kid04_part278_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part278) = true := by rfl

def kid04_part279 : Audit := .cycle 11 11 false (1)
theorem kid04_part279_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part279) = true := by rfl

def kid04_part280 : Audit := .split 12 (4,true) (byMove [
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
.cycle 14 4 false (-1),
.cycle 11 4 false (1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 1 13 false (3),
.cycle 19 4 false (1),
.cycle 18 1 false (2),
.cycle 16 4 false (0),
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
.cycle 14 4 false (1),
.cycle 11 4 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 4 false (3),
.cycle 18 1 false (4),
.cycle 16 4 false (2),
.cycle 13 1 true (1)
]),
.cycle 13 4 false (0),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.split 13 (5,false) (byMove [
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (2),
.cycle 16 1 false (0),
.cycle 14 4 false (0),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 14 4 false (-1),
.cycle 11 4 false (1),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 21 4 false (1),
.cycle 14 4 false (0),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 17 1 false (3),
.cycle 15 4 false (1),
.split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 16 1 false (0),
.cycle 14 4 false (0),
.cycle 0 15 true (0),
.cycle 12 2 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 27 4 false (1),
.cycle 20 4 false (2),
.cycle 18 4 false (2),
.cycle 8 6 true (0),
.cycle 13 1 true (1),
.cycle 15 4 false (1),
.cycle 16 1 false (0),
.cycle 14 4 false (0),
.cycle 17 1 false (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 24 4 false (2),
.cycle 19 4 false (1),
.cycle 13 1 true (1)
])
])
theorem kid04_part280_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part280) = true := by rfl

def kid04_part281 : Audit := .cycle 0 12 true (0)
theorem kid04_part281_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part281) = true := by rfl

def kid04_part282 : Audit := .split 11 (4,true) (byMove [
.cycle 14 1 false (2),
.cycle 13 11 false (-1),
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
.cycle 17 1 false (3),
.last 20 (5,false),
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
.cycle 17 1 false (3),
.cycle 16 5 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 5 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 6 8 true (1),
.cycle 12 1 true (2)
]),
.cycle 15 3 false (0),
.cycle 16 3 false (-2),
.cycle 11 11 false (1),
.cycle 15 1 false (3),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 15 1 false (3),
.last 18 (5,false),
.last 18 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.cycle 17 1 false (3),
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
.cycle 34 1 false (6),
.cycle 15 7 false (1),
.split 12 (5,false) (byMove [
.cycle 28 1 false (2),
.cycle 13 6 false (1),
.cycle 14 6 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.cycle 13 6 false (1),
.cycle 14 6 false (1),
.cycle 34 1 false (6),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 11 false (2),
.cycle 12 1 true (2)
])
])
theorem kid04_part282_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part282) = true := by rfl

def kid04_part284 : Audit := .cycle 14 1 false (2)
theorem kid04_part284_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part284) = true := by rfl

def kid04_part285 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 14 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 11 false (-2),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 11 false (0),
.cycle 13 1 true (-1),
.cycle 14 11 false (-1),
.last 16 (4,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 11 false (-2),
.cycle 13 1 false (-1),
.cycle 26 11 false (0),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 18 1 false (2),
.cycle 15 11 false (0),
.cycle 13 1 true (-1)
])
theorem kid04_part285_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part285) = true := by rfl

def kid04_part286 : Audit := .cycle 18 1 false (-2)
theorem kid04_part286_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part286) = true := by rfl

def kid04_part287 : Audit := .cycle 0 13 true (0)
theorem kid04_part287_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part287) = true := by rfl

def kid04_part288 : Audit := .split 12 (4,true) (byMove [
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
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 4 false (1),
.cycle 17 1 false (3),
.cycle 16 4 false (0),
.last 13 (5,false)
])
theorem kid04_part288_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part288) = true := by rfl

def kid04_part289 : Audit := .split 13 (5,false) (byMove [
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
.cycle 12 4 false (0),
.last 16 (4,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 11 15 false (3),
.cycle 1 13 false (3),
.cycle 12 11 false (1),
.cycle 18 1 false (2),
.cycle 12 8 false (0),
.cycle 13 1 true (-1)
])
theorem kid04_part289_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part289) = true := by rfl

def kid04_part290 : Audit := .cycle 0 12 true (0)
theorem kid04_part290_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part290) = true := by rfl

def kid04_part291 : Audit := .cycle 1 11 true (1)
theorem kid04_part291_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part291) = true := by rfl

def kid04_part292 : Audit := .cycle 24 1 false (2)
theorem kid04_part292_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part292) = true := by rfl

def kid04_part293 : Audit := .cycle 21 1 false (1)
theorem kid04_part293_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part293) = true := by rfl

def kid04_part294 : Audit := .cycle 8 4 true (1)
theorem kid04_part294_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part294) = true := by rfl

def kid04_part295 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 5 false (0),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 5 false (0),
.cycle 17 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 6 8 true (1),
.cycle 12 1 true (2)
])
theorem kid04_part295_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part295) = true := by rfl

def kid04_part296 : Audit := .cycle 15 3 false (0)
theorem kid04_part296_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part296) = true := by rfl

def kid04_part297 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.last 27 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 16 (4,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 20 (4,true),
.last 18 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 21 (4,true),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.last 16 (4,true),
.cycle 0 16 true (-1),
.last 24 (4,true),
.last 23 (4,true),
.last 20 (4,true)
])
theorem kid04_part297_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part297) = true := by rfl

def kid04_part298 : Audit := .split 22 (4,true) (byMove [
.cycle 25 1 false (1),
.last 24 (5,false),
.cycle 0 30 false (3),
.cycle 0 24 true (-3),
.cycle 0 30 false (3),
.cycle 0 26 true (-3),
.cycle 40 28 true (-3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 397, 397, 4096, 128, 256, 8, 4, 397, 4096, 4096],[4, 4096, 397, 1, 2, 1, 4, 397, 256, 1, 2, 397, 4096],6176⟩,
.cycle 12 17 true (-3),
.cycle 0 34 true (-3),
.cycle 8 15 false (2),
.last 23 (5,false),
.cycle 0 31 false (3),
.last 24 (5,false),
.cycle 12 11 false (1),
.cycle 26 1 false (2),
.cycle 0 40 true (-4),
.cycle 28 1 false (2),
.cycle 9 33 false (4),
.cycle 20 16 true (-1),
.cycle 2 21 false (3),
.cycle 4 40 true (-3),
.cycle 0 35 false (3),
.last 23 (5,false)
])
theorem kid04_part298_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part298) = true := by rfl

def kid04_part299 : Audit := .cycle 15 1 false (3)
theorem kid04_part299_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part299) = true := by rfl

def kid04_part300 : Audit := .split 12 (4,true) (byMove [
.cycle 19 1 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 15 1 false (3),
.last 14 (5,false),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 14 4 false (2),
.cycle 13 4 false (1),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 21 4 false (1),
.cycle 13 4 false (1),
.cycle 21 4 false (1),
.cycle 0 14 true (0),
.cycle 20 4 false (0),
.cycle 11 2 true (0)
])
theorem kid04_part300_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part300) = true := by rfl

def kid04_part301 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.last 38 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 23 1 false (1),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 12 4 false (0),
.last 16 (4,true),
.cycle 27 1 false (1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 17 13 false (0),
.cycle 12 3 false (0),
.last 15 (4,true),
.last 33 (4,true),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part301_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part301) = true := by rfl

def kid04_part302 : Audit := .cycle 0 12 true (0)
theorem kid04_part302_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part302) = true := by rfl

def kid04_part303 : Audit := .cycle 1 11 true (1)
theorem kid04_part303_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part303) = true := by rfl

def kid04_part304 : Audit := .cycle 2 10 true (1)
theorem kid04_part304_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part304) = true := by rfl

def kid04_part305 : Audit := .cycle 34 1 false (6)
theorem kid04_part305_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part305) = true := by rfl

def kid04_part306 : Audit := .cycle 15 7 false (1)
theorem kid04_part306_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part306) = true := by rfl

def kid04_part307 : Audit := .split 12 (5,false) (byMove [
.cycle 28 1 false (2),
.cycle 13 14 false (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 34 1 false (6),
.last 13 (4,true),
.cycle 11 3 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 11 false (2),
.cycle 12 1 true (2)
])
theorem kid04_part307_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part307) = true := by rfl

def kid04_part283 : Audit := .split 11 (5,true) (byMove [(kid04_part284),(kid04_part285),(kid04_part286),(kid04_part287),(kid04_part288),(kid04_part289),(kid04_part290),(kid04_part291),(kid04_part292),(kid04_part293),(kid04_part294),(kid04_part295),(kid04_part296),(kid04_part297),(kid04_part298),(kid04_part299),(kid04_part300),(kid04_part301),(kid04_part302),(kid04_part303),(kid04_part304),(kid04_part305),(kid04_part306),(kid04_part307)])

theorem kid04_part283_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part283) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part284),(kid04_part285),(kid04_part286),(kid04_part287),(kid04_part288),(kid04_part289),(kid04_part290),(kid04_part291),(kid04_part292),(kid04_part293),(kid04_part294),(kid04_part295),(kid04_part296),(kid04_part297),(kid04_part298),(kid04_part299),(kid04_part300),(kid04_part301),(kid04_part302),(kid04_part303),(kid04_part304),(kid04_part305),(kid04_part306),(kid04_part307)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part284_checked

  · exact kid04_part290_checked

  · exact kid04_part296_checked

  · exact kid04_part302_checked

  · exact kid04_part285_checked

  · exact kid04_part291_checked

  · exact kid04_part297_checked

  · exact kid04_part303_checked

  · exact kid04_part286_checked

  · exact kid04_part292_checked

  · exact kid04_part298_checked

  · exact kid04_part304_checked

  · exact kid04_part287_checked

  · exact kid04_part293_checked

  · exact kid04_part299_checked

  · exact kid04_part305_checked

  · exact kid04_part288_checked

  · exact kid04_part294_checked

  · exact kid04_part300_checked

  · exact kid04_part306_checked

  · exact kid04_part289_checked

  · exact kid04_part295_checked

  · exact kid04_part301_checked

  · exact kid04_part307_checked

def kid04_part308 : Audit := .cycle 0 11 true (0)
theorem kid04_part308_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part308) = true := by rfl

def kid04_part309 : Audit := .cycle 1 10 true (1)
theorem kid04_part309_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part309) = true := by rfl

def kid04_part310 : Audit := .cycle 0 23 true (0)
theorem kid04_part310_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part310) = true := by rfl

def kid04_part311 : Audit := .cycle 3 8 true (1)
theorem kid04_part311_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part311) = true := by rfl

def kid04_part312 : Audit := .cycle 8 3 true (1)
theorem kid04_part312_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part312) = true := by rfl

def kid04_part313 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.cycle 15 7 false (1),
.split 13 (5,true) (byMove [
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 17 1 false (1),
.cycle 17 5 false (1),
.last 18 (4,true),
.last 26 (4,true),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 17 9 false (1),
.cycle 12 2 true (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 22 true (1),
.cycle 0 23 true (0),
.cycle 8 4 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (1),
.split 14 (4,true) (byMove [
.cycle 32 1 false (2),
.cycle 15 19 false (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 15 8 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 11 4 true (2),
.cycle 18 9 false (1),
.last 16 (5,true),
.cycle 19 8 false (3),
.cycle 38 1 false (6),
.last 20 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.cycle 18 13 false (2),
.last 17 (5,true)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 7 false (1),
.split 13 (5,true) (byMove [
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 22 1 false (4),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.cycle 1 15 true (1),
.cycle 17 7 false (1),
.cycle 61 1 false (7),
.last 14 (4,true),
.cycle 25 1 false (5),
.cycle 45 22 false (0),
.last 18 (4,true),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 17 11 false (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 5 34 true (1),
.last 14 (4,true),
.cycle 14 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 5 23 true (1),
.cycle 6 7 true (1),
.cycle 11 1 true (3)
])
theorem kid04_part313_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part313) = true := by rfl

def kid04_part314 : Audit := .cycle 14 5 false (1)
theorem kid04_part314_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part314) = true := by rfl

def kid04_part315 : Audit := .split 15 (4,true) (byMove [
.cycle 482 256 false (-2),
.cycle 11 14 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 15 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 11 8 false (1),
.cycle 16 1 false (-2),
.last 21 (5,true),
.last 60 (5,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 8 false (1),
.last 19 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.last 23 (5,true),
.cycle 17 1 false (-3),
.cycle 11 8 false (1),
.cycle 16 1 false (-2),
.last 21 (5,true),
.last 111 (5,true),
.cycle 11 14 false (1),
.cycle 24 1 false (4),
.cycle 11 11 false (1),
.last 19 (5,true)
]),
.cycle 11 6 true (-1),
.cycle 16 17 true (0),
.cycle 20 1 false (4),
.cycle 16 1 false (0),
.cycle 11 7 false (1),
.split 16 (5,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 12, 64],[4, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 0 64 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 8 false (1),
.cycle 16 1 false (0),
.cycle 29 1 false (3),
.cycle 17 20 true (0),
.cycle 11 9 false (1),
.cycle 20 1 false (4),
.last 18 (5,true),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 true (-1),
.cycle 33 1 false (3),
.cycle 17 1 false (-1),
.cycle 11 8 false (1),
.cycle 16 1 false (0),
.cycle 0 49 true (-2),
.cycle 11 6 true (-1),
.cycle 17 17 true (0),
.cycle 11 26 true (-1),
.last 18 (5,true),
.last 17 (5,true)
]),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 8 true (-2),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.split 16 (5,false) (byMove [
.last 21 (5,true),
.last 39 (5,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 11 8 false (1),
.cycle 16 1 false (-2),
.cycle 22 1 false (4),
.cycle 12 5 false (0),
.cycle 11 9 false (1),
.cycle 11 8 true (-2),
.cycle 15 2 true (-2),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 24 1 false (4),
.cycle 17 1 false (-3),
.cycle 11 8 false (1),
.cycle 16 1 false (-2),
.last 113 (5,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.last 24 (5,true),
.last 18 (5,true),
.last 17 (5,true)
]),
.cycle 9 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 15, 15, 1, 2, 64, 64],96⟩,
.cycle 0 56 true (-2),
.cycle 11 11 false (1),
.cycle 11 10 false (1),
.split 16 (5,false) (byMove [
.cycle 22 1 false (4),
.cycle 12 5 false (0),
.cycle 11 9 false (1),
.cycle 11 8 true (-1),
.cycle 15 2 true (-1),
.last 17 (5,true),
.cycle 6 11 false (3),
.cycle 17 20 true (0),
.cycle 11 12 false (1),
.cycle 0 56 true (-2),
.last 18 (5,true),
.last 17 (5,true),
.cycle 11 10 false (1),
.cycle 12 5 false (0),
.cycle 11 9 false (1),
.cycle 11 11 false (1),
.last 18 (5,true),
.last 17 (5,true),
.cycle 3 33 false (3),
.cycle 10 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 4, 64],[4, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 124 13 false (0),
.last 18 (5,true),
.last 17 (5,true)
])
])
theorem kid04_part315_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part315) = true := by rfl

def kid04_part316 : Audit := .split 12 (4,true) (byMove [
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
.last 18 (5,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.last 16 (5,true),
.cycle 14 4 false (-1),
.cycle 11 4 false (1),
.last 20 (5,true),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.last 18 (5,true),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 0 19 true (-1),
.cycle 16 4 false (0),
.last 16 (5,true)
]),
.cycle 13 4 false (2),
.cycle 22 4 false (4),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.split 13 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 16 1 false (4),
.cycle 0 17 true (0),
.cycle 14 4 false (2),
.cycle 0 15 true (0),
.cycle 16 4 false (4),
.last 14 (5,true),
.cycle 14 4 false (1),
.cycle 11 4 true (0),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 14 4 false (0),
.cycle 13 1 false (1),
.cycle 21 4 false (3),
.cycle 14 4 false (2),
.cycle 22 4 false (4),
.cycle 0 15 true (0),
.cycle 6 11 true (0),
.last 14 (5,true)
]),
.cycle 13 4 false (0),
.cycle 11 3 false (1),
.cycle 15 4 false (2),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.split 13 (5,false) (byMove [
.last 18 (5,true),
.cycle 7 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 17 4 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (2),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 14 4 false (-1),
.cycle 11 4 false (1),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.cycle 14 4 false (-2),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 14 4 false (0),
.cycle 11 3 false (1),
.cycle 20 4 false (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 9 4 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.cycle 15 4 false (1),
.split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 17 4 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (2),
.cycle 12 2 true (0),
.last 14 (5,true),
.cycle 22 4 false (2),
.cycle 0 17 true (0),
.cycle 17 4 false (1),
.cycle 0 15 true (0),
.cycle 8 8 true (0),
.last 14 (5,true),
.cycle 15 4 false (1),
.cycle 18 4 false (2),
.cycle 14 4 false (0),
.cycle 16 4 false (2),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 31 true (0),
.cycle 10 4 true (0),
.cycle 2 15 true (0),
.cycle 0 15 true (0),
.cycle 27 4 false (1),
.last 14 (5,true)
])
])
theorem kid04_part316_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part316) = true := by rfl

def kid04_part317 : Audit := .cycle 30 1 false (6)
theorem kid04_part317_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part317) = true := by rfl

def kid04_part318 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 23 true (-3),
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
.cycle 9 4 true (0),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.last 21 (5,false),
.last 20 (5,false),
.last 13 (5,false)
]),
.cycle 30 1 false (6),
.cycle 16 5 false (0),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.cycle 8 5 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 9 4 true (1),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 6 8 true (1),
.last 13 (5,false)
]),
.cycle 15 3 false (0),
.cycle 16 3 false (-2),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.last 30 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.cycle 16 1 false (4),
.last 14 (5,false),
.last 15 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 22 (5,false),
.last 15 (5,false),
.last 15 (5,false),
.last 27 (5,false),
.cycle 11 2 true (0),
.last 15 (5,false)
]),
.cycle 0 27 true (0),
.cycle 10 2 true (1),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 16 11 false (2),
.split 12 (5,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 6 false (1),
.last 15 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 16 7 false (1),
.cycle 13 6 false (1),
.last 15 (5,false),
.cycle 34 1 false (6),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 11 false (2),
.last 13 (5,false)
])
])
theorem kid04_part318_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part318) = true := by rfl

def kid04_part320 : Audit := .cycle 0 15 true (0)
theorem kid04_part320_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part320) = true := by rfl

def kid04_part321 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 0 23 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 56 (4,true),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 12 2 true (-1),
.last 25 (4,true),
.cycle 0 21 true (-1),
.last 14 (4,true),
.cycle 0 35 true (-2),
.cycle 0 23 true (-3),
.last 16 (4,true),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.last 33 (4,true),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 0 25 true (-2),
.last 15 (4,true),
.cycle 0 21 true (-1),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part321_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part321) = true := by rfl

def kid04_part322 : Audit := .cycle 18 1 false (-2)
theorem kid04_part322_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part322) = true := by rfl

def kid04_part323 : Audit := .cycle 16 1 false (0)
theorem kid04_part323_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part323) = true := by rfl

def kid04_part324 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 13 4 false (2),
.cycle 23 4 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.last 13 (5,false),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 15 4 false (2),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 9 4 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 4 false (1),
.cycle 16 4 false (0),
.last 13 (5,false)
])
theorem kid04_part324_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part324) = true := by rfl

def kid04_part325 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.last 17 (4,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 12 5 false (0),
.cycle 17 1 true (1),
.cycle 12 4 false (0),
.last 16 (4,true),
.last 19 (4,true),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.last 17 (4,true),
.cycle 0 17 true (-1),
.cycle 0 33 true (-2),
.cycle 0 19 true (-1),
.cycle 12 8 false (0),
.cycle 20 1 true (-2)
])
theorem kid04_part325_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part325) = true := by rfl

def kid04_part326 : Audit := .cycle 30 1 false (6)
theorem kid04_part326_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part326) = true := by rfl

def kid04_part327 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 27 true (-2),
.cycle 22 1 false (-2),
.cycle 20 1 false (0),
.last 14 (4,true),
.last 17 (4,true),
.cycle 34 1 false (6),
.cycle 12 2 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 14 true (1),
.cycle 17 5 false (0),
.last 18 (4,true),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 31 true (0),
.cycle 10 4 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 14 true (1)
])
theorem kid04_part327_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part327) = true := by rfl

def kid04_part328 : Audit := .cycle 15 5 false (1)
theorem kid04_part328_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part328) = true := by rfl

def kid04_part329 : Audit := .cycle 0 13 true (0)
theorem kid04_part329_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part329) = true := by rfl

def kid04_part330 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 9 4 true (1),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 6 8 true (1),
.last 13 (5,false)
])
theorem kid04_part330_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part330) = true := by rfl

def kid04_part331 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (7),
.cycle 30 1 false (6),
.cycle 8 6 true (1),
.cycle 13 1 true (3),
.cycle 9 5 true (1),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 11 7 true (1),
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 43 true (0),
.cycle 6 9 true (1),
.cycle 13 1 true (3)
])
theorem kid04_part331_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part331) = true := by rfl

def kid04_part332 : Audit := .cycle 15 3 false (0)
theorem kid04_part332_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part332) = true := by rfl

def kid04_part333 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.last 25 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 13 1 false (-1),
.last 22 (4,true),
.cycle 12 2 true (-1),
.last 21 (4,true),
.last 23 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 24 (4,true),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 13 1 false (-1),
.last 25 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part333_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part333) = true := by rfl

def kid04_part334 : Audit := .cycle 24 1 false (4)
theorem kid04_part334_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part334) = true := by rfl

def kid04_part335 : Audit := .cycle 19 1 false (-1)
theorem kid04_part335_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part335) = true := by rfl

def kid04_part336 : Audit := .split 12 (4,true) (byMove [
.cycle 19 1 false (1),
.cycle 26 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 15 4 false (1),
.last 14 (5,false),
.cycle 14 4 false (0),
.cycle 16 1 false (4),
.cycle 15 4 false (3),
.cycle 13 4 false (1),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 17 4 false (1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 18 4 false (0),
.cycle 13 4 false (1),
.cycle 0 17 true (0),
.cycle 23 4 false (1),
.cycle 24 4 false (0),
.cycle 11 2 true (0)
])
theorem kid04_part336_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part336) = true := by rfl

def kid04_part337 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 75 31 true (-5),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 12 7 false (1),
.cycle 13 2 true (-1),
.cycle 12 6 false (0),
.cycle 25 1 false (3),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 12 4 false (0),
.last 16 (4,true),
.cycle 12 9 false (1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 13 1 false (-1),
.cycle 12 10 false (1),
.cycle 12 3 false (0),
.last 15 (4,true),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid04_part337_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part337) = true := by rfl

def kid04_part338 : Audit := .cycle 0 27 true (0)
theorem kid04_part338_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part338) = true := by rfl

def kid04_part339 : Audit := .cycle 10 2 true (1)
theorem kid04_part339_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part339) = true := by rfl

def kid04_part340 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.last 15 (5,false),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 27 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.last 14 (5,false),
.cycle 17 5 false (0),
.last 15 (5,false),
.cycle 12 13 false (2),
.cycle 17 1 false (3),
.cycle 14 6 false (0),
.last 17 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 17 9 false (1),
.last 14 (5,false)
])
theorem kid04_part340_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part340) = true := by rfl

def kid04_part341 : Audit := .cycle 0 13 true (0)
theorem kid04_part341_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part341) = true := by rfl

def kid04_part342 : Audit := .split 12 (4,true) (byMove [
.cycle 28 1 false (2),
.last 17 (5,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 13 6 false (1),
.cycle 17 9 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.last 13 (5,false),
.cycle 16 7 false (1),
.last 17 (5,false),
.cycle 17 6 false (2),
.cycle 34 1 false (6),
.cycle 13 6 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 11 false (2),
.last 13 (5,false)
])
theorem kid04_part342_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part342) = true := by rfl

def kid04_part343 : Audit := .split 13 (5,false) (byMove [
.cycle 0 31 true (0),
.cycle 10 4 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 30 29 false (4),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 13 1 true (3),
.cycle 17 11 false (2),
.cycle 11 5 true (1),
.last 15 (4,true),
.cycle 5 34 true (1),
.last 14 (4,true),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 17 15 false (3),
.cycle 13 1 true (3)
])
theorem kid04_part343_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part343) = true := by rfl

def kid04_part319 : Audit := .split 11 (5,true) (byMove [(kid04_part320),(kid04_part321),(kid04_part322),(kid04_part323),(kid04_part324),(kid04_part325),(kid04_part326),(kid04_part327),(kid04_part328),(kid04_part329),(kid04_part330),(kid04_part331),(kid04_part332),(kid04_part333),(kid04_part334),(kid04_part335),(kid04_part336),(kid04_part337),(kid04_part338),(kid04_part339),(kid04_part340),(kid04_part341),(kid04_part342),(kid04_part343)])

theorem kid04_part319_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part319) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part320),(kid04_part321),(kid04_part322),(kid04_part323),(kid04_part324),(kid04_part325),(kid04_part326),(kid04_part327),(kid04_part328),(kid04_part329),(kid04_part330),(kid04_part331),(kid04_part332),(kid04_part333),(kid04_part334),(kid04_part335),(kid04_part336),(kid04_part337),(kid04_part338),(kid04_part339),(kid04_part340),(kid04_part341),(kid04_part342),(kid04_part343)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part320_checked

  · exact kid04_part326_checked

  · exact kid04_part332_checked

  · exact kid04_part338_checked

  · exact kid04_part321_checked

  · exact kid04_part327_checked

  · exact kid04_part333_checked

  · exact kid04_part339_checked

  · exact kid04_part322_checked

  · exact kid04_part328_checked

  · exact kid04_part334_checked

  · exact kid04_part340_checked

  · exact kid04_part323_checked

  · exact kid04_part329_checked

  · exact kid04_part335_checked

  · exact kid04_part341_checked

  · exact kid04_part324_checked

  · exact kid04_part330_checked

  · exact kid04_part336_checked

  · exact kid04_part342_checked

  · exact kid04_part325_checked

  · exact kid04_part331_checked

  · exact kid04_part337_checked

  · exact kid04_part343_checked

def kid04_part344 : Audit := .cycle 0 11 true (0)
theorem kid04_part344_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part344) = true := by rfl

def kid04_part345 : Audit := .cycle 1 10 true (1)
theorem kid04_part345_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part345) = true := by rfl

def kid04_part346 : Audit := .cycle 2 9 true (1)
theorem kid04_part346_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part346) = true := by rfl

def kid04_part347 : Audit := .cycle 4 28 true (1)
theorem kid04_part347_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part347) = true := by rfl

def kid04_part348 : Audit := .cycle 14 9 false (2)
theorem kid04_part348_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part348) = true := by rfl

def kid04_part350 : Audit := .cycle 0 27 true (0)
theorem kid04_part350_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part350) = true := by rfl

def kid04_part351 : Audit := .cycle 10 2 true (2)
theorem kid04_part351_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part351) = true := by rfl

def kid04_part352 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.cycle 16 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 29 1 false (1),
.cycle 17 5 false (1),
.last 15 (5,true),
.cycle 12 13 false (2),
.cycle 17 1 false (3),
.last 18 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 17 9 false (1),
.cycle 14 8 false (2)
])
theorem kid04_part352_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part352) = true := by rfl

def kid04_part353 : Audit := .cycle 0 13 true (0)
theorem kid04_part353_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part353) = true := by rfl

def kid04_part354 : Audit := .split 12 (4,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 15 false (2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 17 9 false (1),
.cycle 16 7 false (1),
.last 14 (5,true),
.cycle 17 6 false (3),
.cycle 34 1 false (6),
.last 18 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 11 false (2),
.cycle 11 2 true (2)
])
theorem kid04_part354_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part354) = true := by rfl

def kid04_part355 : Audit := .split 12 (5,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 15 false (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 19 1 false (1),
.cycle 16 7 false (1),
.cycle 12 2 true (1),
.last 14 (4,true),
.cycle 34 1 false (6),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 11 false (2),
.cycle 11 2 true (2)
])
theorem kid04_part355_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part355) = true := by rfl

def kid04_part356 : Audit := .cycle 0 12 true (0)
theorem kid04_part356_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part356) = true := by rfl

def kid04_part357 : Audit := .cycle 1 11 true (1)
theorem kid04_part357_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part357) = true := by rfl

def kid04_part358 : Audit := .cycle 26 25 false (4)
theorem kid04_part358_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part358) = true := by rfl

def kid04_part359 : Audit := .cycle 3 9 true (1)
theorem kid04_part359_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part359) = true := by rfl

def kid04_part360 : Audit := .cycle 8 4 true (1)
theorem kid04_part360_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part360) = true := by rfl

def kid04_part361 : Audit := .cycle 11 1 true (3)
theorem kid04_part361_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part361) = true := by rfl

def kid04_part362 : Audit := .cycle 15 9 false (2)
theorem kid04_part362_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part362) = true := by rfl

def kid04_part363 : Audit := .split 13 (5,true) (byMove [
.cycle 0 31 true (0),
.cycle 10 4 true (2),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 20 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 30 29 false (4),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.last 17 (4,true),
.cycle 17 11 false (2),
.cycle 12 2 true (2),
.last 15 (4,true),
.cycle 5 34 true (1),
.last 14 (4,true),
.last 20 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 17 15 false (3),
.cycle 11 3 true (2)
])
theorem kid04_part363_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part363) = true := by rfl

def kid04_part364 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.cycle 16 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 20 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 9 5 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 17 (5,true),
.cycle 71 1 false (7),
.cycle 17 5 false (1),
.last 15 (5,true),
.last 25 (5,true),
.cycle 0 18 true (0),
.last 18 (5,true),
.last 14 (5,true),
.cycle 9 5 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 9 false (1),
.cycle 14 8 false (2)
])
theorem kid04_part364_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part364) = true := by rfl

def kid04_part365 : Audit := .cycle 5 28 true (1)
theorem kid04_part365_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part365) = true := by rfl

def kid04_part366 : Audit := .split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 5, 2048, 262144, 128, 256, 32768, 4, 33165, 5, 128, 256, 8, 5, 2048, 2189, 262144],[4, 2048, 5, 1, 32768, 262144, 16384, 2048, 141, 4096, 5, 262144, 4, 2048, 33165, 1, 32768, 262144, 262144],262176⟩,
.cycle 16 1 false (0),
.cycle 9 5 true (1),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 6 28 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 8 6 true (1),
.last 13 (5,true),
.cycle 16 7 false (1),
.last 14 (5,true),
.last 19 (5,true),
.cycle 5 8 true (1),
.last 18 (5,true),
.last 13 (5,true),
.cycle 29 29 false (4),
.cycle 10 3 true (2),
.cycle 2 13 true (1),
.cycle 0 14 true (0),
.cycle 17 15 false (3),
.last 13 (5,true)
])
theorem kid04_part366_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part366) = true := by rfl

def kid04_part367 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 5, 2048, 5, 128, 256, 32768, 4, 33165, 5, 128, 256, 8, 5, 2048, 5, 262144],[4, 2048, 5, 1, 262144, 32768, 16384, 2048, 262144, 4096, 262144, 5, 4, 2048, 33165, 1, 262144, 32768, 262144],262144⟩,
.last 14 (4,true),
.cycle 9 5 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 6 28 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 32 1 false (6),
.cycle 16 7 false (1),
.cycle 12 2 true (1),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 29 29 false (4),
.cycle 10 3 true (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (2)
])
theorem kid04_part367_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part367) = true := by rfl

def kid04_part368 : Audit := .cycle 0 12 true (0)
theorem kid04_part368_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part368) = true := by rfl

def kid04_part369 : Audit := .cycle 1 11 true (1)
theorem kid04_part369_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part369) = true := by rfl

def kid04_part370 : Audit := .cycle 2 10 true (1)
theorem kid04_part370_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part370) = true := by rfl

def kid04_part371 : Audit := .cycle 13 14 true (2)
theorem kid04_part371_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part371) = true := by rfl

def kid04_part372 : Audit := .cycle 15 13 false (3)
theorem kid04_part372_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part372) = true := by rfl

def kid04_part373 : Audit := .cycle 11 1 true (3)
theorem kid04_part373_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part373) = true := by rfl

def kid04_part349 : Audit := .split 11 (5,false) (byMove [(kid04_part350),(kid04_part351),(kid04_part352),(kid04_part353),(kid04_part354),(kid04_part355),(kid04_part356),(kid04_part357),(kid04_part358),(kid04_part359),(kid04_part360),(kid04_part361),(kid04_part362),(kid04_part363),(kid04_part364),(kid04_part365),(kid04_part366),(kid04_part367),(kid04_part368),(kid04_part369),(kid04_part370),(kid04_part371),(kid04_part372),(kid04_part373)])

theorem kid04_part349_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part349) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part350),(kid04_part351),(kid04_part352),(kid04_part353),(kid04_part354),(kid04_part355),(kid04_part356),(kid04_part357),(kid04_part358),(kid04_part359),(kid04_part360),(kid04_part361),(kid04_part362),(kid04_part363),(kid04_part364),(kid04_part365),(kid04_part366),(kid04_part367),(kid04_part368),(kid04_part369),(kid04_part370),(kid04_part371),(kid04_part372),(kid04_part373)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part350_checked

  · exact kid04_part356_checked

  · exact kid04_part362_checked

  · exact kid04_part368_checked

  · exact kid04_part351_checked

  · exact kid04_part357_checked

  · exact kid04_part363_checked

  · exact kid04_part369_checked

  · exact kid04_part352_checked

  · exact kid04_part358_checked

  · exact kid04_part364_checked

  · exact kid04_part370_checked

  · exact kid04_part353_checked

  · exact kid04_part359_checked

  · exact kid04_part365_checked

  · exact kid04_part371_checked

  · exact kid04_part354_checked

  · exact kid04_part360_checked

  · exact kid04_part366_checked

  · exact kid04_part372_checked

  · exact kid04_part355_checked

  · exact kid04_part361_checked

  · exact kid04_part367_checked

  · exact kid04_part373_checked

def kid04_part277 : Audit := .split 10 (1,true) (byMove [(kid04_part278),(kid04_part279),(kid04_part280),(kid04_part281),(kid04_part282),(kid04_part283),(kid04_part308),(kid04_part309),(kid04_part310),(kid04_part311),(kid04_part312),(kid04_part313),(kid04_part314),(kid04_part315),(kid04_part316),(kid04_part317),(kid04_part318),(kid04_part319),(kid04_part344),(kid04_part345),(kid04_part346),(kid04_part347),(kid04_part348),(kid04_part349)])

theorem kid04_part277_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (kid04_part277) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part278),(kid04_part279),(kid04_part280),(kid04_part281),(kid04_part282),(kid04_part283),(kid04_part308),(kid04_part309),(kid04_part310),(kid04_part311),(kid04_part312),(kid04_part313),(kid04_part314),(kid04_part315),(kid04_part316),(kid04_part317),(kid04_part318),(kid04_part319),(kid04_part344),(kid04_part345),(kid04_part346),(kid04_part347),(kid04_part348),(kid04_part349)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part278_checked

  · exact kid04_part308_checked

  · exact kid04_part314_checked

  · exact kid04_part344_checked

  · exact kid04_part279_checked

  · exact kid04_part309_checked

  · exact kid04_part315_checked

  · exact kid04_part345_checked

  · exact kid04_part280_checked

  · exact kid04_part310_checked

  · exact kid04_part316_checked

  · exact kid04_part346_checked

  · exact kid04_part281_checked

  · exact kid04_part311_checked

  · exact kid04_part317_checked

  · exact kid04_part347_checked

  · exact kid04_part282_checked

  · exact kid04_part312_checked

  · exact kid04_part318_checked

  · exact kid04_part348_checked

  · exact kid04_part283_checked

  · exact kid04_part313_checked

  · exact kid04_part319_checked

  · exact kid04_part349_checked

def kid04_part375 : Audit := .cycle 14 1 false (2)
theorem kid04_part375_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part375) = true := by rfl

def kid04_part376 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 14 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 11 false (-2),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 11 false (0),
.cycle 13 1 true (-1),
.last 16 (5,true),
.cycle 14 11 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 11 false (-2),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 18 1 false (2),
.cycle 12 3 false (0),
.cycle 13 1 true (-1)
]),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 11 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 14 11 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 11 false (2),
.cycle 13 1 true (1),
.cycle 12 3 true (0),
.cycle 14 11 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 11 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 14 11 false (3),
.cycle 18 1 false (4),
.last 16 (5,true),
.cycle 13 1 true (1)
]),
.cycle 15 11 false (0),
.cycle 13 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 11 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (2),
.cycle 12 2 true (-1),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 14 11 false (1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 14 11 false (-1),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 11 false (-2),
.cycle 13 1 false (-1),
.cycle 17 11 false (1),
.last 15 (5,true),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 17 1 false (3),
.cycle 11 4 true (0),
.split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 12 2 true (0),
.cycle 14 11 false (0),
.cycle 0 15 true (0),
.cycle 14 11 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 24 true (0),
.cycle 16 11 false (2),
.cycle 14 11 false (2),
.cycle 8 6 true (0),
.cycle 13 1 true (1),
.cycle 14 11 false (1),
.last 15 (5,true),
.cycle 14 11 false (0),
.cycle 17 1 false (3),
.cycle 0 18 true (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 20 11 false (2),
.last 16 (5,true),
.cycle 13 1 true (1)
])
])
theorem kid04_part376_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part376) = true := by rfl

def kid04_part377 : Audit := .cycle 18 1 false (-2)
theorem kid04_part377_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part377) = true := by rfl

def kid04_part378 : Audit := .cycle 0 13 true (0)
theorem kid04_part378_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part378) = true := by rfl

def kid04_part379 : Audit := .cycle 12 4 false (0)
theorem kid04_part379_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part379) = true := by rfl

def kid04_part381 : Audit := .cycle 0 13 false (3)
theorem kid04_part381_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part381) = true := by rfl

def kid04_part382 : Audit := .split 24 (5,false) (byMove [
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
.last 26 (1,true),
.cycle 21 4 false (0),
.cycle 0 27 false (3),
.cycle 25 1 false (-3),
.cycle 20 5 false (0),
.cycle 24 1 false (-2),
.last 38 (1,true),
.cycle 1 24 false (3),
.cycle 14 11 false (1),
.cycle 29 1 false (1),
.last 26 (1,true),
.cycle 24 1 true (-2)
])
theorem kid04_part382_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part382) = true := by rfl

def kid04_part383 : Audit := .cycle 14 1 false (0)
theorem kid04_part383_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part383) = true := by rfl

def kid04_part384 : Audit := .cycle 13 1 false (-1)
theorem kid04_part384_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part384) = true := by rfl

def kid04_part385 : Audit := .split 17 (5,false) (byMove [
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
.last 19 (1,true),
.cycle 14 4 false (-1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 16 15 false (1),
.cycle 1 17 false (3),
.cycle 13 11 false (-1),
.cycle 22 1 false (0),
.last 19 (1,true),
.cycle 17 1 true (-3)
])
theorem kid04_part385_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part385) = true := by rfl

def kid04_part386 : Audit := .split 13 (5,false) (byMove [
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
.last 15 (1,true),
.cycle 13 4 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 12 15 false (3),
.cycle 1 13 false (3),
.cycle 13 11 false (1),
.cycle 18 1 false (2),
.last 15 (1,true),
.cycle 13 1 true (-1)
])
theorem kid04_part386_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part386) = true := by rfl

def kid04_part387 : Audit := .cycle 0 13 true (0)
theorem kid04_part387_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part387) = true := by rfl

def kid04_part388 : Audit := .split 24 (5,false) (byMove [
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
.last 26 (1,true),
.cycle 21 4 false (2),
.cycle 0 27 true (-1),
.cycle 25 1 false (-1),
.cycle 20 5 false (2),
.cycle 24 1 false (0),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 14 11 false (3),
.cycle 29 1 false (3),
.last 26 (1,true),
.cycle 24 1 true (0)
])
theorem kid04_part388_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part388) = true := by rfl

def kid04_part389 : Audit := .cycle 14 1 false (2)
theorem kid04_part389_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part389) = true := by rfl

def kid04_part390 : Audit := .cycle 13 1 false (1)
theorem kid04_part390_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part390) = true := by rfl

def kid04_part391 : Audit := .split 17 (5,false) (byMove [
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
.last 19 (1,true),
.cycle 14 4 false (1),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.cycle 13 5 false (1),
.cycle 17 1 false (-1),
.cycle 8 23 false (3),
.cycle 1 17 false (3),
.cycle 13 11 false (1),
.cycle 22 1 false (2),
.last 19 (1,true),
.cycle 17 1 true (-1)
])
theorem kid04_part391_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part391) = true := by rfl

def kid04_part392 : Audit := .split 13 (5,false) (byMove [
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
.last 15 (1,true),
.cycle 13 4 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 5 false (1),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 13 11 false (3),
.cycle 18 1 false (4),
.last 15 (1,true),
.cycle 13 1 true (1)
])
theorem kid04_part392_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part392) = true := by rfl

def kid04_part393 : Audit := .split 14 (1,true) (byMove [
.cycle 17 1 false (1),
.last 27 (5,false),
.last 20 (5,false),
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
.last 19 (5,false),
.last 20 (5,false),
.cycle 18 1 false (2),
.last 16 (5,false),
.cycle 12 3 false (0),
.last 44 (5,false),
.last 33 (5,false),
.cycle 2 13 false (3),
.last 30 (5,false),
.last 25 (5,false),
.last 15 (5,false)
])
theorem kid04_part393_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part393) = true := by rfl

def kid04_part394 : Audit := .split 16 (5,false) (byMove [
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
.last 18 (1,true),
.cycle 13 4 false (0),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.last 30 (1,true),
.cycle 1 16 false (3),
.cycle 13 11 false (0),
.cycle 21 1 false (1),
.last 18 (1,true),
.cycle 16 1 true (-2)
])
theorem kid04_part394_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part394) = true := by rfl

def kid04_part395 : Audit := .cycle 0 15 true (-1)
theorem kid04_part395_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part395) = true := by rfl

def kid04_part396 : Audit := .cycle 13 1 false (-1)
theorem kid04_part396_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part396) = true := by rfl

def kid04_part397 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 13 12 false (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 9 10 false (2),
.cycle 30 18 false (3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 12 8 true (-3),
.last 19 (1,true),
.cycle 14 4 false (-1),
.cycle 9 12 false (2),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 26 (1,true),
.cycle 9 32 false (4),
.cycle 13 11 false (-1),
.cycle 0 23 true (-3),
.last 19 (1,true),
.cycle 11 16 false (1)
])
theorem kid04_part397_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part397) = true := by rfl

def kid04_part398 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 0 15 true (-1),
.cycle 14 5 false (0),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 13 4 false (-1),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 0 31 true (-2),
.last 14 (1,true),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.cycle 12 3 false (0)
])
theorem kid04_part398_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part398) = true := by rfl

def kid04_part399 : Audit := .cycle 0 13 true (0)
theorem kid04_part399_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part399) = true := by rfl

def kid04_part400 : Audit := .cycle 1 12 true (0)
theorem kid04_part400_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part400) = true := by rfl

def kid04_part401 : Audit := .split 23 (5,false) (byMove [
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
.last 25 (1,true),
.cycle 20 4 false (1),
.cycle 0 26 true (-2),
.cycle 24 1 false (-2),
.cycle 19 5 false (1),
.cycle 23 1 false (-1),
.cycle 2 35 false (3),
.cycle 1 23 false (3),
.cycle 13 11 false (2),
.cycle 28 1 false (2),
.last 25 (1,true),
.cycle 23 1 true (-1)
])
theorem kid04_part401_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part401) = true := by rfl

def kid04_part402 : Audit := .cycle 17 1 false (3)
theorem kid04_part402_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part402) = true := by rfl

def kid04_part403 : Audit := .split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 19 (5,false),
.last 15 (5,false),
.cycle 17 1 false (3),
.last 27 (5,false),
.last 20 (5,false),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 12 3 true (0),
.last 23 (5,false),
.last 18 (5,false),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.last 19 (5,false),
.last 15 (5,false),
.last 27 (5,false),
.cycle 1 15 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 12 3 true (0)
])
theorem kid04_part403_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part403) = true := by rfl

def kid04_part404 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 21 1 false (-3),
.cycle 0 15 true (0),
.cycle 14 5 false (0),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 13 12 true (1),
.cycle 27 1 false (1),
.cycle 24 1 false (0),
.cycle 8 6 true (0),
.cycle 13 1 true (1),
.last 22 (1,true),
.last 14 (1,true),
.proven (BB6.Agent11Raw39RCPumps.M37.table) (fun m hm => BB6.Agent11Raw39RCPumps.M37.never m hm),
.cycle 17 1 false (3),
.cycle 14 5 false (0),
.cycle 12 3 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 34 1 false (2),
.last 15 (1,true),
.cycle 13 1 true (1)
])
theorem kid04_part404_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part404) = true := by rfl

def kid04_part380 : Audit := .split 12 (5,true) (byMove [(kid04_part381),(kid04_part382),(kid04_part383),(kid04_part384),(kid04_part385),(kid04_part386),(kid04_part387),(kid04_part388),(kid04_part389),(kid04_part390),(kid04_part391),(kid04_part392),(kid04_part393),(kid04_part394),(kid04_part395),(kid04_part396),(kid04_part397),(kid04_part398),(kid04_part399),(kid04_part400),(kid04_part401),(kid04_part402),(kid04_part403),(kid04_part404)])

theorem kid04_part380_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part380) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part381),(kid04_part382),(kid04_part383),(kid04_part384),(kid04_part385),(kid04_part386),(kid04_part387),(kid04_part388),(kid04_part389),(kid04_part390),(kid04_part391),(kid04_part392),(kid04_part393),(kid04_part394),(kid04_part395),(kid04_part396),(kid04_part397),(kid04_part398),(kid04_part399),(kid04_part400),(kid04_part401),(kid04_part402),(kid04_part403),(kid04_part404)] mv))) = true

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

def kid04_part405 : Audit := .cycle 0 12 true (0)
theorem kid04_part405_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part405) = true := by rfl

def kid04_part406 : Audit := .cycle 1 11 true (1)
theorem kid04_part406_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part406) = true := by rfl

def kid04_part407 : Audit := .cycle 24 1 false (2)
theorem kid04_part407_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part407) = true := by rfl

def kid04_part408 : Audit := .cycle 21 1 false (1)
theorem kid04_part408_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part408) = true := by rfl

def kid04_part409 : Audit := .cycle 8 4 true (1)
theorem kid04_part409_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part409) = true := by rfl

def kid04_part410 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 17 1 false (3),
.cycle 23 5 false (3),
.cycle 16 5 false (0),
.cycle 0 16 true (0),
.cycle 15 5 false (2),
.last 15 (5,true),
.cycle 19 5 false (-1),
.cycle 15 5 false (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 23 5 false (1),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.last 15 (5,true)
]),
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
.last 16 (1,true),
.cycle 18 1 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 25 1 false (1),
.cycle 19 1 false (3),
.last 16 (1,true),
.cycle 13 2 true (0)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (1),
.cycle 12 1 true (2),
.split 14 (1,true) (byMove [
.cycle 32 1 false (2),
.cycle 15 15 false (1),
.cycle 15 8 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 12 3 true (1),
.cycle 19 9 false (0),
.cycle 15 7 false (1),
.cycle 15 8 false (1),
.cycle 38 1 false (6),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.cycle 11 6 true (1),
.last 20 (5,true)
]),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 28 5 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 17 5 false (1),
.cycle 24 5 false (4),
.cycle 16 5 false (0),
.cycle 18 1 false (4),
.last 16 (5,true),
.last 15 (5,true),
.cycle 19 5 false (-1),
.cycle 15 5 false (0),
.cycle 19 5 false (1),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 27 5 false (1),
.cycle 1 16 true (0),
.cycle 15 5 false (1),
.cycle 25 5 false (1),
.last 16 (5,true),
.last 15 (5,true)
]),
.split 14 (5,true) (byMove [
.cycle 9 7 false (2),
.cycle 32 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 21 1 false (1),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 18 1 false (4),
.cycle 21 1 false (3),
.cycle 17 1 false (3),
.last 16 (1,true),
.cycle 18 1 false (0),
.cycle 23 1 false (1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (1,true),
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 29 1 false (1),
.last 18 (1,true),
.cycle 15 3 true (1)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.split 14 (1,true) (byMove [
.cycle 9 7 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 0 20 true (0),
.cycle 15 7 false (1),
.last 18 (5,true),
.cycle 61 1 false (7),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 15 (5,true),
.cycle 19 11 false (1),
.cycle 11 8 true (1),
.cycle 71 1 false (7),
.cycle 26 1 false (0),
.last 23 (5,true),
.last 17 (5,true),
.cycle 13 19 true (2),
.cycle 1 15 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 15 (5,true)
]),
.cycle 12 1 true (2)
])
theorem kid04_part410_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part410) = true := by rfl

def kid04_part411 : Audit := .split 19 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 12 14 false (1),
.cycle 13 7 false (1),
.cycle 0 21 false (3),
.cycle 17 3 false (-1),
.split 20 (5,true) (byMove [
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
.last 37 (5,false),
.cycle 1 20 false (3),
.cycle 12 13 false (1),
.cycle 25 1 false (1),
.last 23 (5,false),
.last 21 (5,false)
]),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 8 12 false (2),
.split 20 (5,false) (byMove [
.last 37 (5,true),
.cycle 1 20 false (3),
.cycle 12 13 false (1),
.cycle 25 1 false (1),
.last 23 (5,true),
.last 22 (5,true),
.cycle 0 21 true (-2),
.cycle 12 14 true (-2),
.cycle 26 32 true (-4),
.cycle 12 13 false (1),
.cycle 14 7 true (-2),
.cycle 20 1 true (0),
.cycle 18 3 true (-2),
.cycle 9 12 false (2),
.cycle 0 23 true (-2),
.cycle 12 11 false (1),
.last 23 (5,true),
.last 22 (5,true),
.last 37 (5,true),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.last 93 (5,true),
.last 23 (5,true),
.cycle 20 1 true (0)
]),
.cycle 12 8 false (1),
.cycle 15 6 false (0),
.cycle 13 7 false (1),
.cycle 23 1 false (1),
.cycle 17 3 false (-1),
.split 20 (5,true) (byMove [
.cycle 9 13 false (2),
.last 46 (5,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 23 1 false (1),
.last 22 (5,false),
.cycle 13 8 false (1),
.cycle 0 22 true (-2),
.cycle 17 4 true (-2),
.last 22 (5,false),
.cycle 18 3 false (-1),
.cycle 15 6 false (0),
.cycle 25 1 false (1),
.cycle 21 1 false (-3),
.cycle 14 7 false (0),
.last 21 (5,false),
.cycle 12 15 false (1),
.cycle 19 2 true (-2),
.cycle 16 5 false (0),
.cycle 6 28 false (3),
.cycle 11 10 false (1),
.last 22 (5,false)
]),
.cycle 3 36 false (3),
.cycle 19 16 true (-2),
.cycle 2 18 false (3),
.cycle 28 36 true (-4),
.cycle 11 16 false (1),
.split 20 (5,false) (byMove [
.cycle 12 15 false (1),
.cycle 19 2 true (-1),
.cycle 16 5 false (0),
.cycle 6 28 false (3),
.cycle 11 10 false (1),
.last 21 (5,true),
.last 43 (5,true),
.cycle 12 14 true (-2),
.cycle 3 20 false (3),
.cycle 3 18 false (3),
.last 29 (5,true),
.cycle 20 1 true (0),
.last 25 (5,true),
.last 22 (5,true),
.cycle 16 5 false (0),
.cycle 28 36 true (-4),
.cycle 11 10 false (1),
.last 21 (5,true),
.last 37 (5,true),
.last 36 (5,true),
.last 35 (5,true),
.cycle 3 24 false (3),
.last 23 (5,true),
.cycle 20 1 true (0)
])
])
theorem kid04_part411_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part411) = true := by rfl

def kid04_part412 : Audit := .split 12 (1,true) (byMove [
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 22 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 3 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 14 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 3 false (0),
.last 15 (5,true),
.last 16 (5,true),
.cycle 14 3 false (-1),
.last 18 (5,true),
.cycle 14 1 false (-2),
.cycle 15 3 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 19 3 false (0),
.cycle 12 3 false (0),
.last 15 (5,true)
]),
.cycle 15 1 false (3),
.cycle 22 3 false (3),
.cycle 15 3 false (0),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 22 3 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 3 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 22 3 false (3),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 15 3 false (2),
.last 14 (5,false),
.last 16 (5,false),
.cycle 14 3 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 15 3 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 3 false (2),
.cycle 18 1 false (4),
.cycle 12 3 true (0),
.last 14 (5,false)
]),
.cycle 18 3 false (-1),
.cycle 13 3 false (0),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 28 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 3 false (-2),
.cycle 13 1 false (-1),
.cycle 17 3 false (0),
.cycle 12 2 true (-1),
.cycle 16 3 false (-1),
.cycle 17 1 false (3),
.cycle 14 3 false (0),
.last 14 (5,true),
.last 16 (5,true),
.cycle 14 3 false (-1),
.cycle 19 3 false (0),
.cycle 14 1 false (-2),
.cycle 15 3 false (-2),
.cycle 13 1 false (-1),
.cycle 12 5 false (1),
.last 15 (5,true),
.cycle 14 3 false (0),
.cycle 25 3 false (0),
.cycle 11 3 false (1),
.last 14 (5,true)
]),
.cycle 22 3 false (1),
.cycle 1 13 true (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.split 13 (5,true) (byMove [
.cycle 16 1 false (2),
.last 15 (5,false),
.cycle 16 3 false (-1),
.cycle 0 15 true (0),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 9 16 true (0),
.cycle 22 3 false (1),
.cycle 20 3 false (1),
.cycle 8 6 true (0),
.last 14 (5,false),
.cycle 17 3 false (0),
.cycle 12 2 true (0),
.cycle 16 3 false (-1),
.cycle 17 1 false (3),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 26 3 false (1),
.cycle 12 3 true (0),
.last 14 (5,false)
])
])
theorem kid04_part412_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part412) = true := by rfl

def kid04_part413 : Audit := .cycle 9 11 false (2)
theorem kid04_part413_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part413) = true := by rfl

def kid04_part414 : Audit := .cycle 15 1 false (3)
theorem kid04_part414_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part414) = true := by rfl

def kid04_part415 : Audit := .cycle 12 4 false (0)
theorem kid04_part415_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part415) = true := by rfl

def kid04_part417 : Audit := .cycle 9 5 false (2)
theorem kid04_part417_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part417) = true := by rfl

def kid04_part418 : Audit := .cycle 0 16 true (-1)
theorem kid04_part418_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part418) = true := by rfl

def kid04_part419 : Audit := .cycle 14 1 false (0)
theorem kid04_part419_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part419) = true := by rfl

def kid04_part420 : Audit := .cycle 13 1 false (-1)
theorem kid04_part420_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part420) = true := by rfl

def kid04_part421 : Audit := .split 17 (5,false) (byMove [
.cycle 9 10 false (2),
.cycle 8 18 false (2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 20 1 false (0),
.last 18 (1,true),
.cycle 13 6 false (-1),
.cycle 9 11 false (2),
.cycle 16 2 true (-3),
.cycle 12 6 false (0),
.last 19 (1,true),
.cycle 14 4 false (-1),
.cycle 22 1 false (0),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 13 13 false (0),
.last 18 (1,true),
.cycle 15 3 false (-1),
.last 25 (1,true),
.cycle 11 7 false (1),
.cycle 16 3 false (-2)
])
theorem kid04_part421_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part421) = true := by rfl

def kid04_part422 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 1 34 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.last 15 (1,true),
.last 18 (1,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 17 2 true (-2),
.cycle 16 1 true (0),
.last 15 (1,true),
.cycle 13 4 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 4 34 false (3),
.last 15 (1,true),
.cycle 18 1 true (-2)
])
theorem kid04_part422_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part422) = true := by rfl

def kid04_part423 : Audit := .cycle 15 1 false (3)
theorem kid04_part423_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part423) = true := by rfl

def kid04_part424 : Audit := .split 13 (1,true) (byMove [
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
.last 22 (5,false),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.last 18 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 24 (5,false),
.cycle 18 1 false (4),
.cycle 11 5 true (0),
.last 14 (5,false)
])
theorem kid04_part424_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part424) = true := by rfl

def kid04_part425 : Audit := .split 18 (5,false) (byMove [
.cycle 9 11 false (2),
.last 41 (1,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 14 5 false (0),
.cycle 18 1 false (-2),
.cycle 21 1 false (1),
.last 19 (1,true),
.cycle 13 6 false (1),
.cycle 0 20 true (-2),
.cycle 17 2 true (-2),
.cycle 21 1 false (1),
.last 20 (1,true),
.cycle 15 4 false (0),
.cycle 23 1 false (1),
.cycle 19 1 false (-3),
.cycle 14 5 false (0),
.cycle 18 1 false (-2),
.cycle 13 13 false (1),
.last 19 (1,true),
.cycle 16 3 false (0),
.cycle 7 26 false (3),
.cycle 11 8 false (1),
.cycle 13 13 false (1)
])
theorem kid04_part425_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part425) = true := by rfl

def kid04_part426 : Audit := .cycle 0 14 true (0)
theorem kid04_part426_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part426) = true := by rfl

def kid04_part427 : Audit := .split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.last 15 (1,true),
.cycle 13 6 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 13 6 true (0),
.last 16 (1,true),
.cycle 13 4 false (1),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.cycle 13 13 false (3),
.last 15 (1,true),
.cycle 13 3 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 8 8 true (0)
])
theorem kid04_part427_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part427) = true := by rfl

def kid04_part428 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 30 true (-1),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 5 false (2),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.last 27 (1,true),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 18 2 true (1),
.cycle 14 1 true (2),
.last 16 (1,true),
.cycle 14 4 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 5 false (2),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 3 false (3),
.cycle 19 1 false (5),
.last 16 (1,true),
.cycle 14 1 true (2)
])
theorem kid04_part428_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part428) = true := by rfl

def kid04_part429 : Audit := .split 14 (1,true) (byMove [
.cycle 0 18 true (-1),
.last 27 (5,false),
.last 20 (5,false),
.cycle 0 19 true (-1),
.last 16 (5,false),
.cycle 12 3 false (0),
.last 28 (5,false),
.last 27 (5,false),
.last 23 (5,false),
.cycle 0 16 true (-1),
.last 16 (5,false),
.last 18 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.last 20 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.cycle 12 3 false (0),
.cycle 3 15 false (3),
.last 43 (5,false),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 23 (5,false),
.last 27 (5,false)
])
theorem kid04_part429_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part429) = true := by rfl

def kid04_part430 : Audit := .split 16 (5,false) (byMove [
.cycle 9 9 false (2),
.last 21 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.cycle 0 20 true (-2),
.last 17 (1,true),
.cycle 13 6 false (0),
.last 19 (1,true),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.last 18 (1,true),
.cycle 13 4 false (0),
.cycle 0 22 true (-3),
.cycle 17 1 false (-3),
.cycle 13 5 false (0),
.cycle 16 1 false (-2),
.cycle 0 20 true (-2),
.last 17 (1,true),
.cycle 14 3 false (0),
.last 19 (1,true),
.cycle 11 6 false (1),
.last 18 (1,true)
])
theorem kid04_part430_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part430) = true := by rfl

def kid04_part431 : Audit := .cycle 17 1 false (3)
theorem kid04_part431_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part431) = true := by rfl

def kid04_part432 : Audit := .cycle 13 1 false (-1)
theorem kid04_part432_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part432) = true := by rfl

def kid04_part433 : Audit := .split 17 (5,false) (byMove [
.cycle 9 10 false (2),
.last 22 (1,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 23 1 false (3),
.last 18 (1,true),
.cycle 13 6 false (-1),
.last 20 (1,true),
.cycle 16 2 true (-3),
.cycle 12 6 false (0),
.last 19 (1,true),
.cycle 14 4 false (-1),
.cycle 25 1 false (3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 26 13 false (0),
.last 18 (1,true),
.cycle 15 3 false (-1),
.last 20 (1,true),
.cycle 11 7 false (1),
.cycle 16 3 false (-2)
])
theorem kid04_part433_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part433) = true := by rfl

def kid04_part434 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.last 186 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.cycle 23 1 false (1),
.last 14 (1,true),
.cycle 13 6 false (0),
.cycle 17 1 false (3),
.cycle 13 2 true (-1),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 13 4 false (-1),
.cycle 27 1 false (1),
.cycle 14 1 false (-2),
.cycle 13 5 false (-1),
.cycle 13 1 false (-1),
.last 17 (1,true),
.last 14 (1,true),
.cycle 13 3 false (0),
.cycle 0 40 true (-2),
.cycle 11 3 false (1),
.cycle 12 3 false (0)
])
theorem kid04_part434_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part434) = true := by rfl

def kid04_part435 : Audit := .split 25 (5,false) (byMove [
.cycle 9 18 false (3),
.cycle 9 21 true (-2),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 21 5 false (1),
.cycle 25 1 false (-1),
.cycle 28 1 false (2),
.last 26 (1,true),
.cycle 20 6 false (2),
.cycle 9 19 true (-1),
.cycle 24 2 true (-1),
.cycle 0 67 true (-1),
.last 27 (1,true),
.cycle 22 4 false (1),
.cycle 30 1 false (2),
.cycle 26 1 false (-2),
.cycle 21 5 false (1),
.cycle 25 1 false (-1),
.cycle 13 13 false (3),
.last 26 (1,true),
.cycle 23 3 false (1),
.cycle 9 19 true (-1),
.cycle 11 15 false (3),
.cycle 0 147 true (-3)
])
theorem kid04_part435_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part435) = true := by rfl

def kid04_part436 : Audit := .split 13 (1,true) (byMove [
.cycle 16 1 false (2),
.last 26 (5,false),
.last 19 (5,false),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.last 25 (5,false),
.last 25 (5,false),
.last 23 (5,false),
.cycle 8 6 true (0),
.last 14 (5,false),
.last 20 (5,false),
.last 18 (5,false),
.last 19 (5,false),
.cycle 17 1 false (3),
.last 15 (5,false),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.last 29 (5,false),
.cycle 11 5 true (0),
.last 14 (5,false)
])
theorem kid04_part436_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part436) = true := by rfl

def kid04_part437 : Audit := .split 15 (5,false) (byMove [
.cycle 9 8 false (2),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 13 5 false (1),
.cycle 15 1 false (-1),
.cycle 18 1 false (2),
.last 16 (1,true),
.cycle 13 6 false (1),
.cycle 0 17 true (-1),
.cycle 14 2 true (-1),
.cycle 13 12 true (-1),
.last 17 (1,true),
.cycle 13 4 false (1),
.cycle 20 1 false (2),
.cycle 16 1 false (-2),
.cycle 13 5 false (1),
.cycle 15 1 false (-1),
.cycle 13 13 false (2),
.last 16 (1,true),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 11 5 false (1),
.cycle 2 15 false (3)
])
theorem kid04_part437_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part437) = true := by rfl

def kid04_part438 : Audit := .cycle 0 14 true (0)
theorem kid04_part438_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part438) = true := by rfl

def kid04_part439 : Audit := .cycle 11 2 true (0)
theorem kid04_part439_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part439) = true := by rfl

def kid04_part440 : Audit := .split 14 (5,false) (byMove [
.cycle 9 20 false (3),
.last 15 (1,true),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.last 27 (1,true),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.cycle 14 1 true (2),
.last 18 (1,true),
.last 15 (1,true),
.cycle 0 23 true (-2),
.cycle 30 1 false (-2),
.cycle 12 5 true (0),
.cycle 12 3 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 4 40 true (0),
.last 16 (1,true),
.cycle 14 1 true (2)
])
theorem kid04_part440_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part440) = true := by rfl

def kid04_part416 : Audit := .split 12 (5,true) (byMove [(kid04_part417),(kid04_part418),(kid04_part419),(kid04_part420),(kid04_part421),(kid04_part422),(kid04_part423),(kid04_part424),(kid04_part425),(kid04_part426),(kid04_part427),(kid04_part428),(kid04_part429),(kid04_part430),(kid04_part431),(kid04_part432),(kid04_part433),(kid04_part434),(kid04_part435),(kid04_part436),(kid04_part437),(kid04_part438),(kid04_part439),(kid04_part440)])

theorem kid04_part416_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part416) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part417),(kid04_part418),(kid04_part419),(kid04_part420),(kid04_part421),(kid04_part422),(kid04_part423),(kid04_part424),(kid04_part425),(kid04_part426),(kid04_part427),(kid04_part428),(kid04_part429),(kid04_part430),(kid04_part431),(kid04_part432),(kid04_part433),(kid04_part434),(kid04_part435),(kid04_part436),(kid04_part437),(kid04_part438),(kid04_part439),(kid04_part440)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part417_checked

  · exact kid04_part423_checked

  · exact kid04_part429_checked

  · exact kid04_part435_checked

  · exact kid04_part418_checked

  · exact kid04_part424_checked

  · exact kid04_part430_checked

  · exact kid04_part436_checked

  · exact kid04_part419_checked

  · exact kid04_part425_checked

  · exact kid04_part431_checked

  · exact kid04_part437_checked

  · exact kid04_part420_checked

  · exact kid04_part426_checked

  · exact kid04_part432_checked

  · exact kid04_part438_checked

  · exact kid04_part421_checked

  · exact kid04_part427_checked

  · exact kid04_part433_checked

  · exact kid04_part439_checked

  · exact kid04_part422_checked

  · exact kid04_part428_checked

  · exact kid04_part434_checked

  · exact kid04_part440_checked

def kid04_part441 : Audit := .cycle 0 12 true (0)
theorem kid04_part441_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part441) = true := by rfl

def kid04_part442 : Audit := .cycle 1 11 true (1)
theorem kid04_part442_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part442) = true := by rfl

def kid04_part443 : Audit := .cycle 2 10 true (1)
theorem kid04_part443_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part443) = true := by rfl

def kid04_part444 : Audit := .cycle 34 1 false (6)
theorem kid04_part444_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part444) = true := by rfl

def kid04_part445 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 50 true (-2),
.cycle 22 1 false (-2),
.cycle 0 18 true (0),
.cycle 14 6 false (1),
.split 14 (5,true) (byMove [
.cycle 0 19 true (-1),
.last 28 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.cycle 0 18 true (0),
.last 20 (5,false),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.last 21 (5,false),
.last 15 (5,false),
.cycle 13 3 false (1),
.last 20 (5,false),
.cycle 0 22 true (-1),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.cycle 0 18 true (0),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.last 25 (5,false),
.last 17 (5,false),
.last 15 (5,false)
]),
.cycle 34 1 false (6),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 19 1 false (3),
.cycle 15 7 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 34 1 false (6),
.cycle 28 1 false (2),
.cycle 8 7 true (1),
.last 15 (5,false),
.last 17 (5,false),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 15 7 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 71 1 false (7),
.cycle 12 3 true (1),
.last 15 (5,false)
]),
.cycle 13 10 false (1),
.cycle 14 5 false (0),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.cycle 11 5 true (0),
.split 14 (5,true) (byMove [
.cycle 9 7 false (2),
.last 34 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 16 (5,false),
.last 22 (5,false),
.cycle 18 1 false (4),
.cycle 11 5 true (0),
.last 17 (5,false),
.cycle 13 3 false (1),
.last 20 (5,false),
.last 25 (5,false),
.cycle 15 1 false (-1),
.last 21 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 13 2 true (0),
.last 19 (5,false),
.last 31 (5,false),
.cycle 11 5 true (0),
.last 17 (5,false)
]),
.cycle 0 31 true (0),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.split 14 (5,true) (byMove [
.cycle 32 1 false (2),
.last 16 (5,false),
.cycle 15 8 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.last 15 (5,false),
.cycle 17 9 false (1),
.cycle 13 2 true (1),
.cycle 15 8 false (1),
.cycle 38 1 false (6),
.cycle 11 5 true (1),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.cycle 12 3 true (1),
.last 15 (5,false)
])
])
theorem kid04_part445_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part445) = true := by rfl

def kid04_part447 : Audit := .cycle 28 1 false (2)
theorem kid04_part447_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part447) = true := by rfl

def kid04_part448 : Audit := .split 13 (1,true) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (1),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 13 10 false (1),
.cycle 14 5 false (0),
.cycle 9 15 false (2),
.cycle 17 1 false (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 11 5 true (1),
.cycle 12 2 true (1)
])
theorem kid04_part448_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part448) = true := by rfl

def kid04_part449 : Audit := .cycle 13 6 false (1)
theorem kid04_part449_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part449) = true := by rfl

def kid04_part450 : Audit := .cycle 0 14 true (0)
theorem kid04_part450_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part450) = true := by rfl

def kid04_part451 : Audit := .cycle 11 2 true (1)
theorem kid04_part451_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part451) = true := by rfl

def kid04_part452 : Audit := .split 13 (5,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 17 1 false (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 9 15 false (2),
.cycle 17 1 false (3),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.last 15 (1,true),
.cycle 12 2 true (1)
])
theorem kid04_part452_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part452) = true := by rfl

def kid04_part453 : Audit := .cycle 0 13 true (0)
theorem kid04_part453_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part453) = true := by rfl

def kid04_part454 : Audit := .cycle 1 12 true (1)
theorem kid04_part454_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part454) = true := by rfl

def kid04_part455 : Audit := .cycle 0 27 true (0)
theorem kid04_part455_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part455) = true := by rfl

def kid04_part456 : Audit := .cycle 3 10 true (1)
theorem kid04_part456_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part456) = true := by rfl

def kid04_part457 : Audit := .cycle 8 5 true (1)
theorem kid04_part457_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part457) = true := by rfl

def kid04_part458 : Audit := .cycle 12 1 true (2)
theorem kid04_part458_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part458) = true := by rfl

def kid04_part459 : Audit := .split 16 (1,true) (byMove [
.cycle 9 9 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 7 false (-1),
.last 20 (5,true),
.cycle 19 1 false (3),
.cycle 23 7 false (4),
.cycle 17 7 false (1),
.cycle 0 18 true (0),
.cycle 17 7 false (2),
.last 17 (5,true),
.cycle 19 7 false (0),
.cycle 17 7 false (0),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.cycle 17 7 false (-1),
.last 20 (5,true),
.cycle 23 7 false (2),
.cycle 1 17 true (0),
.cycle 17 7 false (1),
.cycle 0 18 true (0),
.cycle 11 6 true (0),
.last 17 (5,true)
])
theorem kid04_part459_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part459) = true := by rfl

def kid04_part460 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 50 true (-2),
.cycle 22 1 false (-2),
.cycle 0 18 true (0),
.cycle 14 6 false (1),
.last 14 (5,true),
.cycle 34 1 false (6),
.cycle 1 14 true (1),
.cycle 16 7 false (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.last 14 (5,true),
.cycle 13 10 false (1),
.cycle 14 5 false (0),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 31 true (0),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.last 14 (5,true)
])
theorem kid04_part460_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part460) = true := by rfl

def kid04_part461 : Audit := .cycle 13 6 false (1)
theorem kid04_part461_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part461) = true := by rfl

def kid04_part462 : Audit := .cycle 34 1 false (6)
theorem kid04_part462_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part462) = true := by rfl

def kid04_part463 : Audit := .split 14 (5,true) (byMove [
.cycle 32 1 false (2),
.last 15 (1,true),
.cycle 15 8 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.cycle 15 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.last 17 (1,true),
.last 18 (1,true),
.last 15 (1,true),
.cycle 15 8 false (1),
.cycle 38 1 false (6),
.cycle 13 2 true (1),
.cycle 15 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.last 16 (1,true),
.cycle 12 3 true (1)
])
theorem kid04_part463_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part463) = true := by rfl

def kid04_part464 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 22 1 false (-2),
.last 16 (1,true),
.cycle 14 6 false (1),
.cycle 15 1 false (-1),
.cycle 34 1 false (6),
.last 14 (1,true),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 22 1 false (4),
.last 23 (1,true),
.last 14 (1,true),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 12 3 true (1)
])
theorem kid04_part464_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part464) = true := by rfl

def kid04_part465 : Audit := .cycle 0 13 true (0)
theorem kid04_part465_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part465) = true := by rfl

def kid04_part466 : Audit := .cycle 1 12 true (1)
theorem kid04_part466_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part466) = true := by rfl

def kid04_part467 : Audit := .cycle 2 11 true (1)
theorem kid04_part467_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part467) = true := by rfl

def kid04_part468 : Audit := .cycle 4 34 true (1)
theorem kid04_part468_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part468) = true := by rfl

def kid04_part469 : Audit := .split 14 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 15 15 false (1),
.cycle 15 8 false (2),
.cycle 0 19 true (0),
.cycle 11 6 true (1),
.last 15 (5,true),
.cycle 6 34 true (1),
.cycle 1 15 true (1),
.cycle 16 11 false (2),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 15 (5,true),
.cycle 20 9 false (0),
.last 22 (5,true),
.last 19 (5,true),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 13 19 true (2),
.cycle 1 15 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.cycle 11 4 true (1),
.last 15 (5,true)
])
theorem kid04_part469_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part469) = true := by rfl

def kid04_part470 : Audit := .cycle 12 1 true (2)
theorem kid04_part470_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part470) = true := by rfl

def kid04_part446 : Audit := .split 12 (5,false) (byMove [(kid04_part447),(kid04_part448),(kid04_part449),(kid04_part450),(kid04_part451),(kid04_part452),(kid04_part453),(kid04_part454),(kid04_part455),(kid04_part456),(kid04_part457),(kid04_part458),(kid04_part459),(kid04_part460),(kid04_part461),(kid04_part462),(kid04_part463),(kid04_part464),(kid04_part465),(kid04_part466),(kid04_part467),(kid04_part468),(kid04_part469),(kid04_part470)])

theorem kid04_part446_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part446) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part447),(kid04_part448),(kid04_part449),(kid04_part450),(kid04_part451),(kid04_part452),(kid04_part453),(kid04_part454),(kid04_part455),(kid04_part456),(kid04_part457),(kid04_part458),(kid04_part459),(kid04_part460),(kid04_part461),(kid04_part462),(kid04_part463),(kid04_part464),(kid04_part465),(kid04_part466),(kid04_part467),(kid04_part468),(kid04_part469),(kid04_part470)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part447_checked

  · exact kid04_part453_checked

  · exact kid04_part459_checked

  · exact kid04_part465_checked

  · exact kid04_part448_checked

  · exact kid04_part454_checked

  · exact kid04_part460_checked

  · exact kid04_part466_checked

  · exact kid04_part449_checked

  · exact kid04_part455_checked

  · exact kid04_part461_checked

  · exact kid04_part467_checked

  · exact kid04_part450_checked

  · exact kid04_part456_checked

  · exact kid04_part462_checked

  · exact kid04_part468_checked

  · exact kid04_part451_checked

  · exact kid04_part457_checked

  · exact kid04_part463_checked

  · exact kid04_part469_checked

  · exact kid04_part452_checked

  · exact kid04_part458_checked

  · exact kid04_part464_checked

  · exact kid04_part470_checked

def kid04_part374 : Audit := .split 11 (4,true) (byMove [(kid04_part375),(kid04_part376),(kid04_part377),(kid04_part378),(kid04_part379),(kid04_part380),(kid04_part405),(kid04_part406),(kid04_part407),(kid04_part408),(kid04_part409),(kid04_part410),(kid04_part411),(kid04_part412),(kid04_part413),(kid04_part414),(kid04_part415),(kid04_part416),(kid04_part441),(kid04_part442),(kid04_part443),(kid04_part444),(kid04_part445),(kid04_part446)])

theorem kid04_part374_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (kid04_part374) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,1⟩)) (4,true) (some mv)) (byMove [(kid04_part375),(kid04_part376),(kid04_part377),(kid04_part378),(kid04_part379),(kid04_part380),(kid04_part405),(kid04_part406),(kid04_part407),(kid04_part408),(kid04_part409),(kid04_part410),(kid04_part411),(kid04_part412),(kid04_part413),(kid04_part414),(kid04_part415),(kid04_part416),(kid04_part441),(kid04_part442),(kid04_part443),(kid04_part444),(kid04_part445),(kid04_part446)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part375_checked

  · exact kid04_part405_checked

  · exact kid04_part411_checked

  · exact kid04_part441_checked

  · exact kid04_part376_checked

  · exact kid04_part406_checked

  · exact kid04_part412_checked

  · exact kid04_part442_checked

  · exact kid04_part377_checked

  · exact kid04_part407_checked

  · exact kid04_part413_checked

  · exact kid04_part443_checked

  · exact kid04_part378_checked

  · exact kid04_part408_checked

  · exact kid04_part414_checked

  · exact kid04_part444_checked

  · exact kid04_part379_checked

  · exact kid04_part409_checked

  · exact kid04_part415_checked

  · exact kid04_part445_checked

  · exact kid04_part380_checked

  · exact kid04_part410_checked

  · exact kid04_part416_checked

  · exact kid04_part446_checked

def kid04_part471 : Audit := .cycle 0 11 true (0)
theorem kid04_part471_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,2⟩)) (kid04_part471) = true := by rfl

def kid04_part472 : Audit := .cycle 14 1 false (0)
theorem kid04_part472_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,3⟩)) (kid04_part472) = true := by rfl

def kid04_part474 : Audit := .cycle 17 1 false (1)
theorem kid04_part474_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part474) = true := by rfl

def kid04_part475 : Audit := .cycle 24 1 false (0)
theorem kid04_part475_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part475) = true := by rfl

def kid04_part476 : Audit := .cycle 12 1 false (0)
theorem kid04_part476_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part476) = true := by rfl

def kid04_part477 : Audit := .cycle 11 1 false (-1)
theorem kid04_part477_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part477) = true := by rfl

def kid04_part478 : Audit := .cycle 11 1 false (-1)
theorem kid04_part478_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part478) = true := by rfl

def kid04_part480 : Audit := .split 46 (5,true) (byMove [
.cycle 42 11 false (0),
.cycle 54 1 false (-4),
.cycle 48 1 false (-4),
.cycle 47 1 false (-5),
.cycle 47 1 false (-5),
.cycle 21 30 false (4),
.last 48 (1,true),
.cycle 21 33 false (4),
.cycle 51 1 false (-1),
.cycle 47 1 false (-3),
.cycle 47 1 false (-3),
.proven (BB6.Agent11Raw39RCCounter38.M38.table) (fun m hm => BB6.Agent11Raw39RCCounter38.M38.never m hm),
.last 48 (1,true),
.cycle 0 51 false (4),
.last 50 (1,true),
.cycle 47 1 false (-5),
.cycle 47 1 false (-5),
.cycle 45 6 false (-3),
.last 48 (1,true),
.proven (BB6.Agent11Raw39RCCounter39.M39.table) (fun m hm => BB6.Agent11Raw39RCCounter39.M39.never m hm),
.cycle 42 20 false (0),
.cycle 51 1 false (-3),
.cycle 42 14 false (0),
.cycle 53 1 false (-1)
])
theorem kid04_part480_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part480) = true := by rfl

def kid04_part481 : Audit := .cycle 19 1 false (-1)
theorem kid04_part481_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part481) = true := by rfl

def kid04_part482 : Audit := .cycle 13 1 false (-1)
theorem kid04_part482_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part482) = true := by rfl

def kid04_part483 : Audit := .cycle 12 1 false (-2)
theorem kid04_part483_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part483) = true := by rfl

def kid04_part484 : Audit := .cycle 12 1 false (-2)
theorem kid04_part484_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part484) = true := by rfl

def kid04_part485 : Audit := .cycle 11 1 false (-1)
theorem kid04_part485_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part485) = true := by rfl

def kid04_part486 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.last 20 (5,true),
.last 14 (5,true),
.cycle 23 1 false (1),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 0, 1, 0, 4],[128, 256, 8, 1140867328, 1073741826, 1, 8192, 16384, 512, 1140867332, 128, 64, 33554432, 67108864, 2097152, 256, 1074266112, 262144, 128, 256, 8, 16384, 1073741826, 1, 33554432, 67108864, 8, 4, 1073741824, 1, 1073741824],[4, 2, 1073742080, 1, 128, 1073741824, 256, 128, 16384, 64, 1073750016, 1073741824, 1048576, 524288, 1140850688, 262144, 1073741824, 1073741824, 4, 2, 1073742080, 1, 128, 1073741824, 4, 2, 1073741824, 1, 1073741824, 1073741824, 1073741824],1599716190⟩,
.cycle 27 1 false (1),
.cycle 0 15 true (-1),
.cycle 0 16 true (-1),
.last 14 (5,true),
.cycle 16 1 false (0),
.last 23 (5,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.last 14 (5,true),
.cycle 0 31 true (-1),
.last 25 (5,true),
.last 16 (5,true),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part486_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part486) = true := by rfl

def kid04_part487 : Audit := .cycle 0 19 true (-1)
theorem kid04_part487_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part487) = true := by rfl

def kid04_part488 : Audit := .cycle 16 1 false (4)
theorem kid04_part488_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part488) = true := by rfl

def kid04_part489 : Audit := .cycle 12 1 false (0)
theorem kid04_part489_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part489) = true := by rfl

def kid04_part490 : Audit := .cycle 12 1 false (0)
theorem kid04_part490_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part490) = true := by rfl

def kid04_part491 : Audit := .split 13 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 17 1 true (1),
.cycle 16 1 false (4),
.last 14 (1,true),
.cycle 15 1 false (1),
.cycle 0 15 true (-1),
.cycle 15 1 true (1),
.cycle 15 1 true (3),
.last 15 (1,true),
.cycle 24 1 true (0),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 12 2 true (0),
.cycle 22 1 false (2),
.last 14 (1,true),
.cycle 16 1 true (0),
.cycle 0 15 true (-1),
.cycle 15 5 true (0),
.cycle 15 1 true (3)
])
theorem kid04_part491_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part491) = true := by rfl

def kid04_part492 : Audit := .split 13 (1,true) (byMove [
.cycle 16 1 false (0),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.last 19 (5,true),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 42 1 false (-4),
.cycle 20 1 false (-2),
.cycle 27 1 false (-1),
.cycle 19 1 false (-1),
.cycle 8 6 false (2),
.last 17 (5,true),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 15 1 false (-3),
.cycle 20 1 false (4),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 27 (5,true),
.last 17 (5,true),
.last 46 (5,true),
.cycle 4 10 false (3),
.last 16 (5,true),
.cycle 9 8 false (1)
])
theorem kid04_part492_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part492) = true := by rfl

def kid04_part493 : Audit := .cycle 10 4 false (0)
theorem kid04_part493_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part493) = true := by rfl

def kid04_part494 : Audit := .split 15 (1,true) (byMove [
.cycle 0 19 true (-2),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 20 true (-2),
.last 24 (5,true),
.last 16 (5,true),
.cycle 25 1 false (1),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 0, 4, 4, 4],[128, 256, 8, 1328047055, 1328047055, 1, 8192, 16384, 512, 1328047055, 128, 1328047055, 33554432, 67108864, 2097152, 256, 1328047055, 1328047055, 33554432, 67108864, 8, 16384, 1328047055, 1, 33554432, 67108864, 134217728, 1328047055, 1328047055, 1328047055, 1073741824],[4, 2, 1328047055, 1, 128, 1073741824, 256, 128, 16384, 64, 1328047055, 1073741824, 1048576, 524288, 1328047055, 262144, 1073741824, 1073741824, 4, 2, 1328047055, 1, 1328047055, 1073741824, 67108864, 33554432, 1328047055, 16777216, 1328047055, 1073741824, 1073741824],2136980318⟩,
.cycle 31 1 false (1),
.cycle 0 17 true (-2),
.cycle 19 1 false (-1),
.last 16 (5,true),
.cycle 18 1 false (0),
.last 27 (5,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 10 6 true (-2),
.last 16 (5,true),
.cycle 0 35 true (-2),
.last 27 (5,true),
.last 18 (5,true),
.last 38 (5,true),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid04_part494_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part494) = true := by rfl

def kid04_part495 : Audit := .cycle 12 1 false (-2)
theorem kid04_part495_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part495) = true := by rfl

def kid04_part496 : Audit := .cycle 12 1 false (-2)
theorem kid04_part496_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part496) = true := by rfl

def kid04_part497 : Audit := .cycle 11 1 false (-1)
theorem kid04_part497_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part497) = true := by rfl

def kid04_part498 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 23 1 false (-1),
.cycle 0 21 true (-2),
.cycle 0 18 true (-1),
.last 15 (5,true),
.last 14 (5,true),
.last 61 (5,true),
.last 27 (5,true),
.last 17 (5,true),
.cycle 0 15 true (-1),
.last 27 (5,true),
.last 14 (5,true),
.cycle 9 7 false (1),
.last 24 (5,true),
.last 21 (5,true),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true),
.last 25 (5,true),
.last 25 (5,true),
.last 16 (5,true),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part498_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part498) = true := by rfl

def kid04_part499 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 false (3),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 1 16 false (3),
.cycle 0 21 true (-1),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 1 21 true (-1),
.last 17 (1,true),
.cycle 1 19 false (3),
.cycle 0 25 true (-2),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.last 17 (1,true),
.last 34 (1,true),
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.cycle 0 21 true (-1),
.cycle 9 7 false (1),
.last 34 (1,true)
])
theorem kid04_part499_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part499) = true := by rfl

def kid04_part500 : Audit := .cycle 24 1 false (0)
theorem kid04_part500_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part500) = true := by rfl

def kid04_part501 : Audit := .cycle 16 1 false (0)
theorem kid04_part501_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part501) = true := by rfl

def kid04_part502 : Audit := .cycle 9 3 false (1)
theorem kid04_part502_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part502) = true := by rfl

def kid04_part503 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 14 (1,true),
.cycle 25 1 false (-3),
.last 16 (1,true),
.cycle 16 1 false (-2),
.cycle 25 1 true (-3),
.last 63 (1,true),
.last 14 (1,true),
.cycle 0 20 true (-1),
.cycle 0 15 true (-1),
.cycle 15 1 true (1),
.cycle 15 1 true (3),
.cycle 9 7 false (1),
.last 14 (1,true),
.cycle 0 39 true (-3),
.cycle 5 9 false (3),
.cycle 16 1 false (-2),
.cycle 14 3 false (0),
.last 27 (1,true),
.last 14 (1,true),
.cycle 2 15 false (3),
.cycle 0 15 true (-1),
.cycle 9 13 false (2),
.cycle 15 1 true (3)
])
theorem kid04_part503_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part503) = true := by rfl

def kid04_part479 : Audit := .split 11 (5,false) (byMove [(kid04_part480),(kid04_part481),(kid04_part482),(kid04_part483),(kid04_part484),(kid04_part485),(kid04_part486),(kid04_part487),(kid04_part488),(kid04_part489),(kid04_part490),(kid04_part491),(kid04_part492),(kid04_part493),(kid04_part494),(kid04_part495),(kid04_part496),(kid04_part497),(kid04_part498),(kid04_part499),(kid04_part500),(kid04_part501),(kid04_part502),(kid04_part503)])

theorem kid04_part479_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part479) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part480),(kid04_part481),(kid04_part482),(kid04_part483),(kid04_part484),(kid04_part485),(kid04_part486),(kid04_part487),(kid04_part488),(kid04_part489),(kid04_part490),(kid04_part491),(kid04_part492),(kid04_part493),(kid04_part494),(kid04_part495),(kid04_part496),(kid04_part497),(kid04_part498),(kid04_part499),(kid04_part500),(kid04_part501),(kid04_part502),(kid04_part503)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part480_checked

  · exact kid04_part486_checked

  · exact kid04_part492_checked

  · exact kid04_part498_checked

  · exact kid04_part481_checked

  · exact kid04_part487_checked

  · exact kid04_part493_checked

  · exact kid04_part499_checked

  · exact kid04_part482_checked

  · exact kid04_part488_checked

  · exact kid04_part494_checked

  · exact kid04_part500_checked

  · exact kid04_part483_checked

  · exact kid04_part489_checked

  · exact kid04_part495_checked

  · exact kid04_part501_checked

  · exact kid04_part484_checked

  · exact kid04_part490_checked

  · exact kid04_part496_checked

  · exact kid04_part502_checked

  · exact kid04_part485_checked

  · exact kid04_part491_checked

  · exact kid04_part497_checked

  · exact kid04_part503_checked

def kid04_part504 : Audit := .cycle 13 1 false (1)
theorem kid04_part504_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part504) = true := by rfl

def kid04_part505 : Audit := .split 11 (1,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 12, 15, 1, 2, 64, 64],96⟩,
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
.last 15 (5,true),
.cycle 23 1 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 19 true (-1),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 15 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 13, 256, 128, 128, 256, 8, 4, 256, 128, 4096],[4, 256, 8, 1, 2, 4096, 4, 4096, 256, 1, 2, 4096, 4096],4096⟩,
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 14 (5,true)
]),
.cycle 14 1 false (4),
.cycle 20 1 false (4),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
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
.last 15 (5,false),
.cycle 23 1 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (3),
.cycle 17 1 false (5),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 16 1 false (0),
.cycle 25 1 false (3),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.split 12 (5,false) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 16384, 8192, 16384, 512, 4, 16384, 67108872, 33554432, 67108864, 2097152, 256, 1327522765, 512, 33554432, 67108864, 134217728, 2097408, 1327522765, 67108864, 33554432, 67108864, 134217728, 1327522765, 1327522765, 201326592, 1073741824],[4, 16384, 0, 1, 2, 1073741824, 256, 1327522765, 2097408, 64, 128, 1073741824, 1048576, 1073741824, 16384, 262144, 524288, 1073741824, 67108864, 64, 1327522765, 16777216, 33554432, 1073741824, 67108864, 1327522765, 1327522765, 16777216, 33554432, 1073741824, 1073741824],2145204288⟩,
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 11 2 true (0),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 24 1 false (4),
.last 13 (5,true),
.last 15 (5,true),
.cycle 29 1 false (3),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 27 1 false (1),
.last 14 (5,true),
.cycle 25 1 false (3),
.cycle 23 1 false (1),
.cycle 10 20 true (0),
.last 13 (5,true)
]),
.cycle 20 1 false (2),
.cycle 1 12 true (0),
.cycle 21 1 false (3),
.cycle 0 13 true (0),
.cycle 25 3 true (3),
.split 12 (5,true) (byMove [
.cycle 15 1 false (3),
.last 14 (5,false),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 27 (5,false),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 8 5 true (0),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 11 2 true (1),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 24 1 false (2),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid04_part505_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part505) = true := by rfl

def kid04_part506 : Audit := .cycle 12 1 false (0)
theorem kid04_part506_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part506) = true := by rfl

def kid04_part507 : Audit := .cycle 14 1 false (4)
theorem kid04_part507_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part507) = true := by rfl

def kid04_part508 : Audit := .cycle 13 1 false (3)
theorem kid04_part508_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part508) = true := by rfl

def kid04_part510 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.cycle 0 19 false (3),
.cycle 0 17 true (0),
.last 35 (1,true),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 10 31 true (0),
.cycle 16 1 true (2),
.last 18 (1,true),
.cycle 13 4 true (1),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 9 8 true (0),
.cycle 11 7 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 13, 256, 256, 128, 256, 8, 4, 256, 256, 4096],[4, 4096, 8, 1, 32, 256, 4, 4096, 256, 1, 32, 8, 4096],4096⟩,
.cycle 29 1 false (1),
.cycle 0 20 true (0),
.cycle 16 1 true (2)
])
theorem kid04_part510_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part510) = true := by rfl

def kid04_part511 : Audit := .cycle 0 15 true (0)
theorem kid04_part511_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part511) = true := by rfl

def kid04_part512 : Audit := .cycle 13 1 false (1)
theorem kid04_part512_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part512) = true := by rfl

def kid04_part513 : Audit := .cycle 12 1 false (0)
theorem kid04_part513_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part513) = true := by rfl

def kid04_part514 : Audit := .cycle 12 1 false (0)
theorem kid04_part514_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part514) = true := by rfl

def kid04_part515 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 14 (1,true),
.cycle 24 1 false (4),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 true (1),
.last 14 (1,true),
.cycle 12 4 true (-1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 14 (1,true),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.cycle 17 1 true (-1)
])
theorem kid04_part515_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part515) = true := by rfl

def kid04_part516 : Audit := .cycle 14 1 false (4)
theorem kid04_part516_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part516) = true := by rfl

def kid04_part517 : Audit := .split 12 (1,true) (byMove [
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
.cycle 17 1 false (1),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (3),
.cycle 17 1 false (5),
.cycle 23 1 false (5),
.last 13 (5,false)
])
theorem kid04_part517_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part517) = true := by rfl

def kid04_part518 : Audit := .cycle 13 1 false (1)
theorem kid04_part518_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part518) = true := by rfl

def kid04_part519 : Audit := .cycle 0 13 true (0)
theorem kid04_part519_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part519) = true := by rfl

def kid04_part520 : Audit := .split 13 (5,false) (byMove [
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
.last 15 (1,true),
.cycle 12 4 true (2),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.cycle 13 1 true (3)
])
theorem kid04_part520_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part520) = true := by rfl

def kid04_part521 : Audit := .split 13 (5,false) (byMove [
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
.last 15 (1,true),
.cycle 13 4 true (2),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 18 1 false (6),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part521_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part521) = true := by rfl

def kid04_part522 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.last 15 (5,false),
.cycle 11 3 false (1),
.cycle 23 1 false (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 262144, 128, 256, 32768, 4, 8192, 262144, 128, 256, 8, 256, 2, 262144, 262144],[4, 2, 256, 1, 32, 8192, 16384, 8192, 262144, 4096, 131072, 256, 4, 2, 256, 1, 32, 8192, 262144],412204⟩,
.cycle 27 1 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false),
.cycle 16 1 false (0),
.last 18 (5,false),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 10 4 true (0),
.cycle 11 3 false (1),
.cycle 0 31 true (0),
.cycle 1 14 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 22 (5,false)
])
theorem kid04_part522_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part522) = true := by rfl

def kid04_part523 : Audit := .split 15 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 18 1 false (4),
.last 16 (1,true),
.cycle 17 1 false (1),
.cycle 0 17 true (0),
.cycle 18 1 false (4),
.cycle 20 1 true (2),
.last 17 (1,true),
.cycle 12 4 true (0),
.cycle 20 1 false (4),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 24 1 false (2),
.last 16 (1,true),
.cycle 25 1 false (3),
.cycle 0 17 true (0),
.cycle 16 7 true (2),
.last 17 (1,true)
])
theorem kid04_part523_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part523) = true := by rfl

def kid04_part524 : Audit := .cycle 16 1 false (4)
theorem kid04_part524_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part524) = true := by rfl

def kid04_part525 : Audit := .cycle 12 1 false (0)
theorem kid04_part525_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part525) = true := by rfl

def kid04_part526 : Audit := .cycle 12 1 false (0)
theorem kid04_part526_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part526) = true := by rfl

def kid04_part527 : Audit := .split 12 (5,false) (byMove [
.cycle 50 1 false (0),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.last 13 (1,true),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 18 1 false (4),
.cycle 11 2 true (0),
.last 14 (1,true),
.cycle 12 4 true (-1),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 27 1 false (1),
.last 13 (1,true),
.cycle 25 1 false (3),
.cycle 23 1 false (1),
.cycle 13 6 true (1),
.cycle 11 3 false (1)
])
theorem kid04_part527_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part527) = true := by rfl

def kid04_part528 : Audit := .cycle 20 1 false (2)
theorem kid04_part528_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part528) = true := by rfl

def kid04_part529 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (3),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 262144, 128, 256, 32768, 4, 128, 262144, 128, 256, 8, 256, 8192, 262144, 262144],[4, 2, 256, 1, 32, 128, 16384, 8192, 262144, 4096, 131072, 128, 4, 2, 256, 1, 32, 128, 262144],412204⟩,
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 8 5 true (0),
.last 13 (5,false),
.cycle 15 1 false (1),
.last 17 (5,false),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 1 14 true (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 24 1 false (2),
.cycle 1 15 true (0),
.last 13 (5,false)
])
theorem kid04_part529_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part529) = true := by rfl

def kid04_part530 : Audit := .split 14 (5,false) (byMove [
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
.last 16 (1,true),
.cycle 12 4 true (1),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (3),
.cycle 19 1 false (5),
.cycle 24 1 false (4),
.cycle 14 1 true (2)
])
theorem kid04_part530_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part530) = true := by rfl

def kid04_part531 : Audit := .cycle 0 13 true (0)
theorem kid04_part531_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part531) = true := by rfl

def kid04_part532 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (2),
.cycle 18 1 false (4),
.cycle 14 3 true (1),
.cycle 15 3 true (1),
.cycle 0 14 true (0),
.cycle 10 17 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 19 3 true (3),
.cycle 13 1 true (3),
.last 15 (1,true),
.cycle 12 4 true (2),
.cycle 0 16 true (0),
.cycle 18 1 false (2),
.cycle 9 5 true (0),
.cycle 16 3 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 25 3 true (3),
.cycle 26 1 false (2),
.cycle 14 3 true (3),
.cycle 13 1 true (3)
])
theorem kid04_part532_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part532) = true := by rfl

def kid04_part533 : Audit := .split 13 (5,false) (byMove [
.cycle 22 1 false (2),
.last 14 (1,true),
.cycle 18 1 false (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 11 15 true (1),
.cycle 24 20 true (2),
.cycle 3 11 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 22 1 false (2),
.last 14 (1,true),
.cycle 21 1 false (5),
.cycle 24 1 false (2),
.cycle 12 3 true (2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 16 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part533_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part533) = true := by rfl

def kid04_part509 : Audit := .split 11 (5,true) (byMove [(kid04_part510),(kid04_part511),(kid04_part512),(kid04_part513),(kid04_part514),(kid04_part515),(kid04_part516),(kid04_part517),(kid04_part518),(kid04_part519),(kid04_part520),(kid04_part521),(kid04_part522),(kid04_part523),(kid04_part524),(kid04_part525),(kid04_part526),(kid04_part527),(kid04_part528),(kid04_part529),(kid04_part530),(kid04_part531),(kid04_part532),(kid04_part533)])

theorem kid04_part509_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part509) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part510),(kid04_part511),(kid04_part512),(kid04_part513),(kid04_part514),(kid04_part515),(kid04_part516),(kid04_part517),(kid04_part518),(kid04_part519),(kid04_part520),(kid04_part521),(kid04_part522),(kid04_part523),(kid04_part524),(kid04_part525),(kid04_part526),(kid04_part527),(kid04_part528),(kid04_part529),(kid04_part530),(kid04_part531),(kid04_part532),(kid04_part533)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part510_checked

  · exact kid04_part516_checked

  · exact kid04_part522_checked

  · exact kid04_part528_checked

  · exact kid04_part511_checked

  · exact kid04_part517_checked

  · exact kid04_part523_checked

  · exact kid04_part529_checked

  · exact kid04_part512_checked

  · exact kid04_part518_checked

  · exact kid04_part524_checked

  · exact kid04_part530_checked

  · exact kid04_part513_checked

  · exact kid04_part519_checked

  · exact kid04_part525_checked

  · exact kid04_part531_checked

  · exact kid04_part514_checked

  · exact kid04_part520_checked

  · exact kid04_part526_checked

  · exact kid04_part532_checked

  · exact kid04_part515_checked

  · exact kid04_part521_checked

  · exact kid04_part527_checked

  · exact kid04_part533_checked

def kid04_part534 : Audit := .split 12 (1,true) (byMove [
.cycle 18 1 false (4),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 20 true (-1),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 52 1 false (-4),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 0 20 true (-1),
.cycle 0 23 true (-1),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 11 3 false (0),
.cycle 10 6 false (0),
.cycle 0 26 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 37 1 false (-1),
.cycle 19 1 false (-1),
.cycle 26 1 false (0),
.cycle 18 1 false (0),
.cycle 9 5 false (1),
.last 14 (5,false)
]),
.cycle 6 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 2, 15, 1, 15, 64, 64],96⟩,
.cycle 9 5 false (1),
.cycle 24 1 false (0),
.cycle 36 1 false (-2),
.split 13 (5,true) (byMove [
.cycle 38 1 false (-2),
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 0 19 true (-1),
.cycle 9 5 false (1),
.last 14 (5,false),
.cycle 24 1 false (0),
.last 15 (5,false),
.cycle 7 7 false (3),
.cycle 0 15 true (-1),
.last 17 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 19 1 false (-1),
.cycle 26 1 false (0),
.cycle 18 1 false (0),
.cycle 9 5 false (1),
.last 14 (5,false),
.cycle 293 1 false (-5),
.last 15 (5,false),
.last 18 (5,false),
.cycle 0 15 true (-1),
.cycle 6 9 false (3),
.last 15 (5,false)
]),
.cycle 15 1 false (-1),
.cycle 10 6 false (0),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 10 3 false (0),
.split 13 (5,true) (byMove [
.cycle 20 1 false (-2),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 16 1 false (0),
.last 15 (5,false),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.last 17 (5,false),
.cycle 11 3 false (0),
.cycle 10 6 false (0),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.last 14 (5,false),
.cycle 9 7 false (1),
.cycle 12 2 true (-1),
.cycle 10 5 false (0),
.cycle 5 9 false (3),
.cycle 17 1 false (-1),
.last 17 (5,false)
]),
.cycle 19 1 false (-1),
.cycle 31 1 false (-1),
.cycle 17 1 false (-1),
.cycle 63 1 false (-3),
.cycle 9 7 false (1),
.split 13 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 15 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 63 1 false (-3),
.last 15 (5,false),
.cycle 19 1 false (-1),
.cycle 0 15 true (-1),
.last 17 (5,false),
.last 15 (5,false),
.cycle 9 7 false (1),
.cycle 12 2 true (0),
.last 18 (5,false),
.cycle 5 9 false (3),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 27 1 false (-1),
.last 15 (5,false),
.cycle 34 1 false (-2),
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.last 15 (5,false)
])
])
theorem kid04_part534_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part534) = true := by rfl

def kid04_part535 : Audit := .cycle 10 3 false (0)
theorem kid04_part535_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part535) = true := by rfl

def kid04_part536 : Audit := .cycle 15 1 false (1)
theorem kid04_part536_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part536) = true := by rfl

def kid04_part537 : Audit := .cycle 11 1 false (-1)
theorem kid04_part537_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part537) = true := by rfl

def kid04_part538 : Audit := .cycle 11 1 false (-1)
theorem kid04_part538_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part538) = true := by rfl

def kid04_part540 : Audit := .split 16 (5,true) (byMove [
.cycle 12 5 false (0),
.last 21 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.last 23 (1,true),
.cycle 22 1 false (4),
.last 17 (1,true),
.cycle 18 1 false (-2),
.last 19 (1,true),
.cycle 10 7 false (0),
.cycle 0 33 true (-2),
.last 18 (1,true),
.cycle 10 9 false (0),
.cycle 24 1 false (4),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.cycle 11 6 false (0),
.cycle 31 1 false (-1),
.last 17 (1,true),
.cycle 10 8 false (0),
.last 19 (1,true),
.cycle 15 2 true (-2),
.cycle 33 1 false (-1)
])
theorem kid04_part540_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part540) = true := by rfl

def kid04_part541 : Audit := .cycle 8 10 false (2)
theorem kid04_part541_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part541) = true := by rfl

def kid04_part542 : Audit := .cycle 13 1 false (-1)
theorem kid04_part542_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part542) = true := by rfl

def kid04_part543 : Audit := .cycle 12 1 false (-2)
theorem kid04_part543_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part543) = true := by rfl

def kid04_part544 : Audit := .cycle 12 1 false (-2)
theorem kid04_part544_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part544) = true := by rfl

def kid04_part545 : Audit := .cycle 11 1 false (-1)
theorem kid04_part545_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part545) = true := by rfl

def kid04_part546 : Audit := .cycle 14 1 false (0)
theorem kid04_part546_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part546) = true := by rfl

def kid04_part547 : Audit := .split 12 (1,true) (byMove [
.last 17 (5,true),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 23 true (-1),
.cycle 15 1 false (1),
.cycle 22 1 false (4),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 19 1 false (3),
.last 13 (5,true),
.cycle 17 1 false (-1),
.cycle 10 5 false (0),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 27 1 false (1),
.last 25 (5,true),
.cycle 0 19 true (-1),
.cycle 23 1 false (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid04_part547_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part547) = true := by rfl

def kid04_part548 : Audit := .cycle 13 1 false (-1)
theorem kid04_part548_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part548) = true := by rfl

def kid04_part549 : Audit := .cycle 15 1 false (1)
theorem kid04_part549_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part549) = true := by rfl

def kid04_part550 : Audit := .cycle 10 2 true (-1)
theorem kid04_part550_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part550) = true := by rfl

def kid04_part551 : Audit := .split 12 (5,true) (byMove [
.cycle 12 5 false (1),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 19 1 true (1),
.cycle 15 1 false (1),
.last 13 (1,true),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 19 1 false (3),
.cycle 15 1 true (3),
.last 14 (1,true),
.cycle 10 5 false (0),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 27 1 false (1),
.last 13 (1,true),
.cycle 0 19 true (-1),
.cycle 23 1 false (1),
.cycle 12 2 true (0),
.cycle 15 1 true (3)
])
theorem kid04_part551_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part551) = true := by rfl

def kid04_part552 : Audit := .split 13 (1,true) (byMove [
.cycle 19 1 false (1),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 0 24 true (-2),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 6 8 false (3),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 128, 8192, 16384, 512, 4, 128, 524288, 33554432, 67108864, 2097152, 256, 1107296256, 16384, 33554432, 67108864, 134217728, 16384, 1107296256, 33554432, 33554432, 67108864, 134217728, 1325400064, 1325400064, 1325400064, 1073741824],[4, 2, 0, 1, 128, 1073741824, 256, 128, 16384, 64, 1107296256, 1073741824, 1048576, 524288, 1140850688, 262144, 1073741824, 1073741824, 67108864, 33554432, 1140850688, 16777216, 1140850688, 1073741824, 67108864, 33554432, 1325400064, 16777216, 1325400064, 1073741824, 1073741824],2145204288⟩,
.cycle 9 6 false (1),
.cycle 8 10 false (2),
.cycle 18 1 false (-2),
.last 14 (5,true),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 18 (5,true),
.last 27 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part552_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part552) = true := by rfl

def kid04_part553 : Audit := .cycle 10 4 false (0)
theorem kid04_part553_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part553) = true := by rfl

def kid04_part554 : Audit := .cycle 16 1 false (0)
theorem kid04_part554_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part554) = true := by rfl

def kid04_part555 : Audit := .cycle 12 1 false (-2)
theorem kid04_part555_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part555) = true := by rfl

def kid04_part556 : Audit := .cycle 12 1 false (-2)
theorem kid04_part556_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part556) = true := by rfl

def kid04_part557 : Audit := .cycle 11 1 false (-1)
theorem kid04_part557_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part557) = true := by rfl

def kid04_part558 : Audit := .cycle 9 5 false (1)
theorem kid04_part558_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part558) = true := by rfl

def kid04_part559 : Audit := .split 12 (1,true) (byMove [
.cycle 18 1 false (4),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 20 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 6 7 false (3),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 128, 8192, 16384, 512, 4, 128, 8192, 33554432, 67108864, 2097152, 256, 1107296256, 33554432, 33554432, 67108864, 134217728, 16384, 1107296256, 33554432, 33554432, 67108864, 134217728, 1140850688, 1107296256, 33554432, 1073741824],[4, 2, 0, 1, 128, 1073741824, 256, 128, 16384, 64, 1074266112, 1073741824, 1048576, 524288, 1140850688, 262144, 1073741824, 1073741824, 67108864, 33554432, 1140850688, 16777216, 33554432, 1073741824, 67108864, 33554432, 1140850688, 16777216, 1107296256, 1073741824, 1073741824],2145335360⟩,
.cycle 9 5 false (1),
.cycle 24 1 false (0),
.last 22 (5,true),
.last 13 (5,true),
.cycle 15 1 false (-1),
.cycle 10 6 false (0),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 17 (5,true),
.last 25 (5,true),
.last 15 (5,true),
.last 61 (5,true),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid04_part559_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part559) = true := by rfl

def kid04_part560 : Audit := .cycle 10 3 false (0)
theorem kid04_part560_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part560) = true := by rfl

def kid04_part561 : Audit := .cycle 5 7 false (3)
theorem kid04_part561_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part561) = true := by rfl

def kid04_part562 : Audit := .split 13 (5,true) (byMove [
.cycle 12 5 false (0),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 9 6 false (1),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.cycle 14 8 true (0),
.last 15 (1,true),
.cycle 10 6 false (0),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (0),
.cycle 9 7 false (1),
.last 14 (1,true),
.cycle 10 5 false (0),
.cycle 5 9 false (3),
.cycle 12 2 true (-1),
.cycle 14 6 true (0)
])
theorem kid04_part562_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part562) = true := by rfl

def kid04_part563 : Audit := .split 12 (5,true) (byMove [
.cycle 18 1 false (4),
.last 13 (1,true),
.cycle 14 1 false (-2),
.last 15 (1,true),
.cycle 10 3 false (0),
.cycle 32 1 true (-4),
.cycle 6 7 false (3),
.last 13 (1,true),
.cycle 9 5 false (1),
.cycle 24 1 false (0),
.cycle 10 13 true (-1),
.cycle 15 1 true (3),
.cycle 15 1 false (-1),
.last 13 (1,true),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 10 3 false (0),
.cycle 11 3 false (0),
.cycle 3 24 false (3),
.last 13 (1,true),
.cycle 2 18 false (3),
.cycle 41 21 false (4),
.cycle 12 2 true (0),
.cycle 15 1 true (3)
])
theorem kid04_part563_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part563) = true := by rfl

def kid04_part539 : Audit := .split 11 (5,false) (byMove [(kid04_part540),(kid04_part541),(kid04_part542),(kid04_part543),(kid04_part544),(kid04_part545),(kid04_part546),(kid04_part547),(kid04_part548),(kid04_part549),(kid04_part550),(kid04_part551),(kid04_part552),(kid04_part553),(kid04_part554),(kid04_part555),(kid04_part556),(kid04_part557),(kid04_part558),(kid04_part559),(kid04_part560),(kid04_part561),(kid04_part562),(kid04_part563)])

theorem kid04_part539_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part539) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part540),(kid04_part541),(kid04_part542),(kid04_part543),(kid04_part544),(kid04_part545),(kid04_part546),(kid04_part547),(kid04_part548),(kid04_part549),(kid04_part550),(kid04_part551),(kid04_part552),(kid04_part553),(kid04_part554),(kid04_part555),(kid04_part556),(kid04_part557),(kid04_part558),(kid04_part559),(kid04_part560),(kid04_part561),(kid04_part562),(kid04_part563)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part540_checked

  · exact kid04_part546_checked

  · exact kid04_part552_checked

  · exact kid04_part558_checked

  · exact kid04_part541_checked

  · exact kid04_part547_checked

  · exact kid04_part553_checked

  · exact kid04_part559_checked

  · exact kid04_part542_checked

  · exact kid04_part548_checked

  · exact kid04_part554_checked

  · exact kid04_part560_checked

  · exact kid04_part543_checked

  · exact kid04_part549_checked

  · exact kid04_part555_checked

  · exact kid04_part561_checked

  · exact kid04_part544_checked

  · exact kid04_part550_checked

  · exact kid04_part556_checked

  · exact kid04_part562_checked

  · exact kid04_part545_checked

  · exact kid04_part551_checked

  · exact kid04_part557_checked

  · exact kid04_part563_checked

def kid04_part564 : Audit := .cycle 23 1 false (1)
theorem kid04_part564_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part564) = true := by rfl

def kid04_part565 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 11 3 false (1),
.cycle 0 19 true (-1),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false)
]),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 2, 64, 64],[4, 2, 4, 1, 2, 64, 64],96⟩,
.cycle 23 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (3),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 1, 3, 4, 1, 3, 3],[128, 256, 8, 0, 0, 1073741824, 128, 256, 32768, 1048836, 131072, 1073741824, 524288, 1048576, 512, 256, 128, 1073741824, 128, 256, 134217728, 1140867072, 536870912, 1073741824, 524288, 1048576, 2097152, 1073741824, 524288, 1073741824, 1073741824],[4, 32, 0, 1, 128, 2, 16384, 131072, 256, 4096, 128, 8192, 256, 2048, 1073741824, 64, 524288, 128, 67108864, 536870912, 256, 16777216, 128, 33554432, 1048576, 8388608, 1073741824, 262144, 524288, 524288, 1073741824],1861381664⟩,
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 1 19 true (0),
.last 13 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 1 26 true (0),
.cycle 25 1 false (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 14 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 15, 15, 1, 2, 64, 64],96⟩,
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 10 2 true (0),
.split 12 (5,true) (byMove [
.cycle 46 1 false (0),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 15 1 false (1),
.last 14 (5,false),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 1 16 true (0),
.last 15 (5,false),
.cycle 11 3 false (1),
.far false 19 ⟨0,[0, 1, 6, 12, 8, 9, 3, 3, 11, 15, 11, 14, 17, 13, 5, 18, 4, 15, 10, 15, 11, 14, 4, 18, 2, 1, 15, 8, 9, 14, 15, 8, 18, 18, 9, 3, 9, 4],[128, 256, 8, 0, 0, 20769187434139310514121985316880384, 9444732965739290427392, 18889465931478580854784, 549755813888, 1125899906842628, 256, 20769187434139310514121985316880384, 36028797018963968, 72057594037927936, 2251799813685248, 32768, 20769187434139310514121985316880384, 20769187434139310514121985316880384, 524288, 1048576, 2097152, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 2475880078570760549798248448, 4951760157141521099596496896, 590295810358705651712, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 38685626227668133590597632, 77371252455336267181195264, 590295810358705651712, 0, 0, 20769187434139310514121985316880384, 604462909807314587353088, 1208925819614629174706176, 40564819207303340847894502572032, 20769192385899467655643084913377280, 18889465931478580854784, 20769187434139310514121985316880384, 649037107316853453566312041152512, 1298074214633706907132624082305024, 8589934592, 0, 0, 20769187434139310514121985316880384, 2475880078570760549798248448, 4951760157141521099596496896, 134217728, 4951760157141802574573207552, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 2475880078570760549798248448, 4951760157141521099596496896, 9223372036854775808, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 38685626227668133590597632, 77371252455336267181195264, 590295810358705651712, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 649037107316853453566312041152512, 1298074214633706907132624082305024, 134217728, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 128, 256, 32768, 20282409603651670423947251286016, 20769187434139310514121985316880384, 20769187434139310514121985316880384, 562949953421312, 1125899906842624, 9903520314283042199192993792, 72057594037927936, 18889465931478580854784, 20769187434139310514121985316880384, 38685626227668133590597632, 77371252455336267181195264, 144115188075855872, 4611686018494496768, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 562949953421312, 1125899906842624, 9903520314283042199192993792, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 649037107316853453566312041152512, 1298074214633706907132624082305024, 2596148429267413814265248164610048, 0, 0, 20769187434139310514121985316880384, 524288, 1048576, 144115188075855872, 21423313829034408751749336724701440, 256, 20769187434139310514121985316880384, 33554432, 67108864, 144115188075855872, 295219962773390753792, 21423313829034408751749336724701440, 20769187434139310514121985316880384, 20769187434139310514121985316880384],[4, 20769187434139310514121985316880384, 0, 1, 128, 18889465931478580854784, 274877906944, 256, 18889465931478580854784, 68719476736, 9444732965739290427392, 20769187434139310514121985316880384, 1125899906842624, 20769187434139310514121985316880384, 20769187434139310514121985316880384, 281474976710656, 36028797018963968, 18889465931478580854784, 1048576, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 262144, 524288, 21423313829034408751749336724701440, 295147905179352825856, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 73786976294838206464, 2475880078570760549798248448, 21423313829034408751749336724701440, 295147905179352825856, 20769187434139310514121985316880384, 0, 73786976294838206464, 38685626227668133590597632, 67108864, 20282409603651670423947251286016, 20769187434139310514121985316880384, 549755813888, 5070602400912917605986812821504, 604462909807314587353088, 256, 4294967296, 0, 0, 1073741824, 649037107316853453566312041152512, 0, 67108864, 21423313829034408751749336724701440, 20769192385899467655643084913377280, 16777216, 2475880078570760549798248448, 21423313829034408751749336724701440, 4611686018427387904, 20769187434139310514121985316880640, 21423313829034408751749336724701440, 1152921504606846976, 2475880078570760549798248448, 21423313829034408751749336724701440, 295147905179352825856, 20769187434139310514121985316880384, 21423313829034408751749336724701440, 73786976294838206464, 38685626227668133590597632, 21423313829034408751749336724701440, 67108864, 20769187434139310514121985316880384, 21423313829034408751749336724701440, 16777216, 649037107316853453566312041152512, 21423313829034408751749336724701440, 16384, 20769187434139310514121985316880384, 256, 4096, 128, 18889465931478580854784, 4951760157141521099596496896, 18889465931478580854784, 1125899906842624, 1237940039285380274899124224, 562949953421312, 20769187434139310514121985316880384, 72057594037927936, 21423313829034408751749336724701440, 77371252455336267181195264, 18014398509481984, 38685626227668133590597632, 21423313829034408751749336724701440, 4951760157141521099596496896, 21423313829034408751749336724701440, 21423313829034408751749336724701440, 1237940039285380274899124224, 562949953421312, 21423313829034408751749336724701440, 1298074214633706907132624082305024, 0, 0, 324518553658426726783156020576256, 649037107316853453566312041152512, 0, 72057594037927936, 20769187434139310514121985316880384, 32768, 18014398509481984, 524288, 1125899906842624, 72057594037927936, 21423313829034408751749336724701440, 67108864, 18014398509481984, 33554432, 20769187434139310514121985383989248, 20769187434139310514121985316880384],41536473387518963573144590070284130⟩,
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 27 1 false (1),
.cycle 11 2 true (0),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.cycle 1 16 true (0),
.last 15 (5,false)
]),
.cycle 0 27 true (0),
.cycle 1 12 true (0),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.split 12 (5,true) (byMove [
.cycle 21 1 false (1),
.last 14 (5,false),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.last 27 (5,false),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.last 13 (5,false),
.last 18 (5,false),
.cycle 11 2 true (1),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 34 true (0),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid04_part565_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part565) = true := by rfl

def kid04_part566 : Audit := .cycle 0 15 true (0)
theorem kid04_part566_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part566) = true := by rfl

def kid04_part567 : Audit := .cycle 21 1 false (1)
theorem kid04_part567_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part567) = true := by rfl

def kid04_part568 : Audit := .cycle 11 3 true (1)
theorem kid04_part568_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part568) = true := by rfl

def kid04_part570 : Audit := .cycle 0 15 true (0)
theorem kid04_part570_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part570) = true := by rfl

def kid04_part571 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid04_part571_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part571) = true := by rfl

def kid04_part572 : Audit := .cycle 13 1 false (-1)
theorem kid04_part572_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part572) = true := by rfl

def kid04_part573 : Audit := .split 14 (1,true) (byMove [
.cycle 17 1 false (3),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 262144, 128, 256, 32768, 4, 128, 262144, 128, 256, 8, 256, 8192, 262144, 262144],[4, 2, 256, 1, 2048, 294912, 16384, 8192, 262144, 4096, 2048, 128, 4, 2, 256, 1, 2048, 8, 262144],412204⟩,
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 8 7 true (0),
.last 15 (5,false),
.cycle 17 1 false (1),
.last 19 (5,false),
.cycle 16 1 false (0),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 26 1 false (2),
.cycle 0 19 true (0),
.last 15 (5,false)
])
theorem kid04_part573_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part573) = true := by rfl

def kid04_part574 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 12 2 true (0),
.cycle 15 1 false (-1),
.cycle 23 1 false (1),
.last 14 (1,true),
.cycle 27 1 false (1),
.cycle 0 15 true (0),
.cycle 8 8 true (0),
.cycle 19 1 true (1),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 2 15 true (0),
.cycle 0 15 true (0),
.cycle 14 5 true (2),
.cycle 16 1 true (2)
])
theorem kid04_part574_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part574) = true := by rfl

def kid04_part575 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 19 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 17 1 true (1),
.last 15 (1,true),
.last 18 (1,true),
.cycle 25 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.proven (BB6.Agent11Raw39Hard56.table) (fun m hm => BB6.Agent11Raw39Hard56.never m hm),
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 0 19 true (-1),
.cycle 9 5 false (1),
.cycle 20 1 true (-2)
])
theorem kid04_part575_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part575) = true := by rfl

def kid04_part576 : Audit := .cycle 21 1 false (1)
theorem kid04_part576_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part576) = true := by rfl

def kid04_part577 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (3),
.last 35 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 262144, 128, 256, 32768, 4, 8192, 262144, 128, 256, 8, 256, 2, 262144, 262144],[4, 2, 256, 1, 2048, 2, 16384, 8192, 262144, 4096, 2048, 8192, 4, 2, 256, 1, 2048, 2, 262144],412204⟩,
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 20 (5,false),
.last 13 (5,false),
.last 43 (5,false),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 9 4 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 27 (5,false),
.cycle 25 1 false (1),
.last 30 (5,false),
.last 13 (5,false)
])
theorem kid04_part577_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part577) = true := by rfl

def kid04_part578 : Audit := .cycle 23 1 false (1)
theorem kid04_part578_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part578) = true := by rfl

def kid04_part579 : Audit := .cycle 0 13 true (0)
theorem kid04_part579_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part579) = true := by rfl

def kid04_part580 : Audit := .split 13 (5,false) (byMove [
.cycle 23 1 false (1),
.last 14 (1,true),
.cycle 8 10 true (0),
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
.last 14 (1,true),
.cycle 8 16 true (0),
.cycle 25 1 false (1),
.cycle 8 8 true (0),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 10 26 true (0),
.cycle 8 9 true (0),
.cycle 13 1 true (3)
])
theorem kid04_part580_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part580) = true := by rfl

def kid04_part581 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 13, 32, 8, 128, 256, 8, 4, 32, 4096, 4096],[4, 4096, 8, 1, 2048, 32, 4, 4096, 4096, 1, 2048, 32, 4096],6144⟩,
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 6 true (0),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 262150, 32, 2, 128, 256, 32768, 4, 131072, 8192, 2, 4, 8, 2, 32, 2, 262144],[4, 262144, 2, 1, 2048, 32, 16384, 262144, 8192, 4096, 2048, 131072, 4, 262144, 2, 1, 32, 32, 262144],289292⟩,
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 13 1 true (3),
.last 15 (1,true),
.last 18 (1,true),
.cycle 0 16 true (0),
.cycle 19 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 4, 64],[4, 64, 4, 1, 32, 32, 64],64⟩,
.cycle 27 1 false (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part581_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part581) = true := by rfl

def kid04_part582 : Audit := .cycle 14 1 false (0)
theorem kid04_part582_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part582) = true := by rfl

def kid04_part583 : Audit := .split 12 (1,true) (byMove [
.last 17 (5,false),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 22 1 false (4),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.last 17 (5,false),
.last 17 (5,false),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 27 1 false (1),
.cycle 1 14 true (0),
.last 15 (5,false),
.cycle 23 1 false (1),
.last 17 (5,false),
.cycle 11 2 true (0)
])
theorem kid04_part583_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part583) = true := by rfl

def kid04_part584 : Audit := .cycle 13 1 false (-1)
theorem kid04_part584_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part584) = true := by rfl

def kid04_part585 : Audit := .cycle 15 1 false (1)
theorem kid04_part585_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part585) = true := by rfl

def kid04_part586 : Audit := .cycle 10 2 true (0)
theorem kid04_part586_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part586) = true := by rfl

def kid04_part587 : Audit := .split 13 (5,false) (byMove [
.cycle 33 1 false (-1),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 10 4 true (-1),
.cycle 12 2 true (-1),
.last 15 (1,true),
.last 18 (1,true),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 9 7 false (1),
.last 14 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 13, 256, 256, 128, 256, 8, 4, 256, 256, 4096],[4, 4096, 8, 1, 2048, 256, 4, 4096, 256, 1, 2048, 256, 4096],4096⟩,
.cycle 5 9 false (3),
.cycle 11 5 false (1),
.cycle 11 3 false (1)
])
theorem kid04_part587_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part587) = true := by rfl

def kid04_part588 : Audit := .cycle 0 27 true (0)
theorem kid04_part588_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part588) = true := by rfl

def kid04_part589 : Audit := .split 12 (1,true) (byMove [
.cycle 21 1 false (1),
.cycle 22 1 false (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 262144, 128, 256, 32768, 4, 128, 262144, 128, 256, 8, 256, 8192, 262144, 262144],[4, 2, 256, 1, 2048, 128, 16384, 8192, 262144, 4096, 2048, 128, 4, 2, 256, 1, 2048, 128, 262144],412204⟩,
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.last 13 (5,false),
.cycle 1 17 true (0),
.last 18 (5,false),
.last 15 (5,false),
.cycle 23 1 false (1),
.cycle 1 14 true (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 34 true (0),
.cycle 1 15 true (0),
.last 13 (5,false)
])
theorem kid04_part589_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part589) = true := by rfl

def kid04_part590 : Audit := .split 14 (5,false) (byMove [
.cycle 23 1 false (1),
.last 15 (1,true),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.cycle 2 14 true (0),
.cycle 0 15 true (0),
.last 30 (1,true),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 8 7 true (0),
.cycle 14 1 true (2),
.cycle 2 18 true (0),
.last 15 (1,true),
.cycle 19 1 false (-1),
.cycle 25 1 false (1),
.cycle 2 15 true (0),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 4 40 true (0),
.cycle 2 16 true (0),
.cycle 14 1 true (2)
])
theorem kid04_part590_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part590) = true := by rfl

def kid04_part591 : Audit := .cycle 0 13 true (0)
theorem kid04_part591_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part591) = true := by rfl

def kid04_part592 : Audit := .split 13 (5,false) (byMove [
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.cycle 14 3 true (2),
.cycle 0 14 true (0),
.cycle 26 3 true (4),
.cycle 28 3 true (3),
.cycle 3 11 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 16 3 true (1),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 5 34 true (0),
.cycle 14 3 true (2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 16 true (1),
.cycle 14 3 true (3),
.cycle 13 1 true (3)
])
theorem kid04_part592_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part592) = true := by rfl

def kid04_part593 : Audit := .split 13 (5,false) (byMove [
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.cycle 13 2 true (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 11 15 true (1),
.cycle 12 18 true (1),
.cycle 3 11 true (0),
.cycle 8 6 true (0),
.cycle 13 1 true (3),
.cycle 12 6 true (1),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 5 34 true (0),
.cycle 12 3 true (2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 16 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3)
])
theorem kid04_part593_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part593) = true := by rfl

def kid04_part569 : Audit := .split 11 (5,true) (byMove [(kid04_part570),(kid04_part571),(kid04_part572),(kid04_part573),(kid04_part574),(kid04_part575),(kid04_part576),(kid04_part577),(kid04_part578),(kid04_part579),(kid04_part580),(kid04_part581),(kid04_part582),(kid04_part583),(kid04_part584),(kid04_part585),(kid04_part586),(kid04_part587),(kid04_part588),(kid04_part589),(kid04_part590),(kid04_part591),(kid04_part592),(kid04_part593)])

theorem kid04_part569_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part569) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part570),(kid04_part571),(kid04_part572),(kid04_part573),(kid04_part574),(kid04_part575),(kid04_part576),(kid04_part577),(kid04_part578),(kid04_part579),(kid04_part580),(kid04_part581),(kid04_part582),(kid04_part583),(kid04_part584),(kid04_part585),(kid04_part586),(kid04_part587),(kid04_part588),(kid04_part589),(kid04_part590),(kid04_part591),(kid04_part592),(kid04_part593)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part570_checked

  · exact kid04_part576_checked

  · exact kid04_part582_checked

  · exact kid04_part588_checked

  · exact kid04_part571_checked

  · exact kid04_part577_checked

  · exact kid04_part583_checked

  · exact kid04_part589_checked

  · exact kid04_part572_checked

  · exact kid04_part578_checked

  · exact kid04_part584_checked

  · exact kid04_part590_checked

  · exact kid04_part573_checked

  · exact kid04_part579_checked

  · exact kid04_part585_checked

  · exact kid04_part591_checked

  · exact kid04_part574_checked

  · exact kid04_part580_checked

  · exact kid04_part586_checked

  · exact kid04_part592_checked

  · exact kid04_part575_checked

  · exact kid04_part581_checked

  · exact kid04_part587_checked

  · exact kid04_part593_checked

def kid04_part473 : Audit := .split 10 (4,true) (byMove [(kid04_part474),(kid04_part475),(kid04_part476),(kid04_part477),(kid04_part478),(kid04_part479),(kid04_part504),(kid04_part505),(kid04_part506),(kid04_part507),(kid04_part508),(kid04_part509),(kid04_part534),(kid04_part535),(kid04_part536),(kid04_part537),(kid04_part538),(kid04_part539),(kid04_part564),(kid04_part565),(kid04_part566),(kid04_part567),(kid04_part568),(kid04_part569)])

theorem kid04_part473_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (kid04_part473) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part474),(kid04_part475),(kid04_part476),(kid04_part477),(kid04_part478),(kid04_part479),(kid04_part504),(kid04_part505),(kid04_part506),(kid04_part507),(kid04_part508),(kid04_part509),(kid04_part534),(kid04_part535),(kid04_part536),(kid04_part537),(kid04_part538),(kid04_part539),(kid04_part564),(kid04_part565),(kid04_part566),(kid04_part567),(kid04_part568),(kid04_part569)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part474_checked

  · exact kid04_part504_checked

  · exact kid04_part534_checked

  · exact kid04_part564_checked

  · exact kid04_part475_checked

  · exact kid04_part505_checked

  · exact kid04_part535_checked

  · exact kid04_part565_checked

  · exact kid04_part476_checked

  · exact kid04_part506_checked

  · exact kid04_part536_checked

  · exact kid04_part566_checked

  · exact kid04_part477_checked

  · exact kid04_part507_checked

  · exact kid04_part537_checked

  · exact kid04_part567_checked

  · exact kid04_part478_checked

  · exact kid04_part508_checked

  · exact kid04_part538_checked

  · exact kid04_part568_checked

  · exact kid04_part479_checked

  · exact kid04_part509_checked

  · exact kid04_part539_checked

  · exact kid04_part569_checked

def kid04_part595 : Audit := .cycle 0 13 true (0)
theorem kid04_part595_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part595) = true := by rfl

def kid04_part597 : Audit := .cycle 0 15 true (-1)
theorem kid04_part597_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part597) = true := by rfl

def kid04_part598 : Audit := .cycle 0 38 true (-2)
theorem kid04_part598_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part598) = true := by rfl

def kid04_part599 : Audit := .cycle 12 1 false (0)
theorem kid04_part599_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part599) = true := by rfl

def kid04_part600 : Audit := .cycle 11 1 false (-1)
theorem kid04_part600_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part600) = true := by rfl

def kid04_part601 : Audit := .split 19 (4,true) (byMove [
.last 56 (5,true),
.cycle 8 13 false (2),
.cycle 7 13 false (3),
.cycle 0 21 true (-3),
.cycle 8 13 false (2),
.last 20 (5,true),
.last 32 (5,true),
.cycle 13 34 true (-3),
.last 358 (5,true),
.last 45 (5,true),
.cycle 8 15 false (2),
.cycle 8 23 false (3),
.cycle 40 3 false (-2),
.cycle 8 13 false (2),
.cycle 7 13 false (3),
.cycle 27 13 false (0),
.cycle 8 13 false (2),
.last 20 (5,true),
.cycle 16 16 true (0),
.cycle 13 36 true (-3),
.cycle 8 21 false (3),
.last 63 (5,true),
.last 21 (5,true),
.cycle 8 17 false (2)
])
theorem kid04_part601_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part601) = true := by rfl

def kid04_part602 : Audit := .split 27 (4,true) (byMove [
.last 45 (5,true),
.cycle 1 29 false (3),
.cycle 7 21 false (3),
.cycle 0 29 true (-3),
.cycle 8 21 false (2),
.last 28 (5,true),
.cycle 1 41 false (5),
.last 62 (5,true),
.last 42 (5,true),
.last 130 (5,true),
.cycle 1 31 false (3),
.cycle 1 39 false (3),
.last 57 (5,true),
.cycle 1 29 false (3),
.cycle 7 21 false (3),
.last 47 (5,true),
.cycle 8 21 false (2),
.last 28 (5,true),
.last 39 (5,true),
.last 38 (5,true),
.cycle 1 37 false (3),
.last 46 (5,true),
.last 29 (5,true),
.last 30 (5,true)
])
theorem kid04_part602_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part602) = true := by rfl

def kid04_part603 : Audit := .cycle 0 13 true (0)
theorem kid04_part603_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part603) = true := by rfl

def kid04_part604 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 0 26 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 0 19 true (-2),
.cycle 0 27 true (-2),
.cycle 0 14 true (0),
.cycle 0 26 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 0 19 true (0),
.cycle 0 27 true (0),
.cycle 0 28 true (0),
.cycle 11 3 false (2),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 154 74 true (4),
.cycle 0 18 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 25 true (0),
.cycle 18 1 false (4),
.last 15 (5,true),
.cycle 0 28 true (0)
])
theorem kid04_part604_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part604) = true := by rfl

def kid04_part605 : Audit := .cycle 0 13 true (0)
theorem kid04_part605_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part605) = true := by rfl

def kid04_part606 : Audit := .cycle 11 1 false (1)
theorem kid04_part606_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part606) = true := by rfl

def kid04_part607 : Audit := .split 33 (4,true) (byMove [
.cycle 8 45 true (-2),
.cycle 0 37 true (-2),
.cycle 8 39 true (-2),
.cycle 0 39 true (-2),
.last 35 (5,true),
.cycle 8 35 true (-2),
.cycle 16 18 true (-2),
.cycle 0 40 true (-2),
.cycle 7 27 true (-2),
.cycle 0 35 true (-2),
.cycle 0 40 true (-2),
.last 34 (5,true),
.cycle 8 54 true (-2),
.cycle 49 3 false (-1),
.cycle 14 20 true (-2),
.cycle 8 37 true (-2),
.last 35 (5,true),
.cycle 0 48 true (-2),
.cycle 8 41 true (-2),
.cycle 0 71 true (-2),
.cycle 0 47 true (-2),
.cycle 0 79 true (-2),
.last 36 (5,true),
.last 34 (5,true)
])
theorem kid04_part607_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part607) = true := by rfl

def kid04_part608 : Audit := .cycle 0 15 true (0)
theorem kid04_part608_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part608) = true := by rfl

def kid04_part609 : Audit := .split 23 (4,true) (byMove [
.last 87 (5,true),
.cycle 6 21 false (3),
.cycle 7 17 false (3),
.cycle 0 25 true (-3),
.cycle 8 17 false (2),
.last 24 (5,true),
.last 40 (5,true),
.last 107 (5,true),
.proven (BB6.Agent11Raw39RCPumps.M65.table) (fun m hm => BB6.Agent11Raw39RCPumps.M65.never m hm),
.last 57 (5,true),
.cycle 6 23 false (3),
.cycle 6 31 false (3),
.cycle 12 36 false (4),
.cycle 6 21 false (3),
.cycle 7 17 false (3),
.last 98 (5,true),
.cycle 8 17 false (2),
.last 24 (5,true),
.last 38 (5,true),
.cycle 12 21 true (-3),
.cycle 6 29 false (3),
.last 79 (5,true),
.last 25 (5,true),
.cycle 12 38 false (4)
])
theorem kid04_part609_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part609) = true := by rfl

def kid04_part610 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 1 33 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 38 (5,true),
.cycle 47 32 false (-1),
.cycle 0 18 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 86 54 true (-1),
.cycle 0 37 true (-2),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 24 8 true (-2),
.cycle 14 1 false (-2),
.last 41 (5,true),
.last 22 (5,true),
.cycle 29 7 false (1),
.cycle 0 17 true (-1),
.cycle 0 33 true (-2),
.cycle 0 19 true (-1),
.last 15 (5,true),
.cycle 9 5 false (1)
])
theorem kid04_part610_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part610) = true := by rfl

def kid04_part611 : Audit := .cycle 7 16 false (3)
theorem kid04_part611_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part611) = true := by rfl

def kid04_part612 : Audit := .cycle 11 1 false (-1)
theorem kid04_part612_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part612) = true := by rfl

def kid04_part613 : Audit := .cycle 0 19 true (-3)
theorem kid04_part613_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part613) = true := by rfl

def kid04_part614 : Audit := .split 17 (5,true) (byMove [
.last 21 (4,true),
.cycle 0 21 true (-2),
.cycle 11 15 false (2),
.last 31 (4,true),
.cycle 8 10 false (2),
.cycle 1 18 false (3),
.cycle 11 98 true (-5),
.cycle 0 23 true (-2),
.cycle 0 24 true (-2),
.cycle 0 19 true (-2),
.last 18 (4,true),
.cycle 0 32 true (-2),
.cycle 11 16 false (2),
.last 20 (4,true),
.cycle 11 110 true (-5),
.cycle 11 13 false (2),
.cycle 8 10 false (2),
.cycle 67 42 true (-1),
.cycle 11 16 true (-2),
.cycle 16 2 true (1),
.last 19 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 133, 1, 8, 128, 256, 8, 4, 1, 128, 4096],[4, 1, 128, 1, 4096, 512, 4, 1, 4096, 1, 4096, 512, 4096],4096⟩,
.last 18 (4,true),
.cycle 16 4 true (1)
])
theorem kid04_part614_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part614) = true := by rfl

def kid04_part615 : Audit := .cycle 0 13 true (0)
theorem kid04_part615_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part615) = true := by rfl

def kid04_part616 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.cycle 1 14 true (0),
.cycle 7 27 false (3),
.cycle 0 15 true (0),
.cycle 8 27 false (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 0 26 true (0),
.far true 2 ⟨0,[0, 1, 0, 1],[514, 514, 512, 512, 2048, 2, 514, 514, 514, 512, 2048, 2, 4096],[514, 514, 16, 514, 514, 4096, 2048, 514, 16, 514, 2048, 4096, 4096],4096⟩,
.cycle 0 24 true (-1),
.cycle 8 6 true (0),
.cycle 1 14 true (0),
.cycle 0 21 true (-2),
.cycle 1 15 true (0),
.cycle 18 19 true (-2),
.cycle 17 1 false (3),
.cycle 40 27 false (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 22 68 true (-1),
.last 15 (5,true),
.cycle 1 15 true (0)
])
theorem kid04_part616_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part616) = true := by rfl

def kid04_part617 : Audit := .cycle 0 13 true (0)
theorem kid04_part617_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part617) = true := by rfl

def kid04_part618 : Audit := .cycle 0 20 true (-1)
theorem kid04_part618_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part618) = true := by rfl

def kid04_part619 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 33 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 28 (4,true),
.cycle 0 20 true (-1),
.last 14 (4,true),
.cycle 0 32 true (-2),
.cycle 16 1 false (4),
.last 13 (4,true),
.cycle 0 28 true (0),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 22 true (-1),
.cycle 13 1 false (-1),
.last 29 (4,true),
.cycle 0 24 true (-2),
.last 66 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.last 30 (4,true),
.last 13 (4,true),
.cycle 13 5 true (1)
])
theorem kid04_part619_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part619) = true := by rfl

def kid04_part620 : Audit := .cycle 9 2 true (0)
theorem kid04_part620_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part620) = true := by rfl

def kid04_part596 : Audit := .split 10 (1,true) (byMove [(kid04_part597),(kid04_part598),(kid04_part599),(kid04_part600),(kid04_part601),(kid04_part602),(kid04_part603),(kid04_part604),(kid04_part605),(kid04_part606),(kid04_part607),(kid04_part608),(kid04_part609),(kid04_part610),(kid04_part611),(kid04_part612),(kid04_part613),(kid04_part614),(kid04_part615),(kid04_part616),(kid04_part617),(kid04_part618),(kid04_part619),(kid04_part620)])

theorem kid04_part596_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part596) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part597),(kid04_part598),(kid04_part599),(kid04_part600),(kid04_part601),(kid04_part602),(kid04_part603),(kid04_part604),(kid04_part605),(kid04_part606),(kid04_part607),(kid04_part608),(kid04_part609),(kid04_part610),(kid04_part611),(kid04_part612),(kid04_part613),(kid04_part614),(kid04_part615),(kid04_part616),(kid04_part617),(kid04_part618),(kid04_part619),(kid04_part620)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid04_part600_checked

  · exact kid04_part606_checked

  · exact kid04_part612_checked

  · exact kid04_part618_checked

  · exact kid04_part601_checked

  · exact kid04_part607_checked

  · exact kid04_part613_checked

  · exact kid04_part619_checked

  · exact kid04_part602_checked

  · exact kid04_part608_checked

  · exact kid04_part614_checked

  · exact kid04_part620_checked

def kid04_part621 : Audit := .cycle 14 1 false (-2)
theorem kid04_part621_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part621) = true := by rfl

def kid04_part622 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (3),
.cycle 23 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
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
.cycle 13 3 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (4),
.last 15 (5,true),
.cycle 0 16 true (0)
]),
.split 13 (5,true) (byMove [
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
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (4),
.last 16 (4,true),
.cycle 0 16 true (0)
]),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 8 5 true (0),
.cycle 18 1 false (4),
.cycle 17 1 false (-1),
.split 16 (4,true) (byMove [
.cycle 0 21 true (-1),
.cycle 26 1 false (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 11 6 true (0),
.cycle 29 1 false (1),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 11 6 false (2),
.cycle 14 3 false (1),
.cycle 10 8 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 12 7 false (2),
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.cycle 23 1 false (-1),
.last 18 (5,true),
.cycle 9 8 true (0)
]),
.cycle 16 1 false (-2),
.cycle 16 1 false (4),
.split 13 (4,true) (byMove [
.cycle 20 1 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (4),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.last 14 (5,true),
.cycle 11 3 false (2),
.cycle 13 3 false (1),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 12 2 true (1),
.cycle 24 1 false (0),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
]),
.split 13 (5,true) (byMove [
.last 17 (4,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (4),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 16 1 false (2),
.cycle 11 3 false (2),
.last 16 (4,true),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 12 2 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 17 true (0)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 26 1 false (0),
.split 14 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 33 1 false (-1),
.cycle 18 1 false (-2),
.cycle 10 5 true (0),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 26 1 false (0),
.cycle 12 3 true (2),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 24 1 false (0),
.cycle 19 1 false (-1),
.last 16 (4,true),
.cycle 18 1 false (-2),
.cycle 20 1 false (0),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 13 19 true (1),
.cycle 12 3 true (2),
.last 16 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0)
]),
.cycle 0 15 true (0)
])
theorem kid04_part622_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part622) = true := by rfl

def kid04_part623 : Audit := .split 10 (4,true) (byMove [
.cycle 0 15 true (-1),
.cycle 18 2 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.split 12 (1,true) (byMove [
.cycle 15 1 false (3),
.cycle 21 2 false (1),
.cycle 14 2 false (0),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.last 23 (5,true),
.cycle 20 2 false (2),
.cycle 18 2 false (2),
.cycle 8 5 true (0),
.last 15 (5,true),
.cycle 15 2 false (1),
.cycle 10 6 true (0),
.cycle 14 2 false (0),
.cycle 16 1 false (4),
.cycle 16 1 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 24 2 false (2),
.last 14 (5,true),
.cycle 0 15 true (0)
]),
.cycle 21 2 false (3),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 11 2 false (1),
.split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 21 2 false (-1),
.cycle 14 2 false (-2),
.cycle 20 2 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 0 15 true (-1),
.last 28 (5,true),
.cycle 0 15 true (-1),
.cycle 18 2 false (0),
.cycle 8 5 false (2),
.last 15 (5,true),
.cycle 15 2 false (-1),
.cycle 10 6 false (0),
.cycle 14 2 false (-2),
.cycle 0 17 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 29 (5,true),
.last 19 (5,true),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 14 (5,true),
.cycle 17 2 false (-1)
]),
.cycle 10 3 false (0),
.split 14 (1,true) (byMove [
.cycle 17 1 false (3),
.cycle 23 2 false (1),
.cycle 16 2 false (0),
.cycle 0 16 true (-1),
.cycle 0 18 true (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.last 25 (5,true),
.cycle 22 2 false (2),
.cycle 20 2 false (2),
.cycle 8 7 true (-1),
.last 17 (5,true),
.cycle 17 2 false (1),
.cycle 10 8 true (-1),
.cycle 16 2 false (0),
.cycle 18 1 false (4),
.cycle 20 1 false (4),
.last 15 (5,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 1048580, 1073741824, 128, 33554432, 67108864, 2097152, 128, 64, 1073741824, 33554432, 67108864, 134217728, 64, 1073741824, 128, 33554432, 67108864, 134217728, 1191198912, 1090519104, 1107296384, 1073741824],[4, 64, 0, 1, 1, 1073741824, 16384, 64, 128, 4096, 64, 1073741824, 1048576, 16777216, 1073741824, 262144, 262144, 1073741824, 67108864, 16777216, 128, 16777216, 16777216, 1073741824, 67108864, 16777216, 1107296384, 16777216, 1090519104, 1073741824, 1073741824],2136880640⟩,
.cycle 26 2 false (0),
.cycle 2 13 true (-1),
.cycle 26 2 false (2),
.last 16 (5,true),
.cycle 18 2 false (0)
]),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.split 12 (1,true) (byMove [
.cycle 21 2 false (1),
.cycle 22 2 false (0),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.last 23 (5,true),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.last 15 (5,true),
.last 16 (5,true),
.cycle 10 7 false (2),
.cycle 10 4 true (0),
.cycle 23 2 false (1),
.cycle 0 31 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 34 true (0),
.last 14 (5,true),
.cycle 0 15 true (0)
]),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.cycle 15 2 false (1),
.split 12 (5,true) (byMove [
.cycle 24 1 false (4),
.cycle 26 2 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 15 2 false (1),
.last 13 (1,true),
.cycle 14 2 false (0),
.cycle 16 1 false (4),
.cycle 14 3 true (2),
.cycle 15 2 false (3),
.last 14 (1,true),
.cycle 10 5 false (1),
.cycle 17 2 false (1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 25 2 false (1),
.last 13 (1,true),
.cycle 10 4 true (0),
.cycle 23 2 false (1),
.cycle 14 3 true (2),
.cycle 13 5 true (1)
]),
.cycle 9 2 true (0)
])
theorem kid04_part623_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part623) = true := by rfl

def kid04_part625 : Audit := .cycle 0 15 true (-1)
theorem kid04_part625_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part625) = true := by rfl

def kid04_part626 : Audit := .cycle 19 1 false (-1)
theorem kid04_part626_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part626) = true := by rfl

def kid04_part627 : Audit := .cycle 12 1 false (0)
theorem kid04_part627_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part627) = true := by rfl

def kid04_part628 : Audit := .cycle 11 1 false (-1)
theorem kid04_part628_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part628) = true := by rfl

def kid04_part629 : Audit := .cycle 12 1 false (-2)
theorem kid04_part629_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part629) = true := by rfl

def kid04_part630 : Audit := .cycle 11 1 false (-1)
theorem kid04_part630_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part630) = true := by rfl

def kid04_part631 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (3),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.last 27 (4,true),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 8 5 true (0),
.cycle 0 16 true (0),
.cycle 16 1 false (0),
.last 16 (4,true),
.cycle 15 1 false (-1),
.cycle 16 1 false (4),
.last 13 (4,true),
.cycle 16 1 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 25 1 false (1),
.cycle 25 1 false (1),
.cycle 0 15 true (0)
])
theorem kid04_part631_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part631) = true := by rfl

def kid04_part632 : Audit := .split 13 (4,true) (byMove [
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
.last 15 (1,true),
.cycle 11 3 false (2),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.last 16 (1,true),
.cycle 24 1 false (2)
])
theorem kid04_part632_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part632) = true := by rfl

def kid04_part633 : Audit := .cycle 0 13 true (0)
theorem kid04_part633_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part633) = true := by rfl

def kid04_part634 : Audit := .cycle 11 1 false (1)
theorem kid04_part634_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part634) = true := by rfl

def kid04_part635 : Audit := .cycle 12 1 false (0)
theorem kid04_part635_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part635) = true := by rfl

def kid04_part636 : Audit := .cycle 11 1 false (1)
theorem kid04_part636_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part636) = true := by rfl

def kid04_part637 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.last 17 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 0 15 true (-1),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 8 5 false (2),
.cycle 9 5 false (1),
.cycle 16 1 false (-2),
.last 16 (4,true),
.cycle 15 1 false (-3),
.cycle 0 17 true (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 42 (4,true),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.cycle 18 1 false (-2),
.cycle 18 1 false (-2)
])
theorem kid04_part637_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part637) = true := by rfl

def kid04_part638 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 0 18 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (1,true),
.cycle 11 3 false (0),
.cycle 22 1 false (-2),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 29 (1,true),
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 0 19 true (-1),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
])
theorem kid04_part638_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part638) = true := by rfl

def kid04_part639 : Audit := .split 14 (1,true) (byMove [
.cycle 17 1 false (3),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 0 18 true (-1),
.cycle 0 15 true (-1),
.last 31 (4,true),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 8 7 true (-1),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.last 18 (4,true),
.cycle 17 1 false (-1),
.cycle 18 1 false (4),
.last 15 (4,true),
.cycle 20 1 false (4),
.last 27 (4,true),
.cycle 27 1 false (-1),
.cycle 2 13 true (-1),
.cycle 27 1 false (1),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1)
])
theorem kid04_part639_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part639) = true := by rfl

def kid04_part640 : Audit := .cycle 11 1 false (-1)
theorem kid04_part640_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part640) = true := by rfl

def kid04_part641 : Audit := .cycle 12 1 false (-2)
theorem kid04_part641_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part641) = true := by rfl

def kid04_part642 : Audit := .cycle 11 1 false (-1)
theorem kid04_part642_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part642) = true := by rfl

def kid04_part643 : Audit := .split 12 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.last 27 (4,true),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 5 true (0),
.cycle 0 16 true (0),
.cycle 26 1 false (0),
.last 17 (4,true),
.last 14 (4,true),
.cycle 24 1 false (0),
.last 13 (4,true),
.cycle 0 31 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 34 true (0),
.cycle 13 19 true (1),
.cycle 0 15 true (0)
])
theorem kid04_part643_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part643) = true := by rfl

def kid04_part644 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 0 15 true (0),
.cycle 16 1 false (-2),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 0 28 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 8 6 true (0),
.cycle 1 16 true (0),
.cycle 17 1 false (-1),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 17 1 false (3),
.cycle 16 1 false (-2),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 26 1 false (0),
.last 16 (1,true),
.cycle 1 15 true (0)
])
theorem kid04_part644_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part644) = true := by rfl

def kid04_part645 : Audit := .cycle 0 13 true (0)
theorem kid04_part645_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part645) = true := by rfl

def kid04_part646 : Audit := .cycle 16 1 false (0)
theorem kid04_part646_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part646) = true := by rfl

def kid04_part647 : Audit := .split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 16 (1,true),
.cycle 16 1 false (-2),
.cycle 10 4 true (0),
.cycle 24 1 false (0),
.last 14 (1,true),
.cycle 26 1 false (0),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 14 6 true (2),
.cycle 17 1 false (-1),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 12 2 true (0),
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 2 14 true (0),
.cycle 0 15 true (0),
.cycle 14 3 true (2),
.cycle 14 5 true (2)
])
theorem kid04_part647_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part647) = true := by rfl

def kid04_part648 : Audit := .cycle 9 2 true (0)
theorem kid04_part648_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part648) = true := by rfl

def kid04_part624 : Audit := .split 10 (5,true) (byMove [(kid04_part625),(kid04_part626),(kid04_part627),(kid04_part628),(kid04_part629),(kid04_part630),(kid04_part631),(kid04_part632),(kid04_part633),(kid04_part634),(kid04_part635),(kid04_part636),(kid04_part637),(kid04_part638),(kid04_part639),(kid04_part640),(kid04_part641),(kid04_part642),(kid04_part643),(kid04_part644),(kid04_part645),(kid04_part646),(kid04_part647),(kid04_part648)])

theorem kid04_part624_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part624) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part625),(kid04_part626),(kid04_part627),(kid04_part628),(kid04_part629),(kid04_part630),(kid04_part631),(kid04_part632),(kid04_part633),(kid04_part634),(kid04_part635),(kid04_part636),(kid04_part637),(kid04_part638),(kid04_part639),(kid04_part640),(kid04_part641),(kid04_part642),(kid04_part643),(kid04_part644),(kid04_part645),(kid04_part646),(kid04_part647),(kid04_part648)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part625_checked

  · exact kid04_part631_checked

  · exact kid04_part637_checked

  · exact kid04_part643_checked

  · exact kid04_part626_checked

  · exact kid04_part632_checked

  · exact kid04_part638_checked

  · exact kid04_part644_checked

  · exact kid04_part627_checked

  · exact kid04_part633_checked

  · exact kid04_part639_checked

  · exact kid04_part645_checked

  · exact kid04_part628_checked

  · exact kid04_part634_checked

  · exact kid04_part640_checked

  · exact kid04_part646_checked

  · exact kid04_part629_checked

  · exact kid04_part635_checked

  · exact kid04_part641_checked

  · exact kid04_part647_checked

  · exact kid04_part630_checked

  · exact kid04_part636_checked

  · exact kid04_part642_checked

  · exact kid04_part648_checked

def kid04_part649 : Audit := .cycle 26 1 false (6)
theorem kid04_part649_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part649) = true := by rfl

def kid04_part650 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 15 1 false (3),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.last 16 (4,true),
.cycle 15 1 false (3),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 22 3 false (4),
.last 15 (4,true),
.last 15 (4,true),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 21 3 false (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 17 true (0)
]),
.cycle 1 11 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 8 3 true (1),
.cycle 1 11 true (1),
.split 16 (5,true) (byMove [
.last 20 (4,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 7 false (-1),
.last 20 (4,true),
.cycle 19 1 false (3),
.cycle 17 7 false (1),
.cycle 17 7 false (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 24 7 false (5),
.cycle 17 7 false (0),
.last 19 (4,true),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.cycle 17 7 false (-1),
.cycle 17 7 false (0),
.cycle 23 7 false (2),
.cycle 17 7 false (1),
.last 18 (4,true),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 6 25 true (0)
]),
.split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 18 6 false (0),
.cycle 15 3 false (0),
.cycle 11 13 false (2),
.cycle 17 1 false (3),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.last 15 (5,true),
.cycle 1 14 true (1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 26 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.last 16 (4,true),
.cycle 15 3 false (1),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 16 1 false (4),
.last 13 (4,true),
.cycle 23 3 false (5),
.last 15 (4,true),
.last 15 (4,true),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 25 3 false (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 23 3 false (1),
.last 13 (4,true),
.cycle 12 19 true (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 51 1 false (7),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 13 5 false (1),
.last 16 (4,true),
.cycle 51 1 false (7),
.cycle 10 3 true (2),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 18 (4,true),
.last 15 (4,true),
.cycle 11 17 true (2),
.cycle 10 3 true (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid04_part650_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part650) = true := by rfl

def kid04_part652 : Audit := .split 16 (4,true) (byMove [
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 17 3 false (-1),
.cycle 0 18 true (-1),
.cycle 18 3 false (-2),
.cycle 0 18 false (3),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 8 9 false (2),
.cycle 25 3 false (1),
.cycle 18 3 false (0),
.last 17 (1,true),
.cycle 17 3 false (-1),
.cycle 20 1 false (2),
.cycle 18 3 false (-2),
.cycle 12 5 false (1),
.cycle 0 33 true (-1),
.cycle 0 32 true (-1),
.cycle 2 15 false (3),
.cycle 27 3 false (1),
.cycle 0 22 true (-1),
.cycle 3 17 false (3)
])
theorem kid04_part652_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part652) = true := by rfl

def kid04_part653 : Audit := .cycle 0 16 true (-1)
theorem kid04_part653_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part653) = true := by rfl

def kid04_part654 : Audit := .cycle 14 1 false (0)
theorem kid04_part654_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part654) = true := by rfl

def kid04_part655 : Audit := .cycle 13 1 false (-1)
theorem kid04_part655_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part655) = true := by rfl

def kid04_part656 : Audit := .cycle 13 3 false (-1)
theorem kid04_part656_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part656) = true := by rfl

def kid04_part657 : Audit := .cycle 0 16 true (-1)
theorem kid04_part657_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part657) = true := by rfl

def kid04_part658 : Audit := .cycle 15 1 false (3)
theorem kid04_part658_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part658) = true := by rfl

def kid04_part659 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 16 1 false (2),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 3 false (2),
.cycle 16 1 false (4),
.cycle 17 3 false (1),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 14 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 18 1 false (4),
.cycle 11 3 true (0),
.cycle 21 3 false (3)
])
theorem kid04_part659_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part659) = true := by rfl

def kid04_part660 : Audit := .cycle 13 3 false (1)
theorem kid04_part660_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part660) = true := by rfl

def kid04_part661 : Audit := .cycle 0 14 true (0)
theorem kid04_part661_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part661) = true := by rfl

def kid04_part662 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 16 1 false (2),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 3 false (2),
.cycle 16 1 false (4),
.last 15 (1,true),
.cycle 13 3 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 3 false (0),
.cycle 14 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 18 1 false (4),
.cycle 11 3 true (0),
.cycle 21 3 false (3)
])
theorem kid04_part662_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part662) = true := by rfl

def kid04_part663 : Audit := .cycle 16 1 false (4)
theorem kid04_part663_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part663) = true := by rfl

def kid04_part664 : Audit := .split 14 (1,true) (byMove [
.cycle 0 18 true (-1),
.cycle 22 3 false (0),
.cycle 15 3 false (-1),
.cycle 0 19 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 23 3 false (1),
.cycle 7 21 false (4),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 82 3 false (-2),
.cycle 16 3 false (0),
.last 18 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 3 15 false (3),
.last 37 (4,true),
.last 16 (4,true),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 10 7 false (2)
])
theorem kid04_part664_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part664) = true := by rfl

def kid04_part665 : Audit := .split 15 (4,true) (byMove [
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 3 false (-2),
.cycle 18 1 false (0),
.last 17 (1,true),
.cycle 25 3 false (3),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 16 3 false (0),
.cycle 16 3 false (1),
.last 17 (1,true),
.cycle 13 3 false (0),
.last 19 (1,true),
.cycle 16 1 false (-2),
.cycle 16 3 false (-2),
.cycle 16 3 false (-1),
.last 17 (1,true),
.last 31 (1,true),
.cycle 0 18 true (-1),
.cycle 19 3 false (1),
.cycle 11 5 false (1),
.cycle 9 7 false (2)
])
theorem kid04_part665_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part665) = true := by rfl

def kid04_part666 : Audit := .cycle 17 1 false (3)
theorem kid04_part666_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part666) = true := by rfl

def kid04_part667 : Audit := .cycle 13 1 false (-1)
theorem kid04_part667_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part667) = true := by rfl

def kid04_part668 : Audit := .cycle 13 3 false (-1)
theorem kid04_part668_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part668) = true := by rfl

def kid04_part669 : Audit := .cycle 13 3 false (0)
theorem kid04_part669_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part669) = true := by rfl

def kid04_part670 : Audit := .cycle 20 3 false (2)
theorem kid04_part670_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part670) = true := by rfl

def kid04_part671 : Audit := .split 13 (1,true) (byMove [
.cycle 16 1 false (2),
.cycle 21 3 false (1),
.cycle 14 3 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 8 6 true (0),
.cycle 22 3 false (2),
.cycle 15 3 false (1),
.last 17 (4,true),
.cycle 14 3 false (0),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 24 3 false (2),
.cycle 11 3 true (0),
.cycle 0 31 true (0)
])
theorem kid04_part671_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part671) = true := by rfl

def kid04_part672 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (-1),
.cycle 17 1 false (1),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (1),
.cycle 17 1 false (3),
.last 16 (1,true),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (-1),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 19 1 false (3),
.cycle 11 4 true (0),
.cycle 22 3 false (2)
])
theorem kid04_part672_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part672) = true := by rfl

def kid04_part673 : Audit := .cycle 0 14 true (0)
theorem kid04_part673_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part673) = true := by rfl

def kid04_part674 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 14 3 false (0),
.cycle 0 15 true (0),
.cycle 15 3 false (-1),
.cycle 11 4 true (0),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 8 6 true (0),
.cycle 22 3 false (2),
.cycle 15 3 false (1),
.last 14 (1,true),
.cycle 14 3 false (0),
.cycle 17 1 false (3),
.cycle 15 3 false (-1),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 24 3 false (2),
.cycle 11 3 true (0),
.cycle 0 31 true (0)
])
theorem kid04_part674_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part674) = true := by rfl

def kid04_part675 : Audit := .cycle 0 31 true (0)
theorem kid04_part675_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part675) = true := by rfl

def kid04_part651 : Audit := .split 12 (5,true) (byMove [(kid04_part652),(kid04_part653),(kid04_part654),(kid04_part655),(kid04_part656),(kid04_part657),(kid04_part658),(kid04_part659),(kid04_part660),(kid04_part661),(kid04_part662),(kid04_part663),(kid04_part664),(kid04_part665),(kid04_part666),(kid04_part667),(kid04_part668),(kid04_part669),(kid04_part670),(kid04_part671),(kid04_part672),(kid04_part673),(kid04_part674),(kid04_part675)])

theorem kid04_part651_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part651) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid04_part652),(kid04_part653),(kid04_part654),(kid04_part655),(kid04_part656),(kid04_part657),(kid04_part658),(kid04_part659),(kid04_part660),(kid04_part661),(kid04_part662),(kid04_part663),(kid04_part664),(kid04_part665),(kid04_part666),(kid04_part667),(kid04_part668),(kid04_part669),(kid04_part670),(kid04_part671),(kid04_part672),(kid04_part673),(kid04_part674),(kid04_part675)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part652_checked

  · exact kid04_part658_checked

  · exact kid04_part664_checked

  · exact kid04_part670_checked

  · exact kid04_part653_checked

  · exact kid04_part659_checked

  · exact kid04_part665_checked

  · exact kid04_part671_checked

  · exact kid04_part654_checked

  · exact kid04_part660_checked

  · exact kid04_part666_checked

  · exact kid04_part672_checked

  · exact kid04_part655_checked

  · exact kid04_part661_checked

  · exact kid04_part667_checked

  · exact kid04_part673_checked

  · exact kid04_part656_checked

  · exact kid04_part662_checked

  · exact kid04_part668_checked

  · exact kid04_part674_checked

  · exact kid04_part657_checked

  · exact kid04_part663_checked

  · exact kid04_part669_checked

  · exact kid04_part675_checked

def kid04_part676 : Audit := .cycle 0 11 true (0)
theorem kid04_part676_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part676) = true := by rfl

def kid04_part677 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 15 1 false (3),
.split 12 (5,true) (byMove [
.cycle 17 3 false (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 14 3 false (0),
.cycle 15 1 false (3),
.last 13 (1,true),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.cycle 15 3 false (3),
.last 14 (1,true),
.cycle 15 3 false (-1),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 21 3 false (1),
.last 13 (1,true),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.cycle 8 7 true (0)
]),
.cycle 8 4 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 8 3 true (1),
.cycle 8 4 true (1),
.split 12 (1,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 13 false (1),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 8 6 true (1),
.last 16 (5,true),
.cycle 13 6 false (1),
.cycle 14 6 false (0),
.cycle 34 1 false (6),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.last 14 (5,true),
.cycle 8 6 true (1)
]),
.split 14 (1,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 3 false (-1),
.cycle 18 3 false (0),
.cycle 17 1 false (3),
.cycle 25 3 false (3),
.cycle 18 3 false (0),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.last 15 (5,true),
.cycle 21 3 false (-1),
.cycle 15 3 false (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 17 3 false (-1),
.cycle 16 3 false (0),
.cycle 25 3 false (1),
.cycle 1 15 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 17 3 false (-1),
.cycle 26 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 14 3 false (0),
.cycle 15 3 false (1),
.last 13 (1,true),
.cycle 14 3 false (0),
.cycle 16 1 false (4),
.cycle 13 3 false (1),
.cycle 16 3 false (4),
.last 14 (1,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 25 3 false (1),
.last 13 (1,true),
.cycle 14 3 false (0),
.cycle 23 3 false (1),
.cycle 14 3 false (0),
.cycle 8 8 true (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 51 1 false (7),
.split 12 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 13 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 51 1 false (7),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 8 7 true (1),
.last 14 (1,true),
.last 18 (1,true),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 19 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 11 17 true (2),
.last 13 (1,true),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 8 7 true (1)
]),
.cycle 8 4 true (1)
])
theorem kid04_part677_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part677) = true := by rfl

def kid04_part678 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 15 1 false (3),
.cycle 12 3 false (0),
.cycle 11 1 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 8 3 true (1),
.cycle 11 1 true (3),
.split 12 (1,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 13 false (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 13 1 true (3),
.cycle 16 7 false (0),
.last 17 (4,true),
.last 14 (4,true),
.cycle 34 1 false (6),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.last 21 (4,true),
.cycle 13 1 true (3)
]),
.split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.cycle 18 1 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 14 1 true (2),
.last 23 (1,true),
.last 14 (1,true),
.cycle 11 13 false (2),
.cycle 17 1 false (3),
.cycle 14 6 false (0),
.cycle 14 5 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.last 16 (1,true),
.cycle 14 1 true (2)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 12 3 false (0),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 51 1 false (7),
.split 13 (4,true) (byMove [
.cycle 34 1 false (6),
.last 14 (1,true),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 15 7 false (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 17 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 14 1 true (4),
.cycle 6 8 true (1),
.last 14 (1,true),
.cycle 15 7 false (1),
.cycle 61 1 false (7),
.cycle 16 5 false (1),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 11 3 true (2),
.cycle 14 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid04_part678_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part678) = true := by rfl

def kid04_part680 : Audit := .cycle 23 1 false (3)
theorem kid04_part680_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part680) = true := by rfl

def kid04_part681 : Audit := .cycle 10 12 false (1)
theorem kid04_part681_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part681) = true := by rfl

def kid04_part682 : Audit := .cycle 11 5 false (1)
theorem kid04_part682_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part682) = true := by rfl

def kid04_part683 : Audit := .split 23 (4,true) (byMove [
.cycle 26 1 false (2),
.cycle 25 1 false (-1),
.cycle 0 33 false (3),
.cycle 0 25 true (-2),
.cycle 0 33 false (3),
.last 24 (5,true),
.far true 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 3, 0, 1],[2048, 262144, 2097152, 512, 2048, 64, 262144, 262144, 0, 2097152, 8388608, 262144, 2048, 0, 2097152, 512, 2048, 64, 0, 0, 2097152, 2097152, 8388608, 262144, 0, 262144, 2097152, 512, 2048, 64, 1073741824],[2097152, 8, 16, 262144, 262144, 1073741824, 2048, 32768, 65536, 2097152, 2097152, 1073741824, 0, 8, 16, 0, 0, 1073741824, 2048, 134217728, 268435456, 262144, 262144, 1073741824, 2097152, 8, 16, 0, 0, 1073741824, 1073741824],1073741824⟩,
.cycle 0 39 true (-2),
.cycle 10 19 true (-2),
.cycle 0 37 true (-2),
.cycle 8 16 true (-2),
.far true 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 3, 0, 1],[2048, 262144, 2097152, 512, 2048, 64, 262144, 262144, 0, 2097152, 8388608, 262144, 2048, 0, 2097152, 512, 2048, 64, 0, 0, 2097152, 2097152, 8388608, 262144, 0, 262144, 2097152, 512, 2048, 64, 1073741824],[2097152, 8, 16, 262144, 262144, 1073741824, 2048, 32768, 65536, 2097152, 1073741824, 1073741824, 0, 8, 16, 0, 0, 1073741824, 2048, 134217728, 268435456, 262144, 1073741824, 1073741824, 2097152, 8, 16, 0, 0, 1073741824, 1073741824],1073741824⟩,
.cycle 0 34 true (-2),
.cycle 25 1 false (-1),
.cycle 11 13 false (2),
.cycle 27 1 false (3),
.cycle 0 39 true (-3),
.last 24 (5,true),
.last 37 (5,true),
.last 36 (5,true),
.cycle 2 22 true (-2),
.cycle 4 43 true (-2),
.last 25 (5,true),
.last 28 (5,true)
])
theorem kid04_part683_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part683) = true := by rfl

def kid04_part684 : Audit := .split 16 (4,true) (byMove [
.last 41 (5,true),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.far true 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 3, 0, 1],[2048, 262144, 2097152, 512, 2048, 64, 262144, 262144, 0, 2097152, 8388608, 262144, 2048, 0, 2097152, 512, 2048, 64, 0, 0, 2097152, 2097152, 8388608, 262144, 0, 262144, 2097152, 512, 2048, 64, 1073741824],[2097152, 16, 16, 262144, 262144, 1073741824, 2048, 65536, 65536, 2097152, 2097152, 1073741824, 0, 16, 16, 0, 0, 1073741824, 2048, 268435456, 268435456, 262144, 262144, 1073741824, 2097152, 16, 16, 0, 0, 1073741824, 1073741824],1073741824⟩,
.cycle 0 23 true (-2),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 12 5 false (0),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.cycle 16 3 false (-2),
.cycle 11 17 false (2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.last 37 (5,true),
.cycle 0 23 true (-2),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.last 18 (5,true),
.cycle 9 8 false (1)
])
theorem kid04_part684_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part684) = true := by rfl

def kid04_part685 : Audit := .split 16 (5,true) (byMove [
.last 45 (4,true),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.last 23 (4,true),
.last 19 (4,true),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 12 5 false (0),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.last 19 (4,true),
.last 27 (4,true),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.last 23 (4,true),
.last 19 (4,true),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.last 19 (4,true),
.cycle 9 8 false (1)
])
theorem kid04_part685_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part685) = true := by rfl

def kid04_part686 : Audit := .cycle 0 19 true (-2)
theorem kid04_part686_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part686) = true := by rfl

def kid04_part687 : Audit := .split 19 (4,true) (byMove [
.cycle 6 24 false (3),
.cycle 20 12 true (-1),
.cycle 10 15 false (2),
.cycle 20 12 true (-3),
.cycle 8 12 false (2),
.cycle 22 12 true (0),
.cycle 0 20 true (-2),
.cycle 20 12 true (1),
.cycle 0 74 true (-4),
.cycle 10 15 false (2),
.cycle 20 12 true (0),
.cycle 22 12 true (2),
.cycle 21 12 true (1),
.cycle 26 12 true (-2),
.cycle 0 22 true (-2),
.cycle 10 13 false (2),
.cycle 8 12 false (2),
.cycle 20 12 true (-1),
.last 33 (5,true),
.cycle 1 19 true (-2),
.cycle 20 12 true (0),
.cycle 53 12 true (1),
.last 21 (5,true),
.cycle 21 12 true (-1)
])
theorem kid04_part687_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part687) = true := by rfl

def kid04_part688 : Audit := .split 18 (5,true) (byMove [
.last 22 (4,true),
.last 25 (4,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 12 7 false (0),
.last 27 (4,true),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 11 8 false (1),
.last 23 (4,true),
.last 19 (4,true),
.cycle 0 25 true (-2),
.cycle 14 5 false (0),
.last 21 (4,true),
.cycle 23 1 false (1),
.cycle 19 1 false (-3),
.cycle 12 7 false (0),
.cycle 13 6 false (0),
.cycle 10 15 false (1),
.cycle 10 15 false (1),
.last 20 (4,true),
.last 23 (4,true),
.last 19 (4,true),
.cycle 16 6 true (-2)
])
theorem kid04_part688_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part688) = true := by rfl

def kid04_part689 : Audit := .cycle 0 29 true (-2)
theorem kid04_part689_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part689) = true := by rfl

def kid04_part690 : Audit := .split 16 (4,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 9 8 false (1),
.cycle 8 11 true (-2),
.cycle 19 12 true (1),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.cycle 22 5 true (1),
.far true 8 ⟨0,[0, 1, 2, 3, 4, 4, 5, 6, 2, 7, 5, 6, 5, 6, 5, 5],[536870912, 262144, 2097152, 512, 2048, 64, 536870912, 536870912, 536870912, 2097152, 8388608, 262144, 288691058638848, 288692132380672, 558345748480, 134217728, 536870912, 16777216, 536870912, 536870912, 549755813888, 549755813888, 2199023255552, 68719476736, 288691058638848, 288691058638848, 323875430727680, 35184372088832, 140737488355328, 4398046511104, 288691058638848, 288691058638848, 288691058638848, 549755813888, 2199023255552, 68719476736, 288691058638848, 288691058638848, 288691058638848, 549755813888, 2199023255552, 68719476736, 536870912, 536870912, 288691058638848, 8589934592, 34359738368, 1073741824, 281474976710656],[549755813888, 262144, 16, 4398046511104, 536870912, 281474976710656, 2048, 4398046511104, 65536, 549755813888, 281474976710656, 281474976710656, 288699648573440, 69793218560, 268435456, 288691058638848, 536870912, 281474976710656, 536870912, 281474976710656, 17179869184, 262144, 281474976710656, 281474976710656, 141287244169216, 4398046511104, 65536, 288691058638848, 288691058638848, 281474976710656, 288691058638848, 281543696187392, 17179869184, 288691058638848, 288691058638848, 281474976710656, 2199023255552, 288691058638848, 17179869184, 288691058638848, 281474976710656, 281474976710656, 536870912, 288691058638848, 17179869184, 550829555712, 281474976710656, 281474976710656, 281474976710656],514012420912128⟩,
.last 24 (5,true),
.cycle 21 3 false (-1),
.cycle 8 13 true (-2),
.cycle 10 9 false (1),
.last 18 (5,true),
.cycle 9 8 false (1),
.last 24 (5,true),
.last 32 (5,true),
.cycle 0 19 true (-2),
.last 129 (5,true),
.last 18 (5,true),
.cycle 6 12 false (3)
])
theorem kid04_part690_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part690) = true := by rfl

def kid04_part691 : Audit := .split 16 (5,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 21 1 false (1),
.cycle 12 7 false (0),
.cycle 9 8 false (1),
.cycle 17 3 true (1),
.last 19 (4,true),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.last 22 (4,true),
.cycle 21 3 true (2),
.cycle 23 3 true (1),
.last 19 (4,true),
.cycle 19 3 true (1),
.cycle 10 9 false (1),
.cycle 12 7 false (0),
.cycle 9 8 false (1),
.cycle 17 3 true (1),
.last 19 (4,true),
.cycle 0 19 true (-2),
.cycle 85 58 true (1),
.last 19 (4,true),
.cycle 6 12 false (3)
])
theorem kid04_part691_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part691) = true := by rfl

def kid04_part692 : Audit := .cycle 10 6 false (1)
theorem kid04_part692_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part692) = true := by rfl

def kid04_part693 : Audit := .split 19 (4,true) (byMove [
.cycle 0 27 true (-4),
.cycle 10 15 false (1),
.cycle 21 1 false (-3),
.cycle 20 1 false (-4),
.cycle 12 8 false (0),
.cycle 13 7 false (-1),
.cycle 14 6 true (-3),
.cycle 17 33 true (-3),
.cycle 0 25 true (-3),
.cycle 20 1 false (-2),
.cycle 12 8 false (0),
.cycle 13 7 false (-1),
.cycle 14 6 false (-1),
.cycle 17 3 false (-2),
.cycle 14 8 true (-4),
.cycle 20 1 false (-4),
.cycle 12 8 false (0),
.cycle 13 7 false (-1),
.cycle 15 7 false (-1),
.proven (BB6.Agent11Raw39RCPumps.M76.table) (fun m hm => BB6.Agent11Raw39RCPumps.M76.never m hm),
.cycle 0 25 true (-3),
.cycle 10 12 false (1),
.last 21 (5,true),
.cycle 9 11 false (1)
])
theorem kid04_part693_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part693) = true := by rfl

def kid04_part694 : Audit := .cycle 11 5 false (1)
theorem kid04_part694_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part694) = true := by rfl

def kid04_part695 : Audit := .cycle 10 7 false (1)
theorem kid04_part695_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part695) = true := by rfl

def kid04_part696 : Audit := .split 16 (4,true) (byMove [
.cycle 23 1 false (-1),
.cycle 0 23 true (-3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.cycle 12 6 false (0),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 24 7 true (0),
.last 17 (5,true),
.cycle 14 3 false (-1),
.cycle 16 3 false (-2),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.last 20 (5,true),
.cycle 15 2 true (-2),
.cycle 0 41 true (-2),
.cycle 0 21 true (-2),
.last 20 (5,true),
.last 17 (5,true)
])
theorem kid04_part696_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part696) = true := by rfl

def kid04_part697 : Audit := .split 16 (5,true) (byMove [
.last 20 (4,true),
.cycle 0 23 true (-3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.cycle 13 5 false (-1),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.last 17 (4,true),
.cycle 23 5 true (1),
.cycle 14 3 false (-1),
.last 19 (4,true),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 10 17 false (1),
.cycle 15 2 true (-2),
.last 18 (4,true),
.cycle 0 21 true (-2),
.last 17 (4,true),
.cycle 17 6 true (-1)
])
theorem kid04_part697_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part697) = true := by rfl

def kid04_part698 : Audit := .cycle 0 19 true (-2)
theorem kid04_part698_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part698) = true := by rfl

def kid04_part699 : Audit := .split 19 (4,true) (byMove [
.cycle 3 20 false (3),
.last 33 (5,true),
.last 40 (5,true),
.last 38 (5,true),
.last 40 (5,true),
.last 20 (5,true),
.last 37 (5,true),
.last 44 (5,true),
.last 32 (5,true),
.last 30 (5,true),
.last 25 (5,true),
.last 35 (5,true),
.last 23 (5,true),
.last 34 (5,true),
.cycle 11 11 false (2),
.cycle 3 22 false (3),
.last 44 (5,true),
.last 20 (5,true),
.last 33 (5,true),
.last 32 (5,true),
.last 31 (5,true),
.last 36 (5,true),
.last 21 (5,true),
.last 24 (5,true)
])
theorem kid04_part699_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part699) = true := by rfl

def kid04_part700 : Audit := .split 17 (4,true) (byMove [
.cycle 20 1 false (0),
.cycle 10 13 false (1),
.cycle 11 7 false (1),
.cycle 0 23 true (-2),
.cycle 12 7 false (0),
.last 18 (5,true),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 128, 1048576, 524288, 1048576, 32768, 17592186044420, 18014398509481984, 1048576, 128, 256, 134217728, 22268348868853888, 128, 274877906944, 137438953472, 274877906944, 8589934592, 67108864, 18014398509481984, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 22268348868853888, 22268348868853888, 1048576, 137438953472, 274877906944, 35184372088832, 1048576, 18014398509481984, 1125899906842624, 562949953421312, 1125899906842624, 549755813888, 22268348868853888, 22268348868853888, 22268348868853888, 8796093022208, 17592186044416, 549755813888, 22268348868853888, 22268348868853888, 22268348868853888, 137438953472, 274877906944, 2251799813685248, 22268348868853888, 22268348868853888, 22268348868853888, 18014398509481984],[4, 256, 1048576, 1, 1, 18014398509481984, 16384, 1048576, 8796093022336, 4096, 4096, 18014398509481984, 67108864, 256, 18014398509481984, 16777216, 16777216, 18014398509481984, 4294967296, 274877906944, 128, 1073741824, 1073741824, 18014398509481984, 17592186044416, 17592186044416, 1048576, 4398046511104, 4398046511104, 18014398509481984, 17592186044416, 274877906944, 18014398509481984, 4398046511104, 4398046511104, 18014398509481984, 274877906944, 1125899906842624, 22268348868853888, 68719476736, 68719476736, 18014398509481984, 274877906944, 17592186044416, 22268348868853888, 68719476736, 68719476736, 18014398509481984, 1125899906842624, 274877906944, 22268348868853888, 281474976710656, 281474976710656, 18014398509481984, 18014398509481984],36028787891038018⟩,
.cycle 0 21 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 8 10 false (2),
.cycle 0 23 true (-2),
.cycle 10 8 false (1),
.cycle 19 3 false (-1),
.cycle 11 7 false (1),
.cycle 21 1 false (1),
.cycle 12 7 false (0),
.last 18 (5,true),
.last 35 (5,true),
.cycle 0 21 true (-2),
.cycle 2 16 false (3),
.cycle 0 23 true (-2),
.last 19 (5,true),
.last 22 (5,true)
])
theorem kid04_part700_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part700) = true := by rfl

def kid04_part701 : Audit := .split 55 (5,true) (byMove [
.last 59 (4,true),
.cycle 4 57 true (-2),
.last 77 (4,true),
.cycle 4 59 true (-2),
.last 58 (4,true),
.last 219 (4,true),
.cycle 16 42 true (0),
.last 69 (4,true),
.last 102 (4,true),
.cycle 4 55 true (-2),
.last 56 (4,true),
.cycle 13 44 true (-2),
.cycle 79 19 false (3),
.last 58 (4,true),
.cycle 16 44 true (0),
.last 77 (4,true),
.last 58 (4,true),
.cycle 123 54 true (3),
.cycle 16 42 true (0),
.cycle 0 135 true (-4),
.last 57 (4,true),
.cycle 94 36 false (4),
.last 56 (4,true),
.cycle 51 6 true (3)
])
theorem kid04_part701_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part701) = true := by rfl

def kid04_part702 : Audit := .split 16 (4,true) (byMove [
.cycle 10 13 false (1),
.last 19 (5,true),
.cycle 20 1 false (-2),
.cycle 0 23 true (-2),
.cycle 12 7 false (0),
.last 17 (5,true),
.last 20 (5,true),
.cycle 19 12 true (1),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.last 22 (5,true),
.last 25 (5,true),
.last 20 (5,true),
.cycle 15 2 true (-1),
.last 24 (5,true),
.cycle 0 21 true (-2),
.cycle 12 7 false (0),
.last 17 (5,true),
.last 20 (5,true),
.last 32 (5,true),
.cycle 0 19 true (-2),
.last 26 (5,true),
.last 18 (5,true),
.last 21 (5,true)
])
theorem kid04_part702_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part702) = true := by rfl

def kid04_part703 : Audit := .split 16 (5,true) (byMove [
.cycle 10 13 false (1),
.last 29 (4,true),
.last 18 (4,true),
.last 21 (4,true),
.last 17 (4,true),
.cycle 18 8 false (-2),
.cycle 0 247 true (-6),
.last 19 (4,true),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.last 23 (4,true),
.cycle 20 9 true (2),
.cycle 14 7 false (0),
.cycle 15 2 true (-1),
.last 18 (4,true),
.cycle 0 21 true (-2),
.last 17 (4,true),
.cycle 13 6 false (0),
.cycle 10 44 true (-2),
.last 19 (4,true),
.cycle 0 19 true (-2),
.last 83 (4,true),
.last 19 (4,true),
.cycle 16 6 true (-1)
])
theorem kid04_part703_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part703) = true := by rfl

def kid04_part679 : Audit := .split 15 (1,true) (byMove [(kid04_part680),(kid04_part681),(kid04_part682),(kid04_part683),(kid04_part684),(kid04_part685),(kid04_part686),(kid04_part687),(kid04_part688),(kid04_part689),(kid04_part690),(kid04_part691),(kid04_part692),(kid04_part693),(kid04_part694),(kid04_part695),(kid04_part696),(kid04_part697),(kid04_part698),(kid04_part699),(kid04_part700),(kid04_part701),(kid04_part702),(kid04_part703)])

theorem kid04_part679_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part679) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part680),(kid04_part681),(kid04_part682),(kid04_part683),(kid04_part684),(kid04_part685),(kid04_part686),(kid04_part687),(kid04_part688),(kid04_part689),(kid04_part690),(kid04_part691),(kid04_part692),(kid04_part693),(kid04_part694),(kid04_part695),(kid04_part696),(kid04_part697),(kid04_part698),(kid04_part699),(kid04_part700),(kid04_part701),(kid04_part702),(kid04_part703)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part680_checked

  · exact kid04_part686_checked

  · exact kid04_part692_checked

  · exact kid04_part698_checked

  · exact kid04_part681_checked

  · exact kid04_part687_checked

  · exact kid04_part693_checked

  · exact kid04_part699_checked

  · exact kid04_part682_checked

  · exact kid04_part688_checked

  · exact kid04_part694_checked

  · exact kid04_part700_checked

  · exact kid04_part683_checked

  · exact kid04_part689_checked

  · exact kid04_part695_checked

  · exact kid04_part701_checked

  · exact kid04_part684_checked

  · exact kid04_part690_checked

  · exact kid04_part696_checked

  · exact kid04_part702_checked

  · exact kid04_part685_checked

  · exact kid04_part691_checked

  · exact kid04_part697_checked

  · exact kid04_part703_checked

def kid04_part705 : Audit := .split 14 (4,true) (byMove [
.cycle 17 1 false (1),
.cycle 0 16 false (3),
.cycle 22 1 false (-4),
.cycle 0 21 true (-1),
.cycle 15 5 false (-1),
.last 15 (5,true),
.cycle 35 1 false (1),
.cycle 12 15 true (0),
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 8 7 false (2),
.cycle 12 4 true (0),
.cycle 26 1 false (-2),
.cycle 10 5 false (1),
.cycle 27 1 false (-1),
.cycle 0 19 true (-1),
.cycle 15 5 false (-1),
.last 15 (5,true),
.cycle 3 17 false (3),
.cycle 0 66 true (-2),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.last 16 (5,true),
.cycle 22 1 false (4)
])
theorem kid04_part705_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part705) = true := by rfl

def kid04_part706 : Audit := .split 28 (4,true) (byMove [
.cycle 18 32 false (2),
.cycle 19 12 false (1),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 24 5 false (0),
.cycle 25 4 false (-1),
.cycle 19 15 false (1),
.cycle 34 15 true (1),
.cycle 0 82 true (-2),
.cycle 29 1 false (-1),
.cycle 24 5 false (0),
.cycle 25 4 true (-2),
.cycle 19 15 false (1),
.cycle 26 3 false (-1),
.cycle 19 17 false (1),
.cycle 29 1 false (-3),
.cycle 24 5 false (0),
.cycle 25 4 false (-1),
.cycle 19 16 false (1),
.far true 1 ⟨0,[0, 0],[10, 10, 10, 8, 32, 2, 64],[42, 2, 16, 10, 10, 64, 64],64⟩,
.cycle 0 82 true (-2),
.cycle 20 9 false (1),
.last 30 (5,true),
.cycle 9 35 true (-3)
])
theorem kid04_part706_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part706) = true := by rfl

def kid04_part707 : Audit := .cycle 12 1 false (0)
theorem kid04_part707_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part707) = true := by rfl

def kid04_part708 : Audit := .cycle 11 1 false (-1)
theorem kid04_part708_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part708) = true := by rfl

def kid04_part709 : Audit := .split 15 (4,true) (byMove [
.cycle 68 1 false (-2),
.cycle 11 12 false (-1),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.proven (BB6.Agent11Raw39RCPumps.M79.table) (fun m hm => BB6.Agent11Raw39RCPumps.M79.never m hm),
.cycle 42 15 true (1),
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
.cycle 49 17 true (1),
.far false 10 ⟨0,[0, 9, 3, 2, 3, 2, 2, 3, 1, 9, 3, 1, 1, 3, 6, 5, 4, 1, 8, 7],[36028797018963968, 72057594037927936, 8, 0, 16777216, 2251799813685248, 8192, 16384, 2097152, 1191220243402125632, 1191220243402125632, 1191220243402125632, 8192, 16384, 2097152, 1191220243402125632, 1191220243402125632, 1191220243402125632, 524288, 1048576, 32768, 1191220243402125632, 1191220243402125632, 1191220243402125632, 36028797018963968, 72057594037927936, 512, 1191220243402125632, 64, 2105344, 128, 256, 2097152, 256, 1152921504606846976, 64, 524288, 1048576, 512, 36028797018963968, 256, 2097152, 2147483648, 4294967296, 549755813888, 67108864, 1152921504606846976, 16777216, 128, 256, 134217728, 1191220243402125632, 16777216, 549755813888, 8796093022208, 17592186044416, 2251799813685248, 1048580, 1152921504606846976, 2251799813685248, 1152921504606846976],[4, 36028797018963968, 36028797018963968, 1, 72057594037927936, 1152921504606846976, 1048576, 2105344, 2105344, 262144, 16384, 1152921504606846976, 1048576, 1191220243402125632, 1191220243402125632, 262144, 16384, 1152921504606846976, 16384, 1191220243402125632, 1191220243402125632, 4096, 1048576, 1152921504606846976, 256, 36028797018963968, 36028797018963968, 64, 72057594037927936, 1152921504606846976, 1048576, 2097152, 2097152, 262144, 256, 1152921504606846976, 256, 1152921504606846976, 1152921504606846976, 64, 1048576, 1152921504606846976, 274877906944, 549755813888, 549755813888, 68719476736, 4294967296, 1152921504606846976, 67108864, 1152921504606846976, 1152921504606846976, 16777216, 256, 1152921504606846976, 1125899906842624, 2251799813685248, 2251799813685248, 281474976710656, 17592186044416, 1152921504606846976, 1152921504606846976],2256144533865627618⟩,
.cycle 11 9 false (-1),
.last 17 (5,true),
.cycle 9 7 false (1)
])
theorem kid04_part709_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part709) = true := by rfl

def kid04_part710 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 11 12 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 21 (5,true),
.cycle 38 15 true (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (-1),
.cycle 11 4 true (-2),
.last 17 (5,true),
.cycle 12 3 false (-1),
.last 31 (5,true),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 21 (5,true),
.last 61 (5,true),
.last 30 (5,true),
.cycle 22 1 false (4),
.last 16 (5,true),
.cycle 9 6 false (1)
])
theorem kid04_part710_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part710) = true := by rfl

def kid04_part711 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (-2),
.cycle 11 12 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (1),
.cycle 14 4 false (0),
.cycle 0 20 true (-1),
.cycle 11 15 true (-1),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 13 5 false (1),
.cycle 14 4 true (-1),
.proven (BB6.Agent11Raw39RCPumps.M81.table) (fun m hm => BB6.Agent11Raw39RCPumps.M81.never m hm),
.cycle 15 3 false (0),
.last 74 (5,true),
.cycle 18 1 false (-2),
.cycle 13 5 false (1),
.cycle 14 4 false (0),
.cycle 0 20 true (-1),
.cycle 6 25 false (3),
.cycle 0 20 true (-1),
.cycle 11 9 false (2),
.last 19 (5,true),
.cycle 9 9 false (2)
])
theorem kid04_part711_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part711) = true := by rfl

def kid04_part712 : Audit := .split 24 (4,true) (byMove [
.cycle 0 29 true (0),
.cycle 13 12 false (5),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 20 5 false (4),
.cycle 21 4 false (3),
.cycle 12 14 true (2),
.cycle 13 15 true (2),
.cycle 0 27 true (0),
.cycle 25 1 false (3),
.cycle 20 5 false (4),
.cycle 21 4 true (2),
.last 47 (5,true),
.cycle 22 3 false (3),
.cycle 0 71 true (-1),
.cycle 25 1 false (1),
.cycle 20 5 false (4),
.cycle 21 4 false (3),
.cycle 12 14 true (2),
.cycle 1 27 true (0),
.cycle 0 27 true (0),
.cycle 16 9 false (5),
.last 26 (5,true),
.cycle 9 16 true (0)
])
theorem kid04_part712_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part712) = true := by rfl

def kid04_part713 : Audit := .split 16 (4,true) (byMove [
.cycle 11 18 true (-3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 0 21 true (-2),
.cycle 0 23 true (-2),
.cycle 11 16 true (-2),
.cycle 17 1 false (-1),
.cycle 12 5 false (0),
.cycle 13 4 true (-2),
.cycle 11 18 true (-3),
.cycle 14 3 false (-1),
.cycle 0 23 true (-3),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 4 false (-1),
.cycle 0 21 true (-2),
.cycle 0 23 true (-2),
.cycle 11 16 true (-2),
.cycle 11 9 false (1),
.last 18 (5,true),
.cycle 9 8 false (1)
])
theorem kid04_part713_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part713) = true := by rfl

def kid04_part714 : Audit := .cycle 14 1 false (4)
theorem kid04_part714_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part714) = true := by rfl

def kid04_part715 : Audit := .split 11 (4,true) (byMove [
.cycle 18 1 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 14 1 false (4),
.cycle 13 15 true (1),
.cycle 0 20 true (-1),
.cycle 0 13 true (0),
.cycle 12 5 false (3),
.last 12 (5,true),
.cycle 8 9 true (0),
.cycle 11 3 false (1),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.last 34 (5,true),
.cycle 8 5 true (0),
.cycle 0 27 true (0),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid04_part715_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part715) = true := by rfl

def kid04_part716 : Audit := .split 11 (5,true) (byMove [
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 14 1 false (4),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.last 14 (4,true),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.last 16 (4,true),
.last 15 (4,true),
.last 24 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
])
theorem kid04_part716_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part716) = true := by rfl

def kid04_part717 : Audit := .split 19 (4,true) (byMove [
.cycle 13 26 false (1),
.cycle 13 12 false (0),
.cycle 21 1 false (-3),
.cycle 20 1 false (-4),
.cycle 15 5 false (-1),
.cycle 16 4 false (-2),
.cycle 11 9 false (0),
.cycle 46 15 true (1),
.cycle 0 44 true (-3),
.cycle 20 1 false (-2),
.cycle 15 5 false (-1),
.cycle 16 4 true (-3),
.cycle 11 9 false (0),
.cycle 17 3 false (-2),
.cycle 11 11 false (0),
.cycle 20 1 false (-4),
.cycle 15 5 false (-1),
.cycle 16 4 false (-2),
.last 25 (5,true),
.last 109 (5,true),
.last 65 (5,true),
.cycle 13 9 false (0),
.last 21 (5,true),
.cycle 9 11 false (1)
])
theorem kid04_part717_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part717) = true := by rfl

def kid04_part718 : Audit := .split 13 (4,true) (byMove [
.cycle 438 230 false (-2),
.cycle 11 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 5 false (0),
.cycle 11 4 false (0),
.cycle 10 6 true (-1),
.cycle 14 15 true (0),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 11 5 false (0),
.cycle 11 4 true (-1),
.cycle 10 6 false (0),
.cycle 11 3 false (0),
.cycle 10 8 true (-2),
.cycle 14 1 false (-2),
.cycle 11 5 false (0),
.cycle 11 4 false (0),
.cycle 10 7 false (1),
.far true 1 ⟨0,[0, 0],[10, 10, 10, 8, 32, 2, 64],[42, 2, 16, 10, 10, 64, 64],64⟩,
.cycle 0 50 true (-2),
.cycle 11 9 false (1),
.last 15 (5,true),
.cycle 9 5 false (1)
])
theorem kid04_part718_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part718) = true := by rfl

def kid04_part719 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (-2),
.cycle 12 12 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 15 5 false (1),
.cycle 16 4 false (0),
.cycle 14 8 false (2),
.cycle 12 15 true (-1),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 15 5 false (1),
.cycle 16 4 true (-1),
.cycle 14 8 false (2),
.cycle 17 3 false (0),
.cycle 14 10 false (2),
.cycle 20 1 false (-2),
.cycle 15 5 false (1),
.cycle 16 4 false (0),
.cycle 18 4 true (-1),
.cycle 49 21 true (-2),
.cycle 0 22 true (-1),
.cycle 12 9 false (2),
.last 21 (5,true),
.cycle 9 11 false (2)
])
theorem kid04_part719_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part719) = true := by rfl

def kid04_part720 : Audit := .cycle 11 1 false (-1)
theorem kid04_part720_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part720) = true := by rfl

def kid04_part721 : Audit := .split 15 (4,true) (byMove [
.cycle 3 52 false (3),
.cycle 11 12 false (-1),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.cycle 34 1 false (4),
.cycle 22 15 true (0),
.cycle 0 38 true (-3),
.cycle 16 1 false (-2),
.cycle 11 5 false (-1),
.cycle 12 4 true (-3),
.cycle 15 3 false (-3),
.cycle 13 3 false (-2),
.cycle 42 1 false (4),
.cycle 16 1 false (-4),
.cycle 11 5 false (-1),
.cycle 12 4 false (-2),
.last 22 (5,true),
.cycle 37 2 true (0),
.last 60 (5,true),
.cycle 11 9 false (-1),
.last 17 (5,true),
.cycle 9 7 false (1)
])
theorem kid04_part721_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part721) = true := by rfl

def kid04_part722 : Audit := .split 14 (4,true) (byMove [
.last 45 (5,true),
.cycle 11 12 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 17 (5,true),
.cycle 18 15 true (0),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 11 5 false (-1),
.cycle 11 4 true (-2),
.last 17 (5,true),
.cycle 12 3 false (-1),
.last 19 (5,true),
.cycle 15 1 false (-3),
.cycle 11 5 false (-1),
.cycle 11 4 false (-1),
.last 17 (5,true),
.last 34 (5,true),
.cycle 0 26 true (-2),
.cycle 11 9 false (0),
.last 16 (5,true),
.cycle 9 6 false (1)
])
theorem kid04_part722_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part722) = true := by rfl

def kid04_part723 : Audit := .split 14 (5,true) (byMove [
.last 18 (4,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 17 1 false (3),
.cycle 0 16 true (0),
.last 20 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 19 (4,true),
.cycle 3 17 false (3),
.last 17 (4,true),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.last 27 (4,true),
.cycle 0 16 true (0),
.last 16 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 39 true (0)
])
theorem kid04_part723_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part723) = true := by rfl

def kid04_part724 : Audit := .cycle 1 12 true (0)
theorem kid04_part724_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part724) = true := by rfl

def kid04_part725 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 11 12 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 2 13 true (0),
.cycle 11 15 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 11 5 false (1),
.cycle 11 4 true (0),
.cycle 0 17 true (-1),
.cycle 11 3 false (1),
.cycle 2 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 4 false (1),
.cycle 2 13 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 11 9 false (2),
.last 14 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part725_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part725) = true := by rfl

def kid04_part726 : Audit := .split 25 (4,true) (byMove [
.far true 2 ⟨0,[0, 1, 0, 1],[641, 641, 512, 512, 2048, 128, 641, 1, 641, 512, 2048, 128, 4096],[641, 641, 16, 641, 1, 4096, 2048, 641, 16, 641, 1, 4096, 4096],4096⟩,
.cycle 16 12 false (2),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 21 5 false (1),
.cycle 22 4 false (0),
.cycle 0 39 true (-1),
.cycle 52 15 true (3),
.cycle 0 31 true (-1),
.cycle 26 1 false (0),
.cycle 21 5 false (1),
.cycle 22 4 true (-1),
.cycle 4 24 false (4),
.cycle 23 3 false (0),
.cycle 0 41 true (-2),
.cycle 26 1 false (-2),
.cycle 21 5 false (1),
.cycle 22 4 false (0),
.cycle 0 39 true (-1),
.cycle 18 90 true (-1),
.cycle 0 31 true (-1),
.cycle 17 9 false (2),
.last 27 (5,true),
.cycle 18 36 true (-2)
])
theorem kid04_part726_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part726) = true := by rfl

def kid04_part727 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 19 1 false (-3),
.last 16 (5,true),
.cycle 12 5 false (0),
.last 12 (5,true),
.last 29 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 32768, 4, 262144, 65536, 128, 256, 8, 16, 16, 16, 262144],[4, 1024, 16, 1, 16, 262144, 16384, 1024, 16, 4096, 65536, 262144, 4, 1024, 262144, 1, 16, 262144, 262144],263168⟩,
.last 12 (5,true),
.last 22 (5,true),
.cycle 10 2 true (0),
.last 23 (5,true),
.cycle 20 1 false (-2),
.cycle 12 5 false (0),
.last 12 (5,true),
.cycle 0 27 true (0),
.last 14 (5,true),
.cycle 2 12 true (0),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid04_part727_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part727) = true := by rfl

def kid04_part728 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 9 4 true (0),
.last 17 (4,true),
.cycle 0 19 true (0),
.last 12 (4,true),
.last 16 (4,true),
.last 25 (4,true),
.last 27 (4,true),
.last 20 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true),
.last 18 (4,true),
.cycle 10 2 true (0),
.last 17 (4,true),
.last 19 (4,true),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 27 true (0),
.cycle 1 15 true (0),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
])
theorem kid04_part728_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part728) = true := by rfl

def kid04_part704 : Audit := .split 10 (1,true) (byMove [(kid04_part705),(kid04_part706),(kid04_part707),(kid04_part708),(kid04_part709),(kid04_part710),(kid04_part711),(kid04_part712),(kid04_part713),(kid04_part714),(kid04_part715),(kid04_part716),(kid04_part717),(kid04_part718),(kid04_part719),(kid04_part720),(kid04_part721),(kid04_part722),(kid04_part723),(kid04_part724),(kid04_part725),(kid04_part726),(kid04_part727),(kid04_part728)])

theorem kid04_part704_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part704) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part705),(kid04_part706),(kid04_part707),(kid04_part708),(kid04_part709),(kid04_part710),(kid04_part711),(kid04_part712),(kid04_part713),(kid04_part714),(kid04_part715),(kid04_part716),(kid04_part717),(kid04_part718),(kid04_part719),(kid04_part720),(kid04_part721),(kid04_part722),(kid04_part723),(kid04_part724),(kid04_part725),(kid04_part726),(kid04_part727),(kid04_part728)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part705_checked

  · exact kid04_part711_checked

  · exact kid04_part717_checked

  · exact kid04_part723_checked

  · exact kid04_part706_checked

  · exact kid04_part712_checked

  · exact kid04_part718_checked

  · exact kid04_part724_checked

  · exact kid04_part707_checked

  · exact kid04_part713_checked

  · exact kid04_part719_checked

  · exact kid04_part725_checked

  · exact kid04_part708_checked

  · exact kid04_part714_checked

  · exact kid04_part720_checked

  · exact kid04_part726_checked

  · exact kid04_part709_checked

  · exact kid04_part715_checked

  · exact kid04_part721_checked

  · exact kid04_part727_checked

  · exact kid04_part710_checked

  · exact kid04_part716_checked

  · exact kid04_part722_checked

  · exact kid04_part728_checked

def kid04_part729 : Audit := .cycle 20 1 false (4)
theorem kid04_part729_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part729) = true := by rfl

def kid04_part730 : Audit := .cycle 15 1 false (-1)
theorem kid04_part730_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part730) = true := by rfl

def kid04_part732 : Audit := .cycle 17 1 false (1)
theorem kid04_part732_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part732) = true := by rfl

def kid04_part733 : Audit := .cycle 24 2 false (0)
theorem kid04_part733_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part733) = true := by rfl

def kid04_part734 : Audit := .cycle 12 1 false (0)
theorem kid04_part734_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part734) = true := by rfl

def kid04_part735 : Audit := .cycle 11 1 false (-1)
theorem kid04_part735_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part735) = true := by rfl

def kid04_part736 : Audit := .cycle 11 2 false (-1)
theorem kid04_part736_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part736) = true := by rfl

def kid04_part737 : Audit := .cycle 11 2 false (-1)
theorem kid04_part737_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part737) = true := by rfl

def kid04_part738 : Audit := .cycle 13 2 false (1)
theorem kid04_part738_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part738) = true := by rfl

def kid04_part739 : Audit := .split 11 (1,true) (byMove [
.last 26 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 14 1 false (4),
.cycle 20 2 false (4),
.cycle 13 2 false (1),
.cycle 0 13 true (0),
.cycle 20 2 false (4),
.last 12 (5,true),
.cycle 16 2 false (0),
.cycle 25 2 false (3),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 20 2 false (2),
.cycle 1 12 true (0),
.cycle 21 2 false (3),
.cycle 0 13 true (0),
.last 23 (5,true),
.last 12 (5,true)
])
theorem kid04_part739_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part739) = true := by rfl

def kid04_part740 : Audit := .cycle 12 2 false (0)
theorem kid04_part740_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part740) = true := by rfl

def kid04_part741 : Audit := .cycle 14 1 false (4)
theorem kid04_part741_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part741) = true := by rfl

def kid04_part742 : Audit := .cycle 13 2 false (3)
theorem kid04_part742_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part742) = true := by rfl

def kid04_part743 : Audit := .split 11 (5,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 14 1 false (4),
.last 12 (1,true),
.cycle 13 2 false (1),
.cycle 0 13 true (0),
.cycle 13 2 false (3),
.cycle 13 2 false (3),
.last 13 (1,true),
.cycle 15 2 false (1),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 20 2 false (2),
.last 12 (1,true),
.cycle 14 2 false (2),
.cycle 0 13 true (0),
.cycle 11 8 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part743_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part743) = true := by rfl

def kid04_part744 : Audit := .split 12 (1,true) (byMove [
.cycle 18 1 false (4),
.cycle 21 2 false (-1),
.cycle 14 2 false (-2),
.cycle 0 20 true (-1),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 6 7 false (3),
.last 27 (5,true),
.last 15 (5,true),
.cycle 24 2 false (0),
.last 25 (5,true),
.last 13 (5,true),
.cycle 15 2 false (-1),
.cycle 10 6 false (0),
.cycle 14 2 false (-2),
.cycle 16 2 false (0),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 16 (5,true),
.last 28 (5,true),
.cycle 17 2 false (-1),
.last 60 (5,true),
.last 17 (5,true),
.last 13 (5,true)
])
theorem kid04_part744_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part744) = true := by rfl

def kid04_part745 : Audit := .cycle 10 3 false (0)
theorem kid04_part745_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part745) = true := by rfl

def kid04_part746 : Audit := .cycle 15 2 false (1)
theorem kid04_part746_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part746) = true := by rfl

def kid04_part747 : Audit := .cycle 11 1 false (-1)
theorem kid04_part747_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part747) = true := by rfl

def kid04_part748 : Audit := .cycle 11 2 false (-1)
theorem kid04_part748_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part748) = true := by rfl

def kid04_part749 : Audit := .cycle 11 2 false (-1)
theorem kid04_part749_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part749) = true := by rfl

def kid04_part750 : Audit := .split 14 (5,true) (byMove [
.cycle 0 37 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 17 1 false (3),
.last 15 (1,true),
.cycle 16 2 false (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 16 2 false (2),
.last 16 (1,true),
.last 19 (1,true),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 23 2 false (1),
.last 15 (1,true),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 0 39 true (0)
])
theorem kid04_part750_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part750) = true := by rfl

def kid04_part751 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 20 2 false (0),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 12 (5,true),
.cycle 21 2 false (1),
.far false 5 ⟨0,[0, 1, 2, 1, 1, 3, 4, 1, 3, 3],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 1048836, 1073741824, 8192, 524288, 1048576, 512, 256, 128, 1073741824, 128, 256, 134217728, 1140867072, 1073741824, 33554432, 524288, 1048576, 2097152, 1073741824, 524288, 1073741824, 1073741824],[4, 2, 0, 1, 128, 1073741824, 16384, 8192, 256, 4096, 128, 1073741824, 256, 128, 1073741824, 64, 524288, 1073741824, 67108864, 33554432, 256, 16777216, 128, 1073741824, 1048576, 524288, 1073741824, 262144, 524288, 1073741824, 1073741824],1861381632⟩,
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 12 (5,true),
.cycle 14 2 false (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 1048580, 1073741824, 256, 33554432, 67108864, 2097152, 32768, 256, 1073741824, 33554432, 67108864, 134217728, 262144, 1073741824, 256, 33554432, 67108864, 134217728, 1325695232, 1325695232, 1325695232, 1073741824],[4, 256, 0, 1, 128, 1073741824, 16384, 256, 256, 4096, 128, 1073741824, 1048576, 256, 1073741824, 262144, 33554432, 1073741824, 67108864, 1325695232, 32768, 16777216, 33554432, 1073741824, 67108864, 1325695232, 1325695232, 16777216, 33554432, 1073741824, 1073741824],2138994176⟩,
.cycle 13 2 false (-1),
.cycle 15 2 false (1),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 0 27 true (0),
.cycle 1 12 true (0),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 12 (5,true)
])
theorem kid04_part751_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part751) = true := by rfl

def kid04_part752 : Audit := .cycle 0 15 true (0)
theorem kid04_part752_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part752) = true := by rfl

def kid04_part753 : Audit := .cycle 21 2 false (1)
theorem kid04_part753_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part753) = true := by rfl

def kid04_part754 : Audit := .split 14 (5,true) (byMove [
.cycle 0 18 true (0),
.last 15 (1,true),
.cycle 20 1 false (0),
.last 17 (1,true),
.cycle 21 2 false (-1),
.cycle 17 2 false (-1),
.cycle 6 34 true (0),
.last 15 (1,true),
.cycle 22 2 false (0),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.cycle 10 10 true (0),
.last 20 (1,true),
.last 15 (1,true),
.cycle 23 2 false (1),
.cycle 5 10 true (0),
.cycle 10 5 true (0),
.cycle 17 2 false (-1),
.cycle 13 19 true (1),
.last 15 (1,true),
.cycle 12 4 true (2),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.cycle 11 6 true (1)
])
theorem kid04_part754_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part754) = true := by rfl

def kid04_part755 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 9 4 true (0),
.cycle 13 2 false (-1),
.cycle 21 2 false (1),
.last 12 (1,true),
.cycle 16 2 false (0),
.cycle 0 13 true (0),
.cycle 8 8 true (0),
.cycle 29 2 false (5),
.cycle 14 2 false (0),
.last 12 (1,true),
.cycle 13 2 false (-1),
.cycle 15 2 false (1),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.cycle 0 27 true (0),
.last 12 (1,true),
.cycle 2 15 true (0),
.cycle 0 13 true (0),
.cycle 11 6 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part755_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part755) = true := by rfl

def kid04_part731 : Audit := .split 10 (4,true) (byMove [(kid04_part732),(kid04_part733),(kid04_part734),(kid04_part735),(kid04_part736),(kid04_part737),(kid04_part738),(kid04_part739),(kid04_part740),(kid04_part741),(kid04_part742),(kid04_part743),(kid04_part744),(kid04_part745),(kid04_part746),(kid04_part747),(kid04_part748),(kid04_part749),(kid04_part750),(kid04_part751),(kid04_part752),(kid04_part753),(kid04_part754),(kid04_part755)])

theorem kid04_part731_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part731) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part732),(kid04_part733),(kid04_part734),(kid04_part735),(kid04_part736),(kid04_part737),(kid04_part738),(kid04_part739),(kid04_part740),(kid04_part741),(kid04_part742),(kid04_part743),(kid04_part744),(kid04_part745),(kid04_part746),(kid04_part747),(kid04_part748),(kid04_part749),(kid04_part750),(kid04_part751),(kid04_part752),(kid04_part753),(kid04_part754),(kid04_part755)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part732_checked

  · exact kid04_part738_checked

  · exact kid04_part744_checked

  · exact kid04_part750_checked

  · exact kid04_part733_checked

  · exact kid04_part739_checked

  · exact kid04_part745_checked

  · exact kid04_part751_checked

  · exact kid04_part734_checked

  · exact kid04_part740_checked

  · exact kid04_part746_checked

  · exact kid04_part752_checked

  · exact kid04_part735_checked

  · exact kid04_part741_checked

  · exact kid04_part747_checked

  · exact kid04_part753_checked

  · exact kid04_part736_checked

  · exact kid04_part742_checked

  · exact kid04_part748_checked

  · exact kid04_part754_checked

  · exact kid04_part737_checked

  · exact kid04_part743_checked

  · exact kid04_part749_checked

  · exact kid04_part755_checked

def kid04_part757 : Audit := .split 14 (4,true) (byMove [
.cycle 17 1 false (1),
.last 15 (1,true),
.cycle 17 1 false (-3),
.cycle 0 21 true (-1),
.cycle 17 1 false (-3),
.cycle 0 16 false (3),
.last 16 (1,true),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 0, 8192, 16384, 512, 4, 16384, 16384, 33554432, 67108864, 2097152, 256, 1327522765, 1327522765, 33554432, 67108864, 134217728, 2097408, 1327522765, 1327522765, 33554432, 67108864, 134217728, 1327522765, 1327522765, 1327522765, 1073741824],[4, 1073741824, 0, 1, 2, 16384, 256, 1073741824, 2097408, 64, 128, 67108872, 1048576, 1073741824, 16384, 262144, 524288, 512, 67108864, 1073741824, 1327522765, 16777216, 33554432, 67108864, 67108864, 1073741824, 1327522765, 16777216, 33554432, 201326592, 1073741824],2145333312⟩,
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 8 7 false (2),
.cycle 9 7 false (1),
.cycle 18 1 false (-2),
.last 15 (1,true),
.cycle 17 1 false (-3),
.cycle 0 19 true (-1),
.cycle 17 1 false (-3),
.cycle 10 5 false (1),
.last 16 (1,true),
.cycle 43 1 false (-1),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.cycle 22 1 false (4),
.cycle 22 1 false (4)
])
theorem kid04_part757_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part757) = true := by rfl

def kid04_part758 : Audit := .cycle 25 1 false (-1)
theorem kid04_part758_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part758) = true := by rfl

def kid04_part759 : Audit := .cycle 12 1 false (0)
theorem kid04_part759_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part759) = true := by rfl

def kid04_part760 : Audit := .cycle 11 1 false (-1)
theorem kid04_part760_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part760) = true := by rfl

def kid04_part761 : Audit := .cycle 12 1 false (-2)
theorem kid04_part761_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part761) = true := by rfl

def kid04_part762 : Audit := .cycle 11 1 false (-1)
theorem kid04_part762_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part762) = true := by rfl

def kid04_part763 : Audit := .cycle 14 1 false (0)
theorem kid04_part763_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part763) = true := by rfl

def kid04_part764 : Audit := .split 11 (1,true) (byMove [
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 14 1 false (4),
.cycle 21 1 false (3),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 21 1 false (1),
.cycle 1 12 true (0),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 25 3 true (3)
])
theorem kid04_part764_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part764) = true := by rfl

def kid04_part765 : Audit := .cycle 13 1 false (-1)
theorem kid04_part765_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part765) = true := by rfl

def kid04_part766 : Audit := .cycle 14 1 false (4)
theorem kid04_part766_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part766) = true := by rfl

def kid04_part767 : Audit := .split 11 (4,true) (byMove [
.cycle 18 1 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 14 1 false (4),
.last 12 (1,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.last 13 (1,true),
.cycle 11 3 false (1),
.cycle 16 1 false (4),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 21 1 false (1),
.last 12 (1,true),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 8 5 true (0)
])
theorem kid04_part767_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part767) = true := by rfl

def kid04_part768 : Audit := .cycle 13 1 false (3)
theorem kid04_part768_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part768) = true := by rfl

def kid04_part769 : Audit := .split 12 (1,true) (byMove [
.cycle 18 1 false (4),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 0 20 true (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 2, 4, 2, 4],[16777216, 8388608, 2097152, 512, 2048, 2048, 16777216, 1073741824, 16777216, 2097152, 8388608, 8388608, 1761775616, 1761775616, 1761775616, 32768, 131072, 131072, 16777216, 1073741824, 134217728, 134217728, 536870912, 536870912, 16777216, 1073741824, 537001984, 134217728, 536870912, 536870912, 1073741824],[134217728, 536870912, 16, 16777216, 1073741824, 64, 2048, 536870912, 65536, 134217728, 1073741824, 262144, 1761775616, 1761775616, 65536, 1761775616, 1073741824, 4096, 131072, 536870912, 65536, 8388608, 1073741824, 16777216, 131072, 536870912, 65536, 131072, 1073741824, 16777216, 1073741824],1107849344⟩,
.cycle 10 5 false (1),
.cycle 25 1 false (-1),
.last 13 (4,true),
.cycle 37 1 false (-3),
.cycle 16 1 false (-2),
.last 16 (4,true),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 20 1 false (-2),
.cycle 32 1 false (-2),
.last 14 (4,true),
.cycle 64 1 false (-4),
.last 13 (4,true),
.cycle 10 7 false (1)
])
theorem kid04_part769_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part769) = true := by rfl

def kid04_part770 : Audit := .split 13 (4,true) (byMove [
.last 50 (1,true),
.cycle 22 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 15 (1,true),
.cycle 28 1 false (2),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (1,true),
.cycle 11 3 false (0),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.last 15 (1,true),
.last 30 (1,true),
.cycle 27 1 false (-1),
.cycle 19 1 false (-1),
.cycle 10 5 false (0),
.cycle 9 5 false (1)
])
theorem kid04_part770_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part770) = true := by rfl

def kid04_part771 : Audit := .cycle 16 1 false (0)
theorem kid04_part771_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part771) = true := by rfl

def kid04_part772 : Audit := .cycle 11 1 false (-1)
theorem kid04_part772_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part772) = true := by rfl

def kid04_part773 : Audit := .cycle 12 1 false (-2)
theorem kid04_part773_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part773) = true := by rfl

def kid04_part774 : Audit := .cycle 11 1 false (-1)
theorem kid04_part774_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part774) = true := by rfl

def kid04_part775 : Audit := .cycle 24 1 false (0)
theorem kid04_part775_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part775) = true := by rfl

def kid04_part776 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 16 true (0),
.last 12 (4,true),
.last 15 (4,true),
.cycle 22 1 false (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 2, 128, 256, 32768, 4, 8192, 8192, 128, 256, 8, 256, 2, 2, 262144],[4, 2, 256, 1, 262144, 128, 16384, 8192, 262144, 4096, 262144, 128, 4, 2, 256, 1, 262144, 128, 262144],279052⟩,
.cycle 24 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (0),
.cycle 15 1 false (-1),
.last 15 (4,true),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 27 true (0),
.cycle 1 12 true (0),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (0)
])
theorem kid04_part776_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part776) = true := by rfl

def kid04_part777 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 24 1 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 11 3 false (1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 18 1 false (0),
.cycle 10 4 true (0),
.cycle 9 4 true (0)
])
theorem kid04_part777_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part777) = true := by rfl

def kid04_part778 : Audit := .cycle 22 1 false (0)
theorem kid04_part778_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part778) = true := by rfl

def kid04_part779 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 14 1 false (-2),
.last 14 (1,true),
.cycle 14 1 false (-2),
.cycle 10 4 true (0),
.cycle 22 1 false (0),
.last 12 (1,true),
.cycle 24 1 false (0),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 9 8 true (0),
.cycle 15 1 false (-1),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 14 1 false (-2),
.cycle 10 2 true (0),
.cycle 0 27 true (0),
.last 12 (1,true),
.cycle 2 12 true (0),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 14 3 true (2)
])
theorem kid04_part779_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part779) = true := by rfl

def kid04_part780 : Audit := .cycle 11 3 true (1)
theorem kid04_part780_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part780) = true := by rfl

def kid04_part756 : Audit := .split 10 (5,true) (byMove [(kid04_part757),(kid04_part758),(kid04_part759),(kid04_part760),(kid04_part761),(kid04_part762),(kid04_part763),(kid04_part764),(kid04_part765),(kid04_part766),(kid04_part767),(kid04_part768),(kid04_part769),(kid04_part770),(kid04_part771),(kid04_part772),(kid04_part773),(kid04_part774),(kid04_part775),(kid04_part776),(kid04_part777),(kid04_part778),(kid04_part779),(kid04_part780)])

theorem kid04_part756_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part756) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part757),(kid04_part758),(kid04_part759),(kid04_part760),(kid04_part761),(kid04_part762),(kid04_part763),(kid04_part764),(kid04_part765),(kid04_part766),(kid04_part767),(kid04_part768),(kid04_part769),(kid04_part770),(kid04_part771),(kid04_part772),(kid04_part773),(kid04_part774),(kid04_part775),(kid04_part776),(kid04_part777),(kid04_part778),(kid04_part779),(kid04_part780)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part757_checked

  · exact kid04_part763_checked

  · exact kid04_part769_checked

  · exact kid04_part775_checked

  · exact kid04_part758_checked

  · exact kid04_part764_checked

  · exact kid04_part770_checked

  · exact kid04_part776_checked

  · exact kid04_part759_checked

  · exact kid04_part765_checked

  · exact kid04_part771_checked

  · exact kid04_part777_checked

  · exact kid04_part760_checked

  · exact kid04_part766_checked

  · exact kid04_part772_checked

  · exact kid04_part778_checked

  · exact kid04_part761_checked

  · exact kid04_part767_checked

  · exact kid04_part773_checked

  · exact kid04_part779_checked

  · exact kid04_part762_checked

  · exact kid04_part768_checked

  · exact kid04_part774_checked

  · exact kid04_part780_checked

def kid04_part781 : Audit := .cycle 0 23 true (0)
theorem kid04_part781_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part781) = true := by rfl

def kid04_part783 : Audit := .cycle 24 1 false (2)
theorem kid04_part783_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part783) = true := by rfl

def kid04_part784 : Audit := .cycle 11 11 false (1)
theorem kid04_part784_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part784) = true := by rfl

def kid04_part785 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 1 13 false (3),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 1 13 true (0),
.cycle 14 4 false (0),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 17 1 false (3),
.last 14 (5,true),
.cycle 1 13 true (0)
])
theorem kid04_part785_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part785) = true := by rfl

def kid04_part786 : Audit := .cycle 0 12 true (0)
theorem kid04_part786_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part786) = true := by rfl

def kid04_part787 : Audit := .split 11 (4,true) (byMove [
.cycle 14 1 false (2),
.cycle 13 11 false (-1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 16 3 false (0),
.cycle 16 3 false (-2),
.cycle 11 11 false (1),
.cycle 15 1 false (3),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.last 13 (5,true),
.cycle 1 12 true (1)
])
theorem kid04_part787_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part787) = true := by rfl

def kid04_part788 : Audit := .split 11 (5,true) (byMove [
.cycle 14 1 false (2),
.cycle 1 13 false (3),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 13 false (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 16 3 false (0),
.last 16 (4,true),
.last 22 (4,true),
.cycle 15 1 false (3),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.last 14 (4,true),
.cycle 1 12 true (1)
])
theorem kid04_part788_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part788) = true := by rfl

def kid04_part789 : Audit := .cycle 0 11 true (0)
theorem kid04_part789_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part789) = true := by rfl

def kid04_part790 : Audit := .cycle 1 10 true (1)
theorem kid04_part790_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part790) = true := by rfl

def kid04_part791 : Audit := .cycle 0 23 true (0)
theorem kid04_part791_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part791) = true := by rfl

def kid04_part792 : Audit := .cycle 3 8 true (1)
theorem kid04_part792_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part792) = true := by rfl

def kid04_part793 : Audit := .cycle 8 3 true (1)
theorem kid04_part793_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part793) = true := by rfl

def kid04_part794 : Audit := .cycle 1 11 true (1)
theorem kid04_part794_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part794) = true := by rfl

def kid04_part795 : Audit := .split 14 (5,true) (byMove [
.last 18 (4,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.last 18 (4,true),
.cycle 17 1 false (3),
.cycle 17 5 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (0),
.cycle 16 5 false (0),
.last 17 (4,true),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (0),
.cycle 21 5 false (2),
.cycle 15 5 false (1),
.last 16 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 16 true (0)
])
theorem kid04_part795_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part795) = true := by rfl

def kid04_part796 : Audit := .split 15 (4,true) (byMove [
.cycle 482 256 false (-2),
.cycle 11 14 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.last 111 (5,true),
.cycle 11 6 true (-1),
.cycle 16 17 true (0),
.cycle 20 1 false (4),
.cycle 16 1 false (0),
.cycle 11 7 false (1),
.cycle 11 6 true (-1),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 8 true (-2),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.cycle 11 6 false (1),
.cycle 10 7 false (2),
.far true 1 ⟨0,[0, 0],[10, 10, 10, 8, 32, 10, 64],[42, 2, 16, 10, 10, 64, 64],64⟩,
.cycle 0 56 true (-2),
.cycle 11 11 false (1),
.last 17 (5,true),
.cycle 9 7 false (2)
])
theorem kid04_part796_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part796) = true := by rfl

def kid04_part797 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 0 17 true (-1),
.cycle 14 4 false (2),
.cycle 22 4 false (4),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 13 4 false (2),
.cycle 14 4 false (0),
.cycle 11 3 false (1),
.cycle 16 4 false (2),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 10 4 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.last 14 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part797_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part797) = true := by rfl

def kid04_part798 : Audit := .cycle 30 1 false (6)
theorem kid04_part798_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part798) = true := by rfl

def kid04_part799 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 23 true (-3),
.cycle 18 1 false (-2),
.cycle 16 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 30 1 false (6),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 8 5 true (1),
.last 12 (5,true),
.cycle 16 3 false (0),
.cycle 16 3 false (-2),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 0 27 true (0),
.cycle 10 2 true (1),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid04_part799_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part799) = true := by rfl

def kid04_part800 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.cycle 18 1 false (-2),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 0 17 true (-1),
.cycle 30 1 false (6),
.cycle 9 4 true (1),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.last 18 (4,true),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 0 27 true (0),
.cycle 10 2 true (1),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 13 true (1)
])
theorem kid04_part800_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part800) = true := by rfl

def kid04_part801 : Audit := .cycle 0 11 true (0)
theorem kid04_part801_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part801) = true := by rfl

def kid04_part802 : Audit := .cycle 1 10 true (1)
theorem kid04_part802_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part802) = true := by rfl

def kid04_part803 : Audit := .cycle 2 9 true (1)
theorem kid04_part803_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part803) = true := by rfl

def kid04_part804 : Audit := .cycle 4 28 true (1)
theorem kid04_part804_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part804) = true := by rfl

def kid04_part805 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 5, 1024, 128, 128, 256, 32768, 4, 5, 128, 128, 256, 8, 5, 1024, 128, 262144],[4, 1024, 5, 1, 262144, 32768, 16384, 1024, 262144, 4096, 262144, 5, 4, 1024, 136, 1, 262144, 32768, 262144],262144⟩,
.last 14 (4,true),
.cycle 10 5 true (1),
.last 13 (4,true),
.cycle 1 15 false (3),
.cycle 6 28 true (1),
.cycle 10 3 true (2),
.cycle 14 9 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1),
.last 19 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 17 (4,true),
.cycle 11 17 true (2),
.cycle 10 3 true (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1)
])
theorem kid04_part805_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part805) = true := by rfl

def kid04_part806 : Audit := .cycle 1 11 true (1)
theorem kid04_part806_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part806) = true := by rfl

def kid04_part782 : Audit := .split 10 (1,true) (byMove [(kid04_part783),(kid04_part784),(kid04_part785),(kid04_part786),(kid04_part787),(kid04_part788),(kid04_part789),(kid04_part790),(kid04_part791),(kid04_part792),(kid04_part793),(kid04_part794),(kid04_part795),(kid04_part796),(kid04_part797),(kid04_part798),(kid04_part799),(kid04_part800),(kid04_part801),(kid04_part802),(kid04_part803),(kid04_part804),(kid04_part805),(kid04_part806)])

theorem kid04_part782_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part782) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid04_part783),(kid04_part784),(kid04_part785),(kid04_part786),(kid04_part787),(kid04_part788),(kid04_part789),(kid04_part790),(kid04_part791),(kid04_part792),(kid04_part793),(kid04_part794),(kid04_part795),(kid04_part796),(kid04_part797),(kid04_part798),(kid04_part799),(kid04_part800),(kid04_part801),(kid04_part802),(kid04_part803),(kid04_part804),(kid04_part805),(kid04_part806)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part783_checked

  · exact kid04_part789_checked

  · exact kid04_part795_checked

  · exact kid04_part801_checked

  · exact kid04_part784_checked

  · exact kid04_part790_checked

  · exact kid04_part796_checked

  · exact kid04_part802_checked

  · exact kid04_part785_checked

  · exact kid04_part791_checked

  · exact kid04_part797_checked

  · exact kid04_part803_checked

  · exact kid04_part786_checked

  · exact kid04_part792_checked

  · exact kid04_part798_checked

  · exact kid04_part804_checked

  · exact kid04_part787_checked

  · exact kid04_part793_checked

  · exact kid04_part799_checked

  · exact kid04_part805_checked

  · exact kid04_part788_checked

  · exact kid04_part794_checked

  · exact kid04_part800_checked

  · exact kid04_part806_checked

def kid04_part807 : Audit := .split 11 (4,true) (byMove [
.cycle 14 1 false (2),
.split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.cycle 14 11 false (1),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (1),
.cycle 14 11 false (3),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.cycle 13 11 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 17 1 false (3),
.last 14 (5,true),
.cycle 2 12 true (0)
]),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 14 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.cycle 13 11 false (1),
.cycle 0 13 true (0),
.cycle 14 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (1),
.cycle 13 11 false (3),
.last 14 (1,true),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (-1),
.cycle 13 11 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 17 1 false (3),
.cycle 11 4 true (0),
.cycle 2 12 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 2 11 true (1),
.split 19 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 12 14 false (1),
.cycle 13 7 false (1),
.cycle 0 21 false (3),
.cycle 17 3 false (-1),
.last 20 (5,true),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 8 12 false (2),
.cycle 12 13 true (-2),
.cycle 12 8 false (1),
.cycle 16 6 false (0),
.cycle 13 7 false (1),
.cycle 23 1 false (1),
.cycle 17 3 false (-1),
.last 20 (5,true),
.last 35 (5,true),
.last 34 (5,true),
.cycle 2 18 false (3),
.cycle 28 36 true (-4),
.last 21 (5,true),
.last 34 (5,true)
]),
.split 12 (1,true) (byMove [
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 3 false (-1),
.cycle 0 16 true (-1),
.cycle 15 1 false (3),
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.last 13 (5,true),
.cycle 19 3 false (-1),
.cycle 13 3 false (0),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 15 3 false (-1),
.cycle 14 3 false (0),
.cycle 23 3 false (1),
.cycle 1 13 true (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.last 13 (5,true)
]),
.cycle 10 11 false (2),
.cycle 15 1 false (3),
.cycle 12 4 false (0),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 0 16 true (-1),
.cycle 15 1 false (3),
.last 13 (1,true),
.cycle 15 3 false (0),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.cycle 22 3 false (3),
.last 14 (1,true),
.cycle 14 3 false (0),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 13 3 false (0),
.cycle 22 3 false (1),
.last 13 (1,true),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.cycle 2 13 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 22 1 false (-2),
.last 16 (1,true),
.cycle 14 6 false (1),
.last 32 (1,true),
.cycle 34 1 false (6),
.last 14 (1,true),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 2 14 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.cycle 11 5 true (0),
.cycle 14 5 false (0),
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 11 3 true (1),
.cycle 2 14 true (1)
]),
.cycle 2 11 true (1)
])
theorem kid04_part807_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part807) = true := by rfl

def kid04_part808 : Audit := .cycle 0 11 true (0)
theorem kid04_part808_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part808) = true := by rfl

def kid04_part810 : Audit := .cycle 24 1 false (2)
theorem kid04_part810_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part810) = true := by rfl

def kid04_part811 : Audit := .split 11 (1,true) (byMove [
.cycle 14 1 false (2),
.cycle 12 11 false (1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 20 4 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.last 14 (5,true),
.cycle 11 8 false (1),
.cycle 12 14 false (0),
.cycle 0 26 true (-3),
.cycle 15 1 false (3),
.cycle 0 16 true (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.last 13 (5,true),
.last 14 (5,true)
])
theorem kid04_part811_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part811) = true := by rfl

def kid04_part812 : Audit := .cycle 14 1 false (0)
theorem kid04_part812_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part812) = true := by rfl

def kid04_part813 : Audit := .cycle 0 12 true (0)
theorem kid04_part813_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part813) = true := by rfl

def kid04_part814 : Audit := .cycle 11 4 false (1)
theorem kid04_part814_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part814) = true := by rfl

def kid04_part815 : Audit := .split 11 (5,true) (byMove [
.cycle 14 1 false (2),
.last 12 (1,true),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 11 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 26 true (-3),
.cycle 15 1 false (3),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.cycle 10 4 true (1),
.cycle 11 4 true (1)
])
theorem kid04_part815_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part815) = true := by rfl

def kid04_part816 : Audit := .cycle 0 11 true (0)
theorem kid04_part816_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part816) = true := by rfl

def kid04_part817 : Audit := .cycle 1 10 true (1)
theorem kid04_part817_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part817) = true := by rfl

def kid04_part818 : Audit := .cycle 0 23 true (0)
theorem kid04_part818_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part818) = true := by rfl

def kid04_part819 : Audit := .cycle 3 8 true (1)
theorem kid04_part819_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part819) = true := by rfl

def kid04_part820 : Audit := .cycle 8 3 true (1)
theorem kid04_part820_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part820) = true := by rfl

def kid04_part821 : Audit := .split 13 (5,true) (byMove [
.cycle 10 7 true (2),
.cycle 0 17 true (0),
.cycle 9 14 true (1),
.cycle 0 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 18 3 false (0),
.cycle 13 16 true (1),
.last 14 (1,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3),
.last 15 (1,true),
.cycle 9 8 true (1),
.cycle 13 18 true (1),
.cycle 9 12 true (1),
.cycle 17 6 false (1),
.cycle 9 8 true (1),
.cycle 9 16 true (1),
.last 14 (1,true),
.cycle 10 5 true (2),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3)
])
theorem kid04_part821_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part821) = true := by rfl

def kid04_part822 : Audit := .split 14 (5,true) (byMove [
.cycle 18 5 false (0),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 13 3 false (1),
.cycle 17 1 false (3),
.last 15 (1,true),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 17 (1,true),
.cycle 13 4 true (0),
.last 16 (1,true),
.last 19 (1,true),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (0),
.cycle 21 5 false (2),
.last 15 (1,true),
.last 18 (1,true),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.cycle 13 4 true (0)
])
theorem kid04_part822_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part822) = true := by rfl

def kid04_part823 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.cycle 18 1 false (-2),
.cycle 0 16 true (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 30 1 false (6),
.cycle 1 12 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 17 3 false (1),
.last 12 (5,true),
.cycle 11 8 false (1),
.cycle 13 3 false (0),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 0 27 true (0),
.cycle 1 12 true (1),
.cycle 15 3 false (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true)
])
theorem kid04_part823_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part823) = true := by rfl

def kid04_part824 : Audit := .split 16 (1,true) (byMove [
.cycle 19 1 false (3),
.cycle 24 4 false (2),
.cycle 17 4 false (1),
.cycle 0 18 true (-1),
.cycle 0 20 true (-1),
.last 17 (5,true),
.cycle 0 17 true (-1),
.last 29 (5,true),
.cycle 23 4 false (3),
.cycle 21 4 false (3),
.cycle 8 9 true (-1),
.last 19 (5,true),
.cycle 18 4 false (2),
.cycle 11 8 true (-1),
.cycle 17 4 false (1),
.cycle 20 1 false (4),
.cycle 22 1 false (4),
.last 17 (5,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 64, 1024, 128, 256, 32768, 1048580, 1073741824, 1024, 33554432, 67108864, 2097152, 128, 64, 268435456, 33554432, 67108864, 134217728, 64, 1090519104, 268435456, 33554432, 67108864, 134217728, 1191198912, 1090519104, 268435456, 1073741824],[4, 64, 128, 1, 1, 1073741824, 16384, 64, 128, 4096, 64, 1073741824, 1048576, 16777216, 1073741824, 262144, 262144, 1073741824, 67108864, 16777216, 128, 16777216, 16777216, 1073741824, 67108864, 16777216, 1107296384, 16777216, 1090519104, 1073741824, 1073741824],2145271328⟩,
.cycle 28 4 false (2),
.cycle 2 15 true (-1),
.cycle 27 4 false (3),
.last 18 (5,true),
.last 19 (5,true)
])
theorem kid04_part824_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part824) = true := by rfl

def kid04_part825 : Audit := .cycle 30 1 false (6)
theorem kid04_part825_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part825) = true := by rfl

def kid04_part826 : Audit := .cycle 11 4 false (1)
theorem kid04_part826_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part826) = true := by rfl

def kid04_part827 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 18 1 false (-2),
.last 14 (1,true),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 30 1 false (6),
.last 12 (1,true),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.cycle 11 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 0 27 true (0),
.last 12 (1,true),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 11 4 true (1)
])
theorem kid04_part827_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part827) = true := by rfl

def kid04_part828 : Audit := .cycle 0 11 true (0)
theorem kid04_part828_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part828) = true := by rfl

def kid04_part829 : Audit := .cycle 1 10 true (1)
theorem kid04_part829_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part829) = true := by rfl

def kid04_part830 : Audit := .cycle 2 9 true (1)
theorem kid04_part830_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part830) = true := by rfl

def kid04_part831 : Audit := .cycle 4 28 true (1)
theorem kid04_part831_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part831) = true := by rfl

def kid04_part832 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 18 1 false (0),
.last 15 (1,true),
.cycle 13 8 false (2),
.cycle 14 3 false (0),
.cycle 6 28 true (1),
.last 13 (1,true),
.cycle 14 9 false (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 4 true (2),
.last 18 (1,true),
.last 13 (1,true),
.cycle 20 6 false (2),
.cycle 5 8 true (1),
.cycle 10 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 11 17 true (2),
.last 13 (1,true),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 4 true (2)
])
theorem kid04_part832_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part832) = true := by rfl

def kid04_part833 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 15 12 false (3),
.last 16 (1,true),
.cycle 9 6 true (1),
.cycle 16 3 false (0),
.cycle 0 29 true (0),
.last 14 (1,true),
.cycle 15 13 false (3),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3),
.last 43 (1,true),
.last 14 (1,true),
.cycle 9 12 true (1),
.cycle 5 9 true (1),
.cycle 13 2 true (2),
.cycle 14 5 false (2),
.cycle 9 16 true (1),
.last 14 (1,true),
.cycle 10 5 true (2),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 11 4 true (3)
])
theorem kid04_part833_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part833) = true := by rfl

def kid04_part809 : Audit := .split 10 (4,true) (byMove [(kid04_part810),(kid04_part811),(kid04_part812),(kid04_part813),(kid04_part814),(kid04_part815),(kid04_part816),(kid04_part817),(kid04_part818),(kid04_part819),(kid04_part820),(kid04_part821),(kid04_part822),(kid04_part823),(kid04_part824),(kid04_part825),(kid04_part826),(kid04_part827),(kid04_part828),(kid04_part829),(kid04_part830),(kid04_part831),(kid04_part832),(kid04_part833)])

theorem kid04_part809_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part809) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid04_part810),(kid04_part811),(kid04_part812),(kid04_part813),(kid04_part814),(kid04_part815),(kid04_part816),(kid04_part817),(kid04_part818),(kid04_part819),(kid04_part820),(kid04_part821),(kid04_part822),(kid04_part823),(kid04_part824),(kid04_part825),(kid04_part826),(kid04_part827),(kid04_part828),(kid04_part829),(kid04_part830),(kid04_part831),(kid04_part832),(kid04_part833)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part810_checked

  · exact kid04_part816_checked

  · exact kid04_part822_checked

  · exact kid04_part828_checked

  · exact kid04_part811_checked

  · exact kid04_part817_checked

  · exact kid04_part823_checked

  · exact kid04_part829_checked

  · exact kid04_part812_checked

  · exact kid04_part818_checked

  · exact kid04_part824_checked

  · exact kid04_part830_checked

  · exact kid04_part813_checked

  · exact kid04_part819_checked

  · exact kid04_part825_checked

  · exact kid04_part831_checked

  · exact kid04_part814_checked

  · exact kid04_part820_checked

  · exact kid04_part826_checked

  · exact kid04_part832_checked

  · exact kid04_part815_checked

  · exact kid04_part821_checked

  · exact kid04_part827_checked

  · exact kid04_part833_checked

def kid04_part835 : Audit := .cycle 24 1 false (2)
theorem kid04_part835_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part835) = true := by rfl

def kid04_part836 : Audit := .split 11 (1,true) (byMove [
.cycle 14 1 false (2),
.cycle 12 11 false (1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 24 1 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 12 1 true (2),
.cycle 11 8 false (1),
.last 15 (4,true),
.last 22 (4,true),
.cycle 15 1 false (3),
.last 12 (4,true),
.cycle 0 16 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.last 41 (4,true),
.cycle 12 1 true (2)
])
theorem kid04_part836_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part836) = true := by rfl

def kid04_part837 : Audit := .split 12 (4,true) (byMove [
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
.last 14 (1,true),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (0),
.cycle 13 1 true (1)
])
theorem kid04_part837_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part837) = true := by rfl

def kid04_part838 : Audit := .cycle 0 12 true (0)
theorem kid04_part838_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part838) = true := by rfl

def kid04_part839 : Audit := .split 11 (4,true) (byMove [
.cycle 14 1 false (2),
.last 12 (1,true),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.cycle 17 1 true (-3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (1),
.cycle 12 1 true (2),
.last 19 (1,true),
.last 12 (1,true),
.cycle 11 11 false (1),
.cycle 15 1 false (3),
.cycle 12 4 false (0),
.cycle 14 3 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.cycle 13 6 false (1),
.cycle 12 1 true (2)
])
theorem kid04_part839_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part839) = true := by rfl

def kid04_part840 : Audit := .cycle 13 1 true (-1)
theorem kid04_part840_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part840) = true := by rfl

def kid04_part841 : Audit := .cycle 0 11 true (0)
theorem kid04_part841_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part841) = true := by rfl

def kid04_part842 : Audit := .cycle 1 10 true (1)
theorem kid04_part842_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part842) = true := by rfl

def kid04_part843 : Audit := .cycle 0 23 true (0)
theorem kid04_part843_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part843) = true := by rfl

def kid04_part844 : Audit := .cycle 3 8 true (1)
theorem kid04_part844_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part844) = true := by rfl

def kid04_part845 : Audit := .cycle 8 3 true (1)
theorem kid04_part845_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part845) = true := by rfl

def kid04_part846 : Audit := .cycle 11 1 true (3)
theorem kid04_part846_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part846) = true := by rfl

def kid04_part847 : Audit := .split 16 (1,true) (byMove [
.cycle 0 20 true (-1),
.cycle 23 5 false (0),
.cycle 17 5 false (-1),
.cycle 0 21 true (-1),
.last 17 (4,true),
.cycle 14 3 false (0),
.cycle 24 5 false (1),
.cycle 6 27 false (4),
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 20 1 true (2),
.cycle 17 5 false (0),
.last 20 (4,true),
.cycle 17 5 false (-1),
.cycle 18 5 false (1),
.last 17 (4,true),
.cycle 14 3 false (0),
.cycle 3 17 false (3),
.last 41 (4,true),
.last 18 (4,true),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 10 7 false (2)
])
theorem kid04_part847_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part847) = true := by rfl

def kid04_part848 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.cycle 18 1 false (-2),
.cycle 0 16 true (0),
.last 12 (4,true),
.last 15 (4,true),
.cycle 30 1 false (6),
.cycle 1 12 true (1),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 15 (4,true),
.cycle 11 8 false (1),
.last 15 (4,true),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 15 (4,true),
.cycle 0 27 true (0),
.cycle 1 12 true (1),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1)
])
theorem kid04_part848_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part848) = true := by rfl

def kid04_part849 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 0 29 true (-2),
.last 14 (1,true),
.cycle 22 4 false (4),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 13 4 false (2),
.last 14 (1,true),
.cycle 11 3 false (1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 13 4 false (0),
.last 14 (1,true),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.cycle 18 4 false (2),
.cycle 9 4 true (0)
])
theorem kid04_part849_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part849) = true := by rfl

def kid04_part850 : Audit := .cycle 30 1 false (6)
theorem kid04_part850_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part850) = true := by rfl

def kid04_part851 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 18 1 false (-2),
.last 14 (1,true),
.cycle 12 4 false (0),
.cycle 9 9 false (2),
.cycle 30 1 false (6),
.last 12 (1,true),
.cycle 15 5 false (-1),
.cycle 0 13 true (0),
.cycle 8 5 true (1),
.cycle 14 5 false (0),
.last 19 (1,true),
.last 12 (1,true),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.cycle 12 4 false (0),
.cycle 14 3 false (-1),
.cycle 0 27 true (0),
.last 12 (1,true),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 11 5 true (1),
.cycle 10 2 true (1)
])
theorem kid04_part851_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part851) = true := by rfl

def kid04_part852 : Audit := .cycle 11 3 false (1)
theorem kid04_part852_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part852) = true := by rfl

def kid04_part853 : Audit := .cycle 0 11 true (0)
theorem kid04_part853_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part853) = true := by rfl

def kid04_part854 : Audit := .cycle 1 10 true (1)
theorem kid04_part854_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part854) = true := by rfl

def kid04_part855 : Audit := .cycle 2 9 true (1)
theorem kid04_part855_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part855) = true := by rfl

def kid04_part856 : Audit := .cycle 4 28 true (1)
theorem kid04_part856_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part856) = true := by rfl

def kid04_part857 : Audit := .split 13 (4,true) (byMove [
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 26 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 8 false (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 17 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (1),
.cycle 14 1 true (4),
.cycle 16 13 false (2),
.last 14 (1,true),
.last 28 (1,true),
.cycle 5 34 true (1),
.cycle 14 6 false (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 11 3 true (2),
.cycle 14 1 true (4)
])
theorem kid04_part857_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part857) = true := by rfl

def kid04_part858 : Audit := .cycle 11 1 true (3)
theorem kid04_part858_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part858) = true := by rfl

def kid04_part834 : Audit := .split 10 (5,true) (byMove [(kid04_part835),(kid04_part836),(kid04_part837),(kid04_part838),(kid04_part839),(kid04_part840),(kid04_part841),(kid04_part842),(kid04_part843),(kid04_part844),(kid04_part845),(kid04_part846),(kid04_part847),(kid04_part848),(kid04_part849),(kid04_part850),(kid04_part851),(kid04_part852),(kid04_part853),(kid04_part854),(kid04_part855),(kid04_part856),(kid04_part857),(kid04_part858)])

theorem kid04_part834_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part834) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part835),(kid04_part836),(kid04_part837),(kid04_part838),(kid04_part839),(kid04_part840),(kid04_part841),(kid04_part842),(kid04_part843),(kid04_part844),(kid04_part845),(kid04_part846),(kid04_part847),(kid04_part848),(kid04_part849),(kid04_part850),(kid04_part851),(kid04_part852),(kid04_part853),(kid04_part854),(kid04_part855),(kid04_part856),(kid04_part857),(kid04_part858)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part835_checked

  · exact kid04_part841_checked

  · exact kid04_part847_checked

  · exact kid04_part853_checked

  · exact kid04_part836_checked

  · exact kid04_part842_checked

  · exact kid04_part848_checked

  · exact kid04_part854_checked

  · exact kid04_part837_checked

  · exact kid04_part843_checked

  · exact kid04_part849_checked

  · exact kid04_part855_checked

  · exact kid04_part838_checked

  · exact kid04_part844_checked

  · exact kid04_part850_checked

  · exact kid04_part856_checked

  · exact kid04_part839_checked

  · exact kid04_part845_checked

  · exact kid04_part851_checked

  · exact kid04_part857_checked

  · exact kid04_part840_checked

  · exact kid04_part846_checked

  · exact kid04_part852_checked

  · exact kid04_part858_checked

def kid04_part594 : Audit := .split 9 (5,false) (byMove [(kid04_part595),(kid04_part596),(kid04_part621),(kid04_part622),(kid04_part623),(kid04_part624),(kid04_part649),(kid04_part650),(kid04_part651),(kid04_part676),(kid04_part677),(kid04_part678),(kid04_part679),(kid04_part704),(kid04_part729),(kid04_part730),(kid04_part731),(kid04_part756),(kid04_part781),(kid04_part782),(kid04_part807),(kid04_part808),(kid04_part809),(kid04_part834)])

theorem kid04_part594_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (kid04_part594) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part595),(kid04_part596),(kid04_part621),(kid04_part622),(kid04_part623),(kid04_part624),(kid04_part649),(kid04_part650),(kid04_part651),(kid04_part676),(kid04_part677),(kid04_part678),(kid04_part679),(kid04_part704),(kid04_part729),(kid04_part730),(kid04_part731),(kid04_part756),(kid04_part781),(kid04_part782),(kid04_part807),(kid04_part808),(kid04_part809),(kid04_part834)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part595_checked

  · exact kid04_part649_checked

  · exact kid04_part679_checked

  · exact kid04_part781_checked

  · exact kid04_part596_checked

  · exact kid04_part650_checked

  · exact kid04_part704_checked

  · exact kid04_part782_checked

  · exact kid04_part621_checked

  · exact kid04_part651_checked

  · exact kid04_part729_checked

  · exact kid04_part807_checked

  · exact kid04_part622_checked

  · exact kid04_part676_checked

  · exact kid04_part730_checked

  · exact kid04_part808_checked

  · exact kid04_part623_checked

  · exact kid04_part677_checked

  · exact kid04_part731_checked

  · exact kid04_part809_checked

  · exact kid04_part624_checked

  · exact kid04_part678_checked

  · exact kid04_part756_checked

  · exact kid04_part834_checked

def kid04_part859 : Audit := .cycle 0 9 true (0)
theorem kid04_part859_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,0⟩)) (kid04_part859) = true := by rfl

def kid04_part860 : Audit := .cycle 1 8 true (1)
theorem kid04_part860_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,1⟩)) (kid04_part860) = true := by rfl

def kid04_part861 : Audit := .cycle 2 7 true (1)
theorem kid04_part861_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,2⟩)) (kid04_part861) = true := by rfl

def kid04_part862 : Audit := .cycle 41 1 false (7)
theorem kid04_part862_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,3⟩)) (kid04_part862) = true := by rfl

def kid04_part863 : Audit := .cycle 8 1 true (2)
theorem kid04_part863_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,4⟩)) (kid04_part863) = true := by rfl

def kid04_part865 : Audit := .cycle 26 1 false (6)
theorem kid04_part865_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part865) = true := by rfl

def kid04_part866 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 15 1 false (3),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (0),
.cycle 0 15 true (0),
.cycle 22 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.cycle 23 3 false (2),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 0 19 true (-2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 3 false (2),
.cycle 19 1 false (3),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
]),
.cycle 11 11 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 8 3 true (2),
.cycle 1 11 true (1),
.cycle 17 7 false (1),
.split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 18 6 false (0),
.cycle 15 3 false (0),
.cycle 11 13 false (2),
.cycle 17 1 false (3),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.last 23 (5,true),
.cycle 16 5 false (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 28 1 false (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 13 14 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 1 13 true (1),
.last 18 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 34 1 false (6),
.last 13 (4,true),
.cycle 64 35 true (-4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.last 16 (4,true),
.last 15 (4,true)
]),
.split 19 (5,true) (byMove [
.last 23 (4,true),
.cycle 0 23 true (-2),
.cycle 11 17 false (2),
.last 35 (4,true),
.cycle 8 12 false (3),
.cycle 1 20 false (3),
.cycle 11 110 true (-5),
.cycle 0 25 true (-2),
.cycle 0 28 true (-2),
.cycle 0 21 true (-2),
.last 20 (4,true),
.cycle 0 36 true (-2),
.cycle 11 18 false (2),
.last 22 (4,true),
.cycle 11 122 true (-5),
.cycle 11 15 false (2),
.last 22 (4,true),
.cycle 73 46 true (-1),
.cycle 11 18 true (-2),
.cycle 18 2 true (1),
.last 21 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 133, 2048, 8, 128, 256, 8, 4, 2048, 128, 4096],[4, 1, 128, 1, 4096, 512, 4, 1, 4096, 1, 4096, 512, 4096],4096⟩,
.last 20 (4,true),
.cycle 18 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 51 1 false (7),
.cycle 8 3 true (2),
.cycle 9 2 true (2)
])
theorem kid04_part866_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part866) = true := by rfl

def kid04_part867 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.cycle 17 1 false (1),
.split 16 (1,true) (byMove [
.cycle 19 1 false (1),
.cycle 24 3 false (0),
.cycle 17 3 false (-1),
.cycle 0 18 true (-1),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 8 9 false (3),
.cycle 23 3 false (1),
.cycle 18 3 false (0),
.cycle 13 6 false (1),
.cycle 17 3 false (-1),
.cycle 20 1 false (2),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 10 23 false (4),
.cycle 32 3 false (0),
.cycle 2 15 false (3),
.cycle 27 3 false (1),
.cycle 22 3 false (0),
.cycle 12 5 false (2)
]),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.split 16 (5,true) (byMove [
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 17 3 false (-1),
.cycle 0 18 true (-1),
.cycle 14 3 false (0),
.cycle 20 1 false (-2),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 8 9 false (3),
.cycle 23 3 false (1),
.cycle 18 3 false (0),
.last 17 (1,true),
.cycle 17 3 false (-1),
.cycle 20 1 false (2),
.cycle 14 3 false (0),
.cycle 20 1 false (-2),
.cycle 347 223 false (-1),
.last 34 (1,true),
.cycle 2 15 false (3),
.cycle 27 3 false (1),
.cycle 20 5 false (0),
.cycle 12 5 false (2)
]),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 19 1 false (3),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
])
theorem kid04_part867_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part867) = true := by rfl

def kid04_part868 : Audit := .cycle 0 11 true (0)
theorem kid04_part868_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part868) = true := by rfl

def kid04_part869 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 15 1 false (3),
.cycle 14 3 false (0),
.cycle 11 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 8 3 true (2),
.cycle 8 4 true (2),
.split 12 (1,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 13 false (1),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 19 11 false (2),
.cycle 18 7 false (1),
.cycle 13 6 false (1),
.cycle 14 6 false (0),
.cycle 34 1 false (6),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 18 15 false (3),
.cycle 18 9 false (2)
]),
.split 14 (1,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 3 false (-1),
.cycle 18 3 false (-2),
.cycle 17 1 false (3),
.cycle 25 3 false (3),
.cycle 18 3 false (0),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.last 15 (5,true),
.cycle 21 3 false (-1),
.cycle 15 3 false (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 18 3 false (-2),
.cycle 25 3 false (1),
.cycle 1 15 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 28 1 false (2),
.last 13 (1,true),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.cycle 13 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 0, 64],[4, 64, 0, 1, 32, 32, 64],64⟩,
.cycle 18 7 false (0),
.last 13 (1,true),
.cycle 14 6 false (0),
.cycle 34 1 false (6),
.cycle 14 3 false (0),
.cycle 13 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 16 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 0, 64],[4, 64, 0, 1, 32, 32, 64],64⟩
]),
.cycle 11 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 51 1 false (7),
.cycle 8 3 true (2),
.cycle 9 2 true (2)
])
theorem kid04_part869_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part869) = true := by rfl

def kid04_part870 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 15 1 false (3),
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
.last 16 (1,true),
.cycle 14 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 3 false (2),
.cycle 19 1 false (3),
.cycle 11 4 true (0),
.cycle 15 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 8 3 true (2),
.cycle 15 1 false (1),
.split 12 (1,true) (byMove [
.cycle 28 1 false (2),
.cycle 13 13 false (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (1),
.cycle 19 5 false (1),
.cycle 18 7 false (1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 34 1 false (6),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 18 15 false (3),
.cycle 18 9 false (2)
]),
.split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 8 6 true (1),
.cycle 20 1 false (0),
.last 23 (1,true),
.last 14 (1,true),
.cycle 11 13 false (2),
.cycle 17 1 false (3),
.last 17 (1,true),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.last 17 (1,true),
.last 16 (1,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 22 1 false (-2),
.last 16 (1,true),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 34 1 false (6),
.last 14 (1,true),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 8 7 true (1),
.cycle 10 4 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.cycle 18 1 false (-2),
.cycle 0 31 true (0),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 0 15 true (0),
.cycle 12 5 true (1),
.cycle 12 2 true (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 51 1 false (7),
.cycle 8 3 true (2),
.cycle 9 2 true (2)
])
theorem kid04_part870_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part870) = true := by rfl

def kid04_part871 : Audit := .cycle 0 10 true (0)
theorem kid04_part871_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part871) = true := by rfl

def kid04_part872 : Audit := .cycle 1 9 true (1)
theorem kid04_part872_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part872) = true := by rfl

def kid04_part873 : Audit := .cycle 7 12 true (2)
theorem kid04_part873_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part873) = true := by rfl

def kid04_part874 : Audit := .cycle 3 7 true (1)
theorem kid04_part874_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part874) = true := by rfl

def kid04_part875 : Audit := .cycle 8 2 true (2)
theorem kid04_part875_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part875) = true := by rfl

def kid04_part876 : Audit := .cycle 9 1 true (3)
theorem kid04_part876_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part876) = true := by rfl

def kid04_part877 : Audit := .cycle 6 4 true (2)
theorem kid04_part877_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part877) = true := by rfl

def kid04_part879 : Audit := .split 14 (4,true) (byMove [
.cycle 32 1 false (2),
.cycle 18 1 false (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 15 8 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 12 4 true (2),
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.cycle 23 1 false (3),
.cycle 38 1 false (6),
.last 18 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.cycle 0 21 true (0),
.cycle 0 20 true (0)
])
theorem kid04_part879_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part879) = true := by rfl

def kid04_part880 : Audit := .cycle 0 14 true (0)
theorem kid04_part880_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part880) = true := by rfl

def kid04_part881 : Audit := .cycle 21 1 false (1)
theorem kid04_part881_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part881) = true := by rfl

def kid04_part882 : Audit := .cycle 0 16 true (0)
theorem kid04_part882_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part882) = true := by rfl

def kid04_part883 : Audit := .split 14 (4,true) (byMove [
.cycle 54 1 false (0),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 14 4 false (0),
.cycle 0 21 true (0),
.cycle 28 3 false (5),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 16 (5,true),
.cycle 14 4 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 14 4 false (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 3 false (2),
.cycle 19 3 false (2),
.last 16 (5,true),
.cycle 15 3 false (1)
])
theorem kid04_part883_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part883) = true := by rfl

def kid04_part884 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 11 14 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 11 7 false (1),
.cycle 13 4 false (-1),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 2048, 128, 524288, 1048576, 32768, 4, 8388608, 128, 128, 256, 8, 128, 2048, 128, 2147483648, 4294967296, 134217728, 4, 34359738368, 68719476736, 2147483648, 4294967296, 8589934592, 128, 34359738368, 70866960384, 2147483648, 4294967296, 8589934592, 75161927680, 34359738368, 70866960384, 68719476736],[4, 1048576, 128, 1, 1, 68719476736, 16384, 68719476736, 128, 4096, 4096, 68719476736, 4, 1048576, 68719476736, 1, 1, 68719476736, 67108864, 68719476736, 128, 16777216, 16777216, 68719476736, 4294967296, 68719476736, 70866960384, 1073741824, 1073741824, 68719476736, 4294967296, 73014444032, 70866960384, 1073741824, 1073741824, 68719476736, 68719476736],137303443020⟩,
.last 22 (5,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 7 false (1),
.cycle 13 4 true (-2),
.last 19 (5,true),
.cycle 14 3 false (-1),
.cycle 11 14 false (1),
.cycle 17 1 false (-3),
.last 18 (5,true),
.cycle 13 4 false (-1),
.last 38 (5,true),
.last 22 (5,true),
.cycle 11 13 false (1),
.last 24 (5,true),
.last 20 (5,true),
.cycle 11 6 false (1)
])
theorem kid04_part884_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part884) = true := by rfl

def kid04_part885 : Audit := .cycle 41 1 false (7)
theorem kid04_part885_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part885) = true := by rfl

def kid04_part886 : Audit := .cycle 1 11 true (1)
theorem kid04_part886_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part886) = true := by rfl

def kid04_part887 : Audit := .cycle 7 4 true (2)
theorem kid04_part887_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part887) = true := by rfl

def kid04_part888 : Audit := .cycle 0 12 true (0)
theorem kid04_part888_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part888) = true := by rfl

def kid04_part889 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.cycle 11 4 true (3),
.cycle 8 6 true (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part889_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part889) = true := by rfl

def kid04_part890 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part890_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part890) = true := by rfl

def kid04_part891 : Audit := .cycle 17 7 false (1)
theorem kid04_part891_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part891) = true := by rfl

def kid04_part892 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 20 true (0),
.cycle 14 6 false (0),
.last 14 (5,true),
.cycle 10 6 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 15 (5,true),
.cycle 11 4 true (1),
.cycle 18 6 false (0),
.cycle 15 3 false (0),
.cycle 17 8 true (-3),
.cycle 0 18 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 16 7 false (2),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 16 5 false (0)
])
theorem kid04_part892_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part892) = true := by rfl

def kid04_part893 : Audit := .cycle 51 1 false (7)
theorem kid04_part893_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part893) = true := by rfl

def kid04_part894 : Audit := .cycle 18 1 false (0)
theorem kid04_part894_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part894) = true := by rfl

def kid04_part895 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 14 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 18 (4,true),
.cycle 6 28 true (1),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 17 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 18 (4,true),
.last 31 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid04_part895_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part895) = true := by rfl

def kid04_part896 : Audit := .split 16 (4,true) (byMove [
.cycle 11 28 false (2),
.cycle 11 14 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 11 7 false (1),
.cycle 13 4 false (-1),
.last 19 (5,true),
.cycle 20 20 true (0),
.cycle 43 1 false (5),
.cycle 17 1 false (-1),
.last 18 (5,true),
.cycle 13 4 true (-2),
.last 19 (5,true),
.cycle 14 3 false (-1),
.last 21 (5,true),
.cycle 17 1 false (-3),
.last 18 (5,true),
.cycle 13 4 false (-1),
.last 19 (5,true),
.last 41 (5,true),
.last 56 (5,true),
.cycle 11 11 false (1),
.last 18 (5,true),
.cycle 11 6 false (1)
])
theorem kid04_part896_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part896) = true := by rfl

def kid04_part897 : Audit := .cycle 6 16 true (2)
theorem kid04_part897_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part897) = true := by rfl

def kid04_part898 : Audit := .cycle 1 11 true (1)
theorem kid04_part898_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part898) = true := by rfl

def kid04_part899 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 18 5 false (0),
.cycle 15 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 11 4 true (2),
.cycle 2 13 true (1),
.cycle 17 3 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 15 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 8 5 true (2),
.cycle 9 4 true (2)
])
theorem kid04_part899_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part899) = true := by rfl

def kid04_part900 : Audit := .cycle 0 12 true (0)
theorem kid04_part900_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part900) = true := by rfl

def kid04_part901 : Audit := .split 11 (4,true) (byMove [
.cycle 30 1 false (6),
.cycle 8 5 true (2),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 17 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 11 4 true (3),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 35 5 false (3),
.cycle 51 1 false (7),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part901_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part901) = true := by rfl

def kid04_part902 : Audit := .split 11 (5,true) (byMove [
.cycle 30 1 false (6),
.cycle 9 4 true (2),
.last 18 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 20 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.last 15 (4,true),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.last 18 (4,true),
.cycle 51 1 false (7),
.last 12 (4,true),
.last 20 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part902_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part902) = true := by rfl

def kid04_part878 : Audit := .split 10 (1,true) (byMove [(kid04_part879),(kid04_part880),(kid04_part881),(kid04_part882),(kid04_part883),(kid04_part884),(kid04_part885),(kid04_part886),(kid04_part887),(kid04_part888),(kid04_part889),(kid04_part890),(kid04_part891),(kid04_part892),(kid04_part893),(kid04_part894),(kid04_part895),(kid04_part896),(kid04_part897),(kid04_part898),(kid04_part899),(kid04_part900),(kid04_part901),(kid04_part902)])

theorem kid04_part878_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part878) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part879),(kid04_part880),(kid04_part881),(kid04_part882),(kid04_part883),(kid04_part884),(kid04_part885),(kid04_part886),(kid04_part887),(kid04_part888),(kid04_part889),(kid04_part890),(kid04_part891),(kid04_part892),(kid04_part893),(kid04_part894),(kid04_part895),(kid04_part896),(kid04_part897),(kid04_part898),(kid04_part899),(kid04_part900),(kid04_part901),(kid04_part902)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part879_checked

  · exact kid04_part885_checked

  · exact kid04_part891_checked

  · exact kid04_part897_checked

  · exact kid04_part880_checked

  · exact kid04_part886_checked

  · exact kid04_part892_checked

  · exact kid04_part898_checked

  · exact kid04_part881_checked

  · exact kid04_part887_checked

  · exact kid04_part893_checked

  · exact kid04_part899_checked

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

def kid04_part904 : Audit := .cycle 54 1 false (0)
theorem kid04_part904_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part904) = true := by rfl

def kid04_part905 : Audit := .cycle 21 3 false (1)
theorem kid04_part905_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part905) = true := by rfl

def kid04_part906 : Audit := .cycle 16 1 false (0)
theorem kid04_part906_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part906) = true := by rfl

def kid04_part907 : Audit := .cycle 15 1 false (-1)
theorem kid04_part907_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part907) = true := by rfl

def kid04_part908 : Audit := .cycle 15 3 false (0)
theorem kid04_part908_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part908) = true := by rfl

def kid04_part909 : Audit := .split 22 (5,true) (byMove [
.cycle 0 23 false (3),
.cycle 29 3 false (1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 23 3 false (0),
.cycle 0 30 true (-2),
.cycle 0 28 true (-2),
.cycle 0 26 true (-2),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 23 3 false (2),
.last 27 (1,true),
.last 24 (1,true),
.cycle 0 29 false (3),
.cycle 0 32 true (-2),
.cycle 23 1 false (-1),
.last 30 (1,true),
.cycle 28 1 false (2),
.cycle 18 26 true (0),
.cycle 0 26 true (-2),
.cycle 28 3 false (2),
.cycle 0 28 true (-2),
.cycle 11 12 true (-2),
.cycle 23 3 false (1)
])
theorem kid04_part909_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part909) = true := by rfl

def kid04_part910 : Audit := .split 16 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 24 3 false (2),
.cycle 17 3 false (1),
.cycle 0 21 true (0),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 25 3 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 7, 32, 7, 64],[4, 2, 7, 1, 1, 64, 64],64⟩,
.cycle 30 3 false (4),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 17 (5,true),
.cycle 18 3 false (2),
.cycle 13 6 true (0),
.cycle 17 3 false (1),
.cycle 19 3 false (3),
.cycle 19 3 false (3),
.last 17 (5,true),
.cycle 0 42 true (0),
.cycle 1 17 true (0),
.cycle 0 19 true (0),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 17 (5,true)
])
theorem kid04_part910_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part910) = true := by rfl

def kid04_part911 : Audit := .cycle 27 3 false (5)
theorem kid04_part911_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part911) = true := by rfl

def kid04_part912 : Audit := .cycle 19 1 false (5)
theorem kid04_part912_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part912) = true := by rfl

def kid04_part913 : Audit := .cycle 15 1 false (1)
theorem kid04_part913_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part913) = true := by rfl

def kid04_part914 : Audit := .split 16 (5,true) (byMove [
.cycle 0 20 true (0),
.last 17 (1,true),
.cycle 17 3 false (1),
.last 19 (1,true),
.cycle 21 3 false (4),
.cycle 8 17 true (-1),
.cycle 25 3 false (3),
.last 17 (1,true),
.cycle 30 3 false (4),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 32, 53, 64],[4, 64, 53, 1, 16, 16, 64],64⟩,
.cycle 0 21 true (0),
.cycle 18 3 false (2),
.last 17 (1,true),
.cycle 17 3 false (1),
.cycle 19 3 false (3),
.cycle 20 3 false (5),
.cycle 22 3 false (2),
.cycle 0 42 true (0),
.last 17 (1,true),
.cycle 8 11 true (0),
.cycle 0 18 true (0),
.cycle 8 10 true (0),
.cycle 17 5 true (2)
])
theorem kid04_part914_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part914) = true := by rfl

def kid04_part915 : Audit := .cycle 19 3 false (3)
theorem kid04_part915_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part915) = true := by rfl

def kid04_part916 : Audit := .split 16 (1,true) (byMove [
.cycle 19 1 false (1),
.cycle 24 3 false (0),
.cycle 17 3 false (-1),
.cycle 23 3 false (1),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 107 3 false (-1),
.cycle 119 3 false (-1),
.cycle 29 3 false (1),
.cycle 21 3 false (1),
.last 18 (5,true),
.cycle 7 17 false (3),
.cycle 18 3 false (0),
.cycle 13 6 false (1),
.cycle 17 3 false (-1),
.cycle 23 1 false (5),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 65 3 false (-1),
.cycle 10 11 false (2),
.cycle 53 3 false (-1),
.cycle 4 13 false (3),
.last 18 (5,true),
.cycle 12 5 false (2)
])
theorem kid04_part916_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part916) = true := by rfl

def kid04_part917 : Audit := .cycle 13 3 false (1)
theorem kid04_part917_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part917) = true := by rfl

def kid04_part918 : Audit := .split 18 (1,true) (byMove [
.cycle 0 22 true (-1),
.cycle 26 3 false (2),
.cycle 19 3 false (1),
.cycle 0 23 true (-1),
.cycle 0 27 true (-1),
.last 19 (5,true),
.cycle 27 3 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 32, 15, 64],[4, 2, 15, 1, 15, 64, 64],64⟩,
.cycle 34 3 false (4),
.cycle 0 20 true (-1),
.cycle 0 22 true (-1),
.last 19 (5,true),
.cycle 20 3 false (2),
.cycle 13 8 true (-1),
.cycle 19 3 false (1),
.cycle 21 3 false (3),
.cycle 23 3 false (3),
.last 19 (5,true),
.cycle 44 3 false (2),
.cycle 72 3 false (4),
.cycle 21 3 false (1),
.cycle 0 20 true (-1),
.cycle 30 3 false (2),
.last 19 (5,true)
])
theorem kid04_part918_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part918) = true := by rfl

def kid04_part919 : Audit := .cycle 15 1 false (-1)
theorem kid04_part919_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part919) = true := by rfl

def kid04_part920 : Audit := .split 16 (5,true) (byMove [
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 17 3 false (-1),
.last 27 (1,true),
.cycle 14 3 false (0),
.cycle 62 11 false (0),
.last 18 (1,true),
.last 48 (1,true),
.cycle 29 3 false (1),
.cycle 21 3 false (1),
.cycle 14 18 true (-1),
.cycle 7 17 false (3),
.cycle 18 3 false (0),
.last 17 (1,true),
.cycle 17 3 false (-1),
.cycle 23 1 false (5),
.cycle 14 3 false (0),
.cycle 22 3 false (0),
.last 18 (1,true),
.last 24 (1,true),
.cycle 50 5 false (0),
.cycle 4 13 false (3),
.cycle 21 5 false (1),
.cycle 12 5 false (2)
])
theorem kid04_part920_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part920) = true := by rfl

def kid04_part921 : Audit := .cycle 23 1 false (5)
theorem kid04_part921_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part921) = true := by rfl

def kid04_part922 : Audit := .split 16 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 25 3 false (1),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 6 40 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 7, 32, 7, 64],[4, 2, 7, 1, 1, 64, 64],64⟩,
.cycle 10 30 true (0),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 17 (5,true),
.cycle 10 8 true (0),
.cycle 13 7 false (2),
.cycle 13 4 true (0),
.cycle 5 12 true (0),
.cycle 10 36 true (0),
.last 17 (5,true),
.cycle 0 42 true (0),
.cycle 1 17 true (0),
.cycle 0 19 true (0),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 17 (5,true)
])
theorem kid04_part922_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part922) = true := by rfl

def kid04_part923 : Audit := .cycle 1 20 true (0)
theorem kid04_part923_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part923) = true := by rfl

def kid04_part924 : Audit := .cycle 26 3 false (2)
theorem kid04_part924_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part924) = true := by rfl

def kid04_part925 : Audit := .cycle 18 3 false (2)
theorem kid04_part925_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part925) = true := by rfl

def kid04_part926 : Audit := .split 16 (5,true) (byMove [
.cycle 0 20 true (0),
.last 17 (1,true),
.cycle 11 8 true (0),
.last 19 (1,true),
.cycle 17 7 true (1),
.cycle 0 26 true (-2),
.cycle 6 40 true (0),
.last 17 (1,true),
.cycle 10 30 true (0),
.cycle 0 18 true (0),
.cycle 8 16 true (0),
.cycle 0 21 true (0),
.cycle 10 8 true (0),
.last 17 (1,true),
.cycle 13 4 true (0),
.cycle 5 12 true (0),
.cycle 18 8 true (2),
.cycle 23 3 false (1),
.cycle 0 42 true (0),
.last 17 (1,true),
.cycle 2 23 true (0),
.cycle 0 18 true (0),
.cycle 18 6 true (3),
.cycle 17 5 true (2)
])
theorem kid04_part926_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part926) = true := by rfl

def kid04_part927 : Audit := .cycle 15 3 false (1)
theorem kid04_part927_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part927) = true := by rfl

def kid04_part903 : Audit := .split 14 (4,true) (byMove [(kid04_part904),(kid04_part905),(kid04_part906),(kid04_part907),(kid04_part908),(kid04_part909),(kid04_part910),(kid04_part911),(kid04_part912),(kid04_part913),(kid04_part914),(kid04_part915),(kid04_part916),(kid04_part917),(kid04_part918),(kid04_part919),(kid04_part920),(kid04_part921),(kid04_part922),(kid04_part923),(kid04_part924),(kid04_part925),(kid04_part926),(kid04_part927)])

theorem kid04_part903_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part903) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 14 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some mv)) (byMove [(kid04_part904),(kid04_part905),(kid04_part906),(kid04_part907),(kid04_part908),(kid04_part909),(kid04_part910),(kid04_part911),(kid04_part912),(kid04_part913),(kid04_part914),(kid04_part915),(kid04_part916),(kid04_part917),(kid04_part918),(kid04_part919),(kid04_part920),(kid04_part921),(kid04_part922),(kid04_part923),(kid04_part924),(kid04_part925),(kid04_part926),(kid04_part927)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part904_checked

  · exact kid04_part910_checked

  · exact kid04_part916_checked

  · exact kid04_part922_checked

  · exact kid04_part905_checked

  · exact kid04_part911_checked

  · exact kid04_part917_checked

  · exact kid04_part923_checked

  · exact kid04_part906_checked

  · exact kid04_part912_checked

  · exact kid04_part918_checked

  · exact kid04_part924_checked

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

def kid04_part928 : Audit := .cycle 41 1 false (7)
theorem kid04_part928_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part928) = true := by rfl

def kid04_part930 : Audit := .cycle 32 1 false (2)
theorem kid04_part930_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid04_part930) = true := by rfl

def kid04_part931 : Audit := .cycle 0 14 true (0)
theorem kid04_part931_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid04_part931) = true := by rfl

def kid04_part932 : Audit := .cycle 21 1 false (1)
theorem kid04_part932_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid04_part932) = true := by rfl

def kid04_part933 : Audit := .cycle 0 16 true (0)
theorem kid04_part933_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid04_part933) = true := by rfl

def kid04_part934 : Audit := .cycle 14 3 false (0)
theorem kid04_part934_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid04_part934) = true := by rfl

def kid04_part935 : Audit := .split 15 (5,true) (byMove [
.cycle 18 1 false (0),
.last 16 (1,true),
.cycle 11 7 false (1),
.cycle 22 1 false (-2),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.last 17 (1,true),
.cycle 10 8 false (2),
.last 19 (1,true),
.cycle 11 11 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 23 3 true (3),
.cycle 11 8 false (1),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 21 (1,true),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.last 17 (1,true),
.cycle 1 36 false (3),
.last 19 (1,true),
.cycle 4 12 false (3),
.cycle 17 6 true (1),
.cycle 11 8 false (1)
])
theorem kid04_part935_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid04_part935) = true := by rfl

def kid04_part936 : Audit := .cycle 41 1 false (7)
theorem kid04_part936_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid04_part936) = true := by rfl

def kid04_part937 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 6 8 true (2),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part937_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid04_part937) = true := by rfl

def kid04_part938 : Audit := .cycle 7 4 true (2)
theorem kid04_part938_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid04_part938) = true := by rfl

def kid04_part939 : Audit := .cycle 0 12 true (0)
theorem kid04_part939_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid04_part939) = true := by rfl

def kid04_part940 : Audit := .cycle 8 4 true (2)
theorem kid04_part940_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid04_part940) = true := by rfl

def kid04_part941 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.cycle 11 3 true (3),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part941_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid04_part941) = true := by rfl

def kid04_part942 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.cycle 14 6 false (0),
.cycle 0 17 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 6 28 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.cycle 8 8 true (1),
.last 13 (5,true),
.cycle 18 7 false (1),
.cycle 13 6 false (1),
.cycle 14 6 false (0),
.cycle 5 8 true (1),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 36 17 false (3),
.cycle 1 13 true (1),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 18 13 false (2),
.last 13 (5,true)
])
theorem kid04_part942_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid04_part942) = true := by rfl

def kid04_part943 : Audit := .split 14 (1,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 49 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 3 false (-1),
.last 17 (5,true),
.cycle 0 18 true (0),
.cycle 16 3 false (3),
.cycle 18 3 false (0),
.cycle 25 3 false (3),
.cycle 15 3 false (1),
.last 15 (5,true),
.cycle 21 3 false (-1),
.cycle 15 3 false (0),
.cycle 0 20 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.last 17 (5,true),
.cycle 0 18 true (0),
.cycle 1 20 true (0),
.cycle 15 3 false (1),
.cycle 0 49 true (0),
.cycle 13 2 true (0),
.last 15 (5,true)
])
theorem kid04_part943_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid04_part943) = true := by rfl

def kid04_part944 : Audit := .cycle 51 1 false (7)
theorem kid04_part944_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid04_part944) = true := by rfl

def kid04_part945 : Audit := .cycle 18 1 false (0)
theorem kid04_part945_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid04_part945) = true := by rfl

def kid04_part946 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 14 6 false (0),
.last 15 (1,true),
.cycle 14 3 false (0),
.cycle 13 4 false (1),
.cycle 6 28 true (1),
.last 13 (1,true),
.cycle 17 7 false (1),
.cycle 0 14 true (0),
.cycle 8 8 true (1),
.cycle 13 3 true (3),
.cycle 18 7 false (0),
.last 13 (1,true),
.cycle 14 6 false (0),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.cycle 13 4 false (1),
.cycle 32 9 false (2),
.last 13 (1,true),
.cycle 15 5 false (1),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩
])
theorem kid04_part946_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid04_part946) = true := by rfl

def kid04_part947 : Audit := .split 15 (5,true) (byMove [
.cycle 43 1 false (5),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 18 (1,true),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 6 10 false (3),
.last 16 (1,true),
.cycle 11 12 false (1),
.cycle 11 62 true (-2),
.cycle 10 6 false (2),
.cycle 19 3 true (3),
.cycle 11 8 false (1),
.last 16 (1,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 15 6 true (-1),
.last 16 (1,true),
.cycle 12 8 false (0),
.cycle 5 20 false (3),
.cycle 15 2 true (-1),
.cycle 17 5 true (1)
])
theorem kid04_part947_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid04_part947) = true := by rfl

def kid04_part948 : Audit := .cycle 6 16 true (2)
theorem kid04_part948_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid04_part948) = true := by rfl

def kid04_part949 : Audit := .split 11 (1,true) (byMove [
.cycle 30 1 false (6),
.cycle 1 12 true (1),
.cycle 1 18 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 1 18 true (1),
.cycle 1 24 true (0),
.cycle 51 1 false (7),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part949_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid04_part949) = true := by rfl

def kid04_part950 : Audit := .cycle 2 11 true (1)
theorem kid04_part950_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid04_part950) = true := by rfl

def kid04_part951 : Audit := .cycle 0 12 true (0)
theorem kid04_part951_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid04_part951) = true := by rfl

def kid04_part952 : Audit := .cycle 8 4 true (2)
theorem kid04_part952_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid04_part952) = true := by rfl

def kid04_part953 : Audit := .split 11 (5,true) (byMove [
.cycle 30 1 false (6),
.last 12 (1,true),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 9 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 11 3 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 19 5 false (1),
.cycle 51 1 false (7),
.cycle 10 2 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part953_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid04_part953) = true := by rfl

def kid04_part929 : Audit := .split 10 (4,true) (byMove [(kid04_part930),(kid04_part931),(kid04_part932),(kid04_part933),(kid04_part934),(kid04_part935),(kid04_part936),(kid04_part937),(kid04_part938),(kid04_part939),(kid04_part940),(kid04_part941),(kid04_part942),(kid04_part943),(kid04_part944),(kid04_part945),(kid04_part946),(kid04_part947),(kid04_part948),(kid04_part949),(kid04_part950),(kid04_part951),(kid04_part952),(kid04_part953)])

theorem kid04_part929_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part929) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid04_part930),(kid04_part931),(kid04_part932),(kid04_part933),(kid04_part934),(kid04_part935),(kid04_part936),(kid04_part937),(kid04_part938),(kid04_part939),(kid04_part940),(kid04_part941),(kid04_part942),(kid04_part943),(kid04_part944),(kid04_part945),(kid04_part946),(kid04_part947),(kid04_part948),(kid04_part949),(kid04_part950),(kid04_part951),(kid04_part952),(kid04_part953)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part930_checked

  · exact kid04_part936_checked

  · exact kid04_part942_checked

  · exact kid04_part948_checked

  · exact kid04_part931_checked

  · exact kid04_part937_checked

  · exact kid04_part943_checked

  · exact kid04_part949_checked

  · exact kid04_part932_checked

  · exact kid04_part938_checked

  · exact kid04_part944_checked

  · exact kid04_part950_checked

  · exact kid04_part933_checked

  · exact kid04_part939_checked

  · exact kid04_part945_checked

  · exact kid04_part951_checked

  · exact kid04_part934_checked

  · exact kid04_part940_checked

  · exact kid04_part946_checked

  · exact kid04_part952_checked

  · exact kid04_part935_checked

  · exact kid04_part941_checked

  · exact kid04_part947_checked

  · exact kid04_part953_checked

def kid04_part955 : Audit := .split 14 (4,true) (byMove [
.cycle 32 1 false (2),
.last 15 (1,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 15 8 false (1),
.cycle 18 1 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 23 1 false (5),
.cycle 0 23 true (0),
.last 15 (1,true),
.last 20 (1,true),
.cycle 38 1 false (6),
.cycle 24 1 false (4),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 4 40 true (1),
.cycle 0 21 true (0),
.cycle 0 20 true (0)
])
theorem kid04_part955_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part955) = true := by rfl

def kid04_part956 : Audit := .cycle 0 14 true (0)
theorem kid04_part956_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part956) = true := by rfl

def kid04_part957 : Audit := .cycle 21 1 false (1)
theorem kid04_part957_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part957) = true := by rfl

def kid04_part958 : Audit := .cycle 0 16 true (0)
theorem kid04_part958_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part958) = true := by rfl

def kid04_part959 : Audit := .split 14 (4,true) (byMove [
.cycle 54 1 false (0),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 28 3 false (5),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.cycle 21 3 false (4),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 14 3 false (0),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 1 20 true (0),
.cycle 27 3 false (2),
.cycle 19 3 false (2),
.cycle 16 7 true (1),
.cycle 15 3 false (1)
])
theorem kid04_part959_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part959) = true := by rfl

def kid04_part960 : Audit := .cycle 13 1 false (-1)
theorem kid04_part960_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part960) = true := by rfl

def kid04_part961 : Audit := .cycle 41 1 false (7)
theorem kid04_part961_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part961) = true := by rfl

def kid04_part962 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.cycle 32 1 false (8),
.cycle 6 8 true (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 1 13 true (1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part962_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part962) = true := by rfl

def kid04_part963 : Audit := .cycle 7 4 true (2)
theorem kid04_part963_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part963) = true := by rfl

def kid04_part964 : Audit := .cycle 0 12 true (0)
theorem kid04_part964_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part964) = true := by rfl

def kid04_part965 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 8 4 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 8 4 true (2),
.cycle 25 1 false (7),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 8 6 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part965_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part965) = true := by rfl

def kid04_part966 : Audit := .cycle 21 1 false (5)
theorem kid04_part966_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part966) = true := by rfl

def kid04_part967 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.last 14 (4,true),
.cycle 0 17 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 6 28 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 2048, 32, 128, 256, 8, 4, 2048, 32, 4096],[4, 32, 32, 1, 4096, 32, 4, 32, 4096, 1, 4096, 32, 4096],4096⟩,
.cycle 18 7 false (1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 36 17 false (3),
.cycle 1 13 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 13 false (2)
])
theorem kid04_part967_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part967) = true := by rfl

def kid04_part968 : Audit := .split 13 (4,true) (byMove [
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 22 1 false (-2),
.cycle 0 20 true (0),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.last 15 (1,true),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 16 (1,true),
.cycle 20 1 false (0),
.last 23 (1,true),
.last 14 (1,true),
.last 24 (1,true),
.cycle 0 18 true (0),
.last 17 (1,true),
.cycle 18 1 false (-2),
.last 15 (1,true),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (1,true),
.last 16 (1,true)
])
theorem kid04_part968_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part968) = true := by rfl

def kid04_part969 : Audit := .cycle 51 1 false (7)
theorem kid04_part969_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part969) = true := by rfl

def kid04_part970 : Audit := .cycle 18 1 false (0)
theorem kid04_part970_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part970) = true := by rfl

def kid04_part971 : Audit := .split 13 (4,true) (byMove [
.cycle 19 1 false (5),
.last 14 (1,true),
.cycle 22 1 false (-2),
.last 16 (1,true),
.cycle 14 6 false (0),
.cycle 18 1 false (-2),
.cycle 6 8 true (1),
.last 14 (1,true),
.cycle 17 7 false (1),
.cycle 61 1 false (7),
.cycle 8 8 true (1),
.cycle 10 4 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.cycle 18 1 false (-2),
.cycle 12 6 true (1),
.last 14 (1,true),
.cycle 0 18 true (0),
.cycle 5 34 true (1),
.cycle 12 6 true (1),
.cycle 12 2 true (1)
])
theorem kid04_part971_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part971) = true := by rfl

def kid04_part972 : Audit := .cycle 13 1 false (-1)
theorem kid04_part972_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part972) = true := by rfl

def kid04_part973 : Audit := .cycle 6 16 true (2)
theorem kid04_part973_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part973) = true := by rfl

def kid04_part974 : Audit := .split 11 (1,true) (byMove [
.cycle 30 1 false (6),
.cycle 1 12 true (1),
.last 18 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 1 16 true (1),
.cycle 6 6 true (2),
.last 15 (4,true),
.last 18 (4,true),
.cycle 51 1 false (7),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part974_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part974) = true := by rfl

def kid04_part975 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 18 5 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 19 1 false (1),
.last 14 (1,true),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 2 13 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 8 5 true (2),
.cycle 9 4 true (2)
])
theorem kid04_part975_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part975) = true := by rfl

def kid04_part976 : Audit := .cycle 0 12 true (0)
theorem kid04_part976_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part976) = true := by rfl

def kid04_part977 : Audit := .split 11 (4,true) (byMove [
.cycle 30 1 false (6),
.last 12 (1,true),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 17 5 false (1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 8 9 true (2),
.cycle 6 6 true (2),
.last 12 (1,true),
.last 22 (1,true),
.cycle 51 1 false (7),
.cycle 16 5 false (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 8 4 true (2),
.cycle 9 3 true (2)
])
theorem kid04_part977_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part977) = true := by rfl

def kid04_part978 : Audit := .cycle 9 3 true (2)
theorem kid04_part978_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part978) = true := by rfl

def kid04_part954 : Audit := .split 10 (5,true) (byMove [(kid04_part955),(kid04_part956),(kid04_part957),(kid04_part958),(kid04_part959),(kid04_part960),(kid04_part961),(kid04_part962),(kid04_part963),(kid04_part964),(kid04_part965),(kid04_part966),(kid04_part967),(kid04_part968),(kid04_part969),(kid04_part970),(kid04_part971),(kid04_part972),(kid04_part973),(kid04_part974),(kid04_part975),(kid04_part976),(kid04_part977),(kid04_part978)])

theorem kid04_part954_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part954) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part955),(kid04_part956),(kid04_part957),(kid04_part958),(kid04_part959),(kid04_part960),(kid04_part961),(kid04_part962),(kid04_part963),(kid04_part964),(kid04_part965),(kid04_part966),(kid04_part967),(kid04_part968),(kid04_part969),(kid04_part970),(kid04_part971),(kid04_part972),(kid04_part973),(kid04_part974),(kid04_part975),(kid04_part976),(kid04_part977),(kid04_part978)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part955_checked

  · exact kid04_part961_checked

  · exact kid04_part967_checked

  · exact kid04_part973_checked

  · exact kid04_part956_checked

  · exact kid04_part962_checked

  · exact kid04_part968_checked

  · exact kid04_part974_checked

  · exact kid04_part957_checked

  · exact kid04_part963_checked

  · exact kid04_part969_checked

  · exact kid04_part975_checked

  · exact kid04_part958_checked

  · exact kid04_part964_checked

  · exact kid04_part970_checked

  · exact kid04_part976_checked

  · exact kid04_part959_checked

  · exact kid04_part965_checked

  · exact kid04_part971_checked

  · exact kid04_part977_checked

  · exact kid04_part960_checked

  · exact kid04_part966_checked

  · exact kid04_part972_checked

  · exact kid04_part978_checked

def kid04_part979 : Audit := .cycle 0 10 true (0)
theorem kid04_part979_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part979) = true := by rfl

def kid04_part980 : Audit := .cycle 1 9 true (1)
theorem kid04_part980_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part980) = true := by rfl

def kid04_part981 : Audit := .cycle 2 8 true (1)
theorem kid04_part981_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part981) = true := by rfl

def kid04_part982 : Audit := .cycle 11 12 true (2)
theorem kid04_part982_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part982) = true := by rfl

def kid04_part983 : Audit := .cycle 8 2 true (2)
theorem kid04_part983_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part983) = true := by rfl

def kid04_part984 : Audit := .cycle 9 1 true (3)
theorem kid04_part984_checked : zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part984) = true := by rfl

def kid04_part864 : Audit := .split 9 (5,false) (byMove [(kid04_part865),(kid04_part866),(kid04_part867),(kid04_part868),(kid04_part869),(kid04_part870),(kid04_part871),(kid04_part872),(kid04_part873),(kid04_part874),(kid04_part875),(kid04_part876),(kid04_part877),(kid04_part878),(kid04_part903),(kid04_part928),(kid04_part929),(kid04_part954),(kid04_part979),(kid04_part980),(kid04_part981),(kid04_part982),(kid04_part983),(kid04_part984)])

theorem kid04_part864_checked : zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (kid04_part864) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨false,false,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part865),(kid04_part866),(kid04_part867),(kid04_part868),(kid04_part869),(kid04_part870),(kid04_part871),(kid04_part872),(kid04_part873),(kid04_part874),(kid04_part875),(kid04_part876),(kid04_part877),(kid04_part878),(kid04_part903),(kid04_part928),(kid04_part929),(kid04_part954),(kid04_part979),(kid04_part980),(kid04_part981),(kid04_part982),(kid04_part983),(kid04_part984)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part865_checked

  · exact kid04_part871_checked

  · exact kid04_part877_checked

  · exact kid04_part979_checked

  · exact kid04_part866_checked

  · exact kid04_part872_checked

  · exact kid04_part878_checked

  · exact kid04_part980_checked

  · exact kid04_part867_checked

  · exact kid04_part873_checked

  · exact kid04_part903_checked

  · exact kid04_part981_checked

  · exact kid04_part868_checked

  · exact kid04_part874_checked

  · exact kid04_part928_checked

  · exact kid04_part982_checked

  · exact kid04_part869_checked

  · exact kid04_part875_checked

  · exact kid04_part929_checked

  · exact kid04_part983_checked

  · exact kid04_part870_checked

  · exact kid04_part876_checked

  · exact kid04_part954_checked

  · exact kid04_part984_checked

def kid04 : Audit := .split 8 (4,false) (byMove [(kid04_part1),(kid04_part2),(kid04_part3),(kid04_part4),(kid04_part5),(kid04_part54),(kid04_part199),(kid04_part200),(kid04_part201),(kid04_part202),(kid04_part203),(kid04_part204),(kid04_part277),(kid04_part374),(kid04_part471),(kid04_part472),(kid04_part473),(kid04_part594),(kid04_part859),(kid04_part860),(kid04_part861),(kid04_part862),(kid04_part863),(kid04_part864)])

theorem check04 : zipCheck 2354 (childRC ⟨false,false,4⟩) (kid04) = true := by

  change (zipQueryOK 2354 (childRC ⟨false,false,4⟩) 8 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (childRC ⟨false,false,4⟩) (4,false) (some mv)) (byMove [(kid04_part1),(kid04_part2),(kid04_part3),(kid04_part4),(kid04_part5),(kid04_part54),(kid04_part199),(kid04_part200),(kid04_part201),(kid04_part202),(kid04_part203),(kid04_part204),(kid04_part277),(kid04_part374),(kid04_part471),(kid04_part472),(kid04_part473),(kid04_part594),(kid04_part859),(kid04_part860),(kid04_part861),(kid04_part862),(kid04_part863),(kid04_part864)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1_checked

  · exact kid04_part199_checked

  · exact kid04_part277_checked

  · exact kid04_part859_checked

  · exact kid04_part2_checked

  · exact kid04_part200_checked

  · exact kid04_part374_checked

  · exact kid04_part860_checked

  · exact kid04_part3_checked

  · exact kid04_part201_checked

  · exact kid04_part471_checked

  · exact kid04_part861_checked

  · exact kid04_part4_checked

  · exact kid04_part202_checked

  · exact kid04_part472_checked

  · exact kid04_part862_checked

  · exact kid04_part5_checked

  · exact kid04_part203_checked

  · exact kid04_part473_checked

  · exact kid04_part863_checked

  · exact kid04_part54_checked

  · exact kid04_part204_checked

  · exact kid04_part594_checked

  · exact kid04_part864_checked

end BB6.Agent11Raw39RC
