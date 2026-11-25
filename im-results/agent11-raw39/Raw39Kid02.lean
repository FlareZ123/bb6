import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid02_part1 : Audit := .cycle 0 9 true (0)
theorem kid02_part1_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,0⟩)) (kid02_part1) = true := by rfl

def kid02_part2 : Audit := .cycle 1 8 true (1)
theorem kid02_part2_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,1⟩)) (kid02_part2) = true := by rfl

def kid02_part3 : Audit := .cycle 17 1 false (1)
theorem kid02_part3_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,2⟩)) (kid02_part3) = true := by rfl

def kid02_part4 : Audit := .cycle 1 11 true (0)
theorem kid02_part4_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,3⟩)) (kid02_part4) = true := by rfl

def kid02_part6 : Audit := .cycle 1 10 true (0)
theorem kid02_part6_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part6) = true := by rfl

def kid02_part7 : Audit := .cycle 12 1 false (0)
theorem kid02_part7_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part7) = true := by rfl

def kid02_part8 : Audit := .cycle 13 1 false (-1)
theorem kid02_part8_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part8) = true := by rfl

def kid02_part9 : Audit := .cycle 0 11 true (0)
theorem kid02_part9_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part9) = true := by rfl

def kid02_part10 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 false (3),
.cycle 19 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 12 true (-1),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 23 (5,true),
.cycle 1 11 false (3),
.cycle 19 1 false (-1),
.cycle 1 14 true (-1),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
]),
.cycle 0 11 true (0),
.cycle 19 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 1 false (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
]),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 1 12 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 23 (5,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 1 13 true (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 9 12 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 9 4 true (0),
.cycle 11 1 true (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid02_part10_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part10) = true := by rfl

def kid02_part12 : Audit := .cycle 0 11 false (3)
theorem kid02_part12_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part12) = true := by rfl

def kid02_part13 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 false (3),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 0 21 false (3),
.cycle 11 10 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.cycle 20 1 true (-2),
.cycle 17 5 false (1),
.last 23 (4,true),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 34 1 false (-2),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 1 23 false (3),
.cycle 9 12 false (1),
.cycle 20 1 true (-2)
])
theorem kid02_part13_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part13) = true := by rfl

def kid02_part14 : Audit := .cycle 12 1 false (0)
theorem kid02_part14_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part14) = true := by rfl

def kid02_part15 : Audit := .cycle 11 1 false (-1)
theorem kid02_part15_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part15) = true := by rfl

def kid02_part16 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 13 false (3),
.cycle 11 10 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 12 1 true (-2),
.cycle 11 5 false (-1),
.last 15 (4,true),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 24 (4,true),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 1 15 false (3),
.cycle 9 4 false (1),
.cycle 12 1 true (-2)
])
theorem kid02_part16_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part16) = true := by rfl

def kid02_part17 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 12 true (-1),
.cycle 11 10 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 true (-1),
.cycle 11 1 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 10 13 false (3),
.cycle 1 11 false (3),
.cycle 11 9 false (1),
.cycle 1 14 true (-1),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
])
theorem kid02_part17_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part17) = true := by rfl

def kid02_part18 : Audit := .cycle 0 11 true (0)
theorem kid02_part18_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part18) = true := by rfl

def kid02_part19 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 false (3),
.cycle 11 10 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 21 true (0),
.cycle 11 10 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 19 2 true (0),
.cycle 20 1 true (0),
.cycle 17 5 false (3),
.last 23 (4,true),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 12 9 false (3),
.cycle 1 23 true (0),
.cycle 9 12 true (0),
.cycle 20 1 true (0)
])
theorem kid02_part19_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part19) = true := by rfl

def kid02_part20 : Audit := .cycle 12 1 false (2)
theorem kid02_part20_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part20) = true := by rfl

def kid02_part21 : Audit := .cycle 11 1 false (1)
theorem kid02_part21_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part21) = true := by rfl

def kid02_part22 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 11 10 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 11 2 true (0),
.cycle 12 1 true (0),
.cycle 11 5 false (1),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 11 9 false (2),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (0)
])
theorem kid02_part22_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part22) = true := by rfl

def kid02_part23 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 11 10 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.cycle 11 5 false (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 11 9 false (3),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid02_part23_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part23) = true := by rfl

def kid02_part24 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (3),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 0 16 false (3),
.cycle 12 10 true (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 true (-3),
.cycle 15 1 true (-3),
.cycle 11 5 false (0),
.last 18 (4,true),
.cycle 0 18 false (3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 16 false (1),
.cycle 1 15 false (3),
.cycle 12 9 false (0),
.cycle 1 18 false (3),
.cycle 9 7 false (1),
.cycle 15 1 true (-3)
])
theorem kid02_part24_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part24) = true := by rfl

def kid02_part25 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.last 23 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 14 true (-1),
.last 23 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 11 3 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 27 1 false (-1),
.cycle 1 13 false (3),
.last 22 (5,false),
.cycle 1 16 true (-1),
.cycle 9 5 false (1),
.last 14 (5,false)
])
theorem kid02_part25_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part25) = true := by rfl

def kid02_part26 : Audit := .cycle 0 13 true (-1)
theorem kid02_part26_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part26) = true := by rfl

def kid02_part27 : Audit := .cycle 11 1 false (-1)
theorem kid02_part27_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part27) = true := by rfl

def kid02_part28 : Audit := .split 12 (5,false) (byMove [
.cycle 14 17 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 18 false (3),
.last 15 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.cycle 11 5 false (-1),
.last 15 (4,true),
.cycle 0 22 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 15 true (-2),
.cycle 1 22 false (3),
.cycle 9 4 false (1),
.last 15 (4,true)
])
theorem kid02_part28_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part28) = true := by rfl

def kid02_part29 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 1 12 true (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 28 (4,true),
.cycle 1 15 false (3),
.last 13 (4,true),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid02_part29_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part29) = true := by rfl

def kid02_part30 : Audit := .cycle 0 11 true (0)
theorem kid02_part30_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part30) = true := by rfl

def kid02_part31 : Audit := .cycle 1 10 true (0)
theorem kid02_part31_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part31) = true := by rfl

def kid02_part32 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 false (3),
.cycle 11 10 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 18 2 false (0),
.cycle 19 1 false (-1),
.cycle 0 20 true (-1),
.cycle 11 10 true (-1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 18 2 true (-1),
.cycle 19 1 true (-1),
.cycle 16 5 false (2),
.last 22 (4,true),
.cycle 0 22 true (-2),
.cycle 20 1 false (-2),
.cycle 18 2 false (0),
.cycle 19 1 false (-1),
.cycle 2 29 false (3),
.cycle 1 19 false (3),
.cycle 11 9 false (2),
.cycle 1 22 true (-1),
.cycle 9 11 false (2),
.cycle 19 1 true (-1)
])
theorem kid02_part32_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part32) = true := by rfl

def kid02_part33 : Audit := .cycle 1 13 true (0)
theorem kid02_part33_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part33) = true := by rfl

def kid02_part34 : Audit := .cycle 9 2 true (0)
theorem kid02_part34_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part34) = true := by rfl

def kid02_part35 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.last 20 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid02_part35_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part35) = true := by rfl

def kid02_part11 : Audit := .split 10 (5,true) (byMove [(kid02_part12),(kid02_part13),(kid02_part14),(kid02_part15),(kid02_part16),(kid02_part17),(kid02_part18),(kid02_part19),(kid02_part20),(kid02_part21),(kid02_part22),(kid02_part23),(kid02_part24),(kid02_part25),(kid02_part26),(kid02_part27),(kid02_part28),(kid02_part29),(kid02_part30),(kid02_part31),(kid02_part32),(kid02_part33),(kid02_part34),(kid02_part35)])

theorem kid02_part11_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part11) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid02_part12),(kid02_part13),(kid02_part14),(kid02_part15),(kid02_part16),(kid02_part17),(kid02_part18),(kid02_part19),(kid02_part20),(kid02_part21),(kid02_part22),(kid02_part23),(kid02_part24),(kid02_part25),(kid02_part26),(kid02_part27),(kid02_part28),(kid02_part29),(kid02_part30),(kid02_part31),(kid02_part32),(kid02_part33),(kid02_part34),(kid02_part35)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part12_checked

  · exact kid02_part18_checked

  · exact kid02_part24_checked

  · exact kid02_part30_checked

  · exact kid02_part13_checked

  · exact kid02_part19_checked

  · exact kid02_part25_checked

  · exact kid02_part31_checked

  · exact kid02_part14_checked

  · exact kid02_part20_checked

  · exact kid02_part26_checked

  · exact kid02_part32_checked

  · exact kid02_part15_checked

  · exact kid02_part21_checked

  · exact kid02_part27_checked

  · exact kid02_part33_checked

  · exact kid02_part16_checked

  · exact kid02_part22_checked

  · exact kid02_part28_checked

  · exact kid02_part34_checked

  · exact kid02_part17_checked

  · exact kid02_part23_checked

  · exact kid02_part29_checked

  · exact kid02_part35_checked

def kid02_part36 : Audit := .cycle 0 10 true (0)
theorem kid02_part36_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part36) = true := by rfl

def kid02_part37 : Audit := .cycle 1 9 true (1)
theorem kid02_part37_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part37) = true := by rfl

def kid02_part38 : Audit := .cycle 20 1 false (2)
theorem kid02_part38_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part38) = true := by rfl

def kid02_part39 : Audit := .cycle 17 1 false (1)
theorem kid02_part39_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part39) = true := by rfl

def kid02_part40 : Audit := .cycle 9 1 true (1)
theorem kid02_part40_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part40) = true := by rfl

def kid02_part41 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 9 2 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 9 2 true (1),
.cycle 10 1 true (2),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.cycle 15 5 false (-1),
.cycle 0 15 true (0),
.cycle 21 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 5 false (2),
.cycle 15 5 false (1),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 5 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 1 17 true (0),
.cycle 9 6 true (0),
.cycle 17 5 false (1)
]),
.split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 9 5 true (1),
.cycle 10 4 true (1),
.cycle 15 8 false (1),
.cycle 16 1 false (0),
.cycle 0 32 true (-2),
.cycle 1 15 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (1),
.cycle 25 1 false (-1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 9 4 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 9 4 true (1),
.cycle 10 3 true (1),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (1),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 1 14 true (0),
.last 13 (4,true),
.cycle 15 1 false (3),
.cycle 17 1 false (-1),
.last 15 (4,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 16 1 false (0),
.last 14 (4,true),
.cycle 1 14 true (0),
.last 13 (4,true),
.cycle 13 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2)
])
theorem kid02_part41_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part41) = true := by rfl

def kid02_part42 : Audit := .cycle 11 4 false (1)
theorem kid02_part42_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part42) = true := by rfl

def kid02_part43 : Audit := .cycle 12 1 false (0)
theorem kid02_part43_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part43) = true := by rfl

def kid02_part44 : Audit := .cycle 0 20 true (-2)
theorem kid02_part44_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part44) = true := by rfl

def kid02_part45 : Audit := .cycle 1 11 true (0)
theorem kid02_part45_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part45) = true := by rfl

def kid02_part46 : Audit := .split 10 (4,true) (byMove [
.cycle 1 15 false (3),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 13 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 28 (5,true),
.last 15 (5,true),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 1 11 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 12 1 false (2),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 1 false (2),
.last 12 (5,false),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
]),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 1 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 28 (5,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 1 13 true (-1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 1 11 true (0),
.cycle 13 1 false (-1),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 9 3 true (0),
.split 11 (5,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 32 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 17 (5,false),
.last 12 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
])
theorem kid02_part46_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part46) = true := by rfl

def kid02_part48 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 false (3),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 0 16 true (-1),
.last 17 (5,false),
.cycle 0 16 false (3),
.cycle 0 15 true (-1),
.last 24 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 1 16 true (-1),
.last 17 (5,false),
.cycle 10 5 false (1),
.cycle 12 15 true (0),
.cycle 12 14 true (-1),
.cycle 2 13 false (3),
.cycle 1 17 true (-1),
.cycle 12 6 true (-1),
.last 15 (5,false)
])
theorem kid02_part48_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part48) = true := by rfl

def kid02_part49 : Audit := .cycle 0 14 true (-1)
theorem kid02_part49_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part49) = true := by rfl

def kid02_part50 : Audit := .cycle 12 1 false (0)
theorem kid02_part50_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part50) = true := by rfl

def kid02_part51 : Audit := .cycle 11 1 false (-1)
theorem kid02_part51_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part51) = true := by rfl

def kid02_part52 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.cycle 0 20 true (-2),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 11 4 false (-1),
.last 14 (4,true),
.cycle 7 8 false (3),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid02_part52_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part52) = true := by rfl

def kid02_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.last 28 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 1 17 false (3),
.last 14 (4,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 14 1 true (0),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 1 21 false (3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 9 3 false (1),
.cycle 16 1 true (-2)
])
theorem kid02_part53_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part53) = true := by rfl

def kid02_part54 : Audit := .cycle 1 11 true (0)
theorem kid02_part54_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part54) = true := by rfl

def kid02_part55 : Audit := .cycle 13 1 false (1)
theorem kid02_part55_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part55) = true := by rfl

def kid02_part56 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 1 14 true (-1),
.cycle 16 1 false (0),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 16 1 false (2),
.cycle 11 5 false (1),
.last 16 (4,true),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 8 17 false (3),
.cycle 11 4 false (1),
.last 15 (4,true),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 11 11 false (2)
])
theorem kid02_part56_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part56) = true := by rfl

def kid02_part57 : Audit := .cycle 0 12 true (0)
theorem kid02_part57_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part57) = true := by rfl

def kid02_part58 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.last 21 (5,false),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.last 21 (5,false),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.cycle 11 3 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.last 20 (5,false),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid02_part58_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part58) = true := by rfl

def kid02_part59 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 0 13 true (0),
.cycle 25 1 false (3),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.last 15 (4,true),
.cycle 12 1 true (2),
.cycle 12 5 false (2),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (4,true),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (2)
])
theorem kid02_part59_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part59) = true := by rfl

def kid02_part60 : Audit := .split 15 (5,false) (byMove [
.last 19 (4,true),
.last 22 (4,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 48 (4,true),
.cycle 18 1 false (-2),
.cycle 13 3 false (-1),
.last 20 (4,true),
.last 16 (4,true),
.cycle 10 6 false (0),
.cycle 11 5 false (0),
.last 18 (4,true),
.last 52 (4,true),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 39 (4,true),
.cycle 12 4 false (0),
.last 17 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.cycle 12 6 false (0)
])
theorem kid02_part60_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part60) = true := by rfl

def kid02_part61 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.last 23 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.last 26 (5,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 11 3 false (0),
.last 20 (5,false),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 31 1 false (-1),
.cycle 29 1 false (-1),
.cycle 0 16 true (-1),
.last 20 (5,false),
.cycle 9 5 false (1),
.last 14 (5,false)
])
theorem kid02_part61_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part61) = true := by rfl

def kid02_part62 : Audit := .cycle 1 13 true (-1)
theorem kid02_part62_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part62) = true := by rfl

def kid02_part63 : Audit := .cycle 11 1 false (-1)
theorem kid02_part63_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part63) = true := by rfl

def kid02_part64 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 40 (4,true),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.cycle 0 20 true (-2),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 40 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 11 4 false (-1),
.last 14 (4,true),
.cycle 5 8 false (3),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid02_part64_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part64) = true := by rfl

def kid02_part65 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 1 17 false (3),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.cycle 1 13 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 1 21 false (3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 11 4 false (0),
.last 13 (4,true),
.cycle 1 13 true (-1),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid02_part65_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part65) = true := by rfl

def kid02_part66 : Audit := .cycle 1 11 true (0)
theorem kid02_part66_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part66) = true := by rfl

def kid02_part67 : Audit := .split 14 (5,false) (byMove [
.last 18 (4,true),
.cycle 35 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 1 15 false (3),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 16 true (-2),
.last 15 (4,true),
.cycle 1 15 false (3),
.cycle 11 5 false (1),
.last 17 (4,true),
.cycle 1 17 false (3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 28 (4,true),
.cycle 11 4 false (1),
.last 16 (4,true),
.cycle 7 20 false (3),
.last 15 (4,true),
.last 28 (4,true)
])
theorem kid02_part67_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part67) = true := by rfl

def kid02_part68 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.last 22 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 21 (5,false),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid02_part68_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part68) = true := by rfl

def kid02_part69 : Audit := .cycle 0 12 true (0)
theorem kid02_part69_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part69) = true := by rfl

def kid02_part70 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 9 4 true (0),
.cycle 0 12 true (0),
.last 21 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 1 13 true (0),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid02_part70_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part70) = true := by rfl

def kid02_part71 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (0),
.cycle 39 1 false (-3),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 2 22 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 15 (4,true),
.cycle 12 1 true (2),
.last 16 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 1 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (2)
])
theorem kid02_part71_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part71) = true := by rfl

def kid02_part47 : Audit := .split 10 (5,true) (byMove [(kid02_part48),(kid02_part49),(kid02_part50),(kid02_part51),(kid02_part52),(kid02_part53),(kid02_part54),(kid02_part55),(kid02_part56),(kid02_part57),(kid02_part58),(kid02_part59),(kid02_part60),(kid02_part61),(kid02_part62),(kid02_part63),(kid02_part64),(kid02_part65),(kid02_part66),(kid02_part67),(kid02_part68),(kid02_part69),(kid02_part70),(kid02_part71)])

theorem kid02_part47_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part47) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid02_part48),(kid02_part49),(kid02_part50),(kid02_part51),(kid02_part52),(kid02_part53),(kid02_part54),(kid02_part55),(kid02_part56),(kid02_part57),(kid02_part58),(kid02_part59),(kid02_part60),(kid02_part61),(kid02_part62),(kid02_part63),(kid02_part64),(kid02_part65),(kid02_part66),(kid02_part67),(kid02_part68),(kid02_part69),(kid02_part70),(kid02_part71)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part48_checked

  · exact kid02_part54_checked

  · exact kid02_part60_checked

  · exact kid02_part66_checked

  · exact kid02_part49_checked

  · exact kid02_part55_checked

  · exact kid02_part61_checked

  · exact kid02_part67_checked

  · exact kid02_part50_checked

  · exact kid02_part56_checked

  · exact kid02_part62_checked

  · exact kid02_part68_checked

  · exact kid02_part51_checked

  · exact kid02_part57_checked

  · exact kid02_part63_checked

  · exact kid02_part69_checked

  · exact kid02_part52_checked

  · exact kid02_part58_checked

  · exact kid02_part64_checked

  · exact kid02_part70_checked

  · exact kid02_part53_checked

  · exact kid02_part59_checked

  · exact kid02_part65_checked

  · exact kid02_part71_checked

def kid02_part72 : Audit := .cycle 0 10 true (0)
theorem kid02_part72_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part72) = true := by rfl

def kid02_part73 : Audit := .cycle 1 9 true (1)
theorem kid02_part73_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part73) = true := by rfl

def kid02_part74 : Audit := .cycle 2 8 true (1)
theorem kid02_part74_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part74) = true := by rfl

def kid02_part75 : Audit := .cycle 1 12 true (1)
theorem kid02_part75_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part75) = true := by rfl

def kid02_part76 : Audit := .cycle 9 1 true (1)
theorem kid02_part76_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part76) = true := by rfl

def kid02_part78 : Audit := .cycle 1 11 true (1)
theorem kid02_part78_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part78) = true := by rfl

def kid02_part79 : Audit := .cycle 17 1 false (-1)
theorem kid02_part79_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part79) = true := by rfl

def kid02_part80 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 3 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 3 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 13 3 false (1)
])
theorem kid02_part80_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part80) = true := by rfl

def kid02_part81 : Audit := .cycle 0 12 true (0)
theorem kid02_part81_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part81) = true := by rfl

def kid02_part82 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid02_part82_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part82) = true := by rfl

def kid02_part83 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 15 1 false (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid02_part83_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part83) = true := by rfl

def kid02_part84 : Audit := .cycle 0 11 true (0)
theorem kid02_part84_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part84) = true := by rfl

def kid02_part85 : Audit := .cycle 1 10 true (1)
theorem kid02_part85_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part85) = true := by rfl

def kid02_part86 : Audit := .cycle 0 23 true (0)
theorem kid02_part86_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part86) = true := by rfl

def kid02_part87 : Audit := .cycle 3 8 true (1)
theorem kid02_part87_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part87) = true := by rfl

def kid02_part88 : Audit := .cycle 9 2 true (1)
theorem kid02_part88_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part88) = true := by rfl

def kid02_part89 : Audit := .cycle 10 1 true (2)
theorem kid02_part89_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part89) = true := by rfl

def kid02_part90 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.cycle 17 5 false (-1),
.cycle 0 15 true (0),
.cycle 20 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 5 false (2),
.cycle 17 5 false (1),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 17 5 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 1 17 true (0),
.cycle 9 6 true (0),
.cycle 15 5 false (1)
])
theorem kid02_part90_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part90) = true := by rfl

def kid02_part91 : Audit := .cycle 17 1 false (-1)
theorem kid02_part91_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part91) = true := by rfl

def kid02_part92 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 20 (5,true),
.cycle 15 3 false (1),
.cycle 23 3 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 14 (5,true),
.cycle 1 16 true (0),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 14 (5,true),
.last 20 (5,true),
.cycle 0 17 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.last 14 (5,true),
.cycle 13 3 false (1)
])
theorem kid02_part92_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part92) = true := by rfl

def kid02_part93 : Audit := .cycle 1 12 true (1)
theorem kid02_part93_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part93) = true := by rfl

def kid02_part94 : Audit := .split 11 (4,true) (byMove [
.cycle 1 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 1 44 true (-2),
.cycle 19 1 false (-1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 1 14 true (0),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.last 12 (5,true)
])
theorem kid02_part94_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part94) = true := by rfl

def kid02_part95 : Audit := .split 11 (5,true) (byMove [
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 20 1 false (4),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 29 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (1)
])
theorem kid02_part95_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part95) = true := by rfl

def kid02_part96 : Audit := .cycle 0 11 true (0)
theorem kid02_part96_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part96) = true := by rfl

def kid02_part97 : Audit := .cycle 1 10 true (1)
theorem kid02_part97_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part97) = true := by rfl

def kid02_part98 : Audit := .cycle 2 9 true (1)
theorem kid02_part98_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part98) = true := by rfl

def kid02_part99 : Audit := .cycle 1 13 true (1)
theorem kid02_part99_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part99) = true := by rfl

def kid02_part100 : Audit := .cycle 9 2 true (1)
theorem kid02_part100_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part100) = true := by rfl

def kid02_part101 : Audit := .cycle 10 1 true (2)
theorem kid02_part101_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part101) = true := by rfl

def kid02_part77 : Audit := .split 10 (5,false) (byMove [(kid02_part78),(kid02_part79),(kid02_part80),(kid02_part81),(kid02_part82),(kid02_part83),(kid02_part84),(kid02_part85),(kid02_part86),(kid02_part87),(kid02_part88),(kid02_part89),(kid02_part90),(kid02_part91),(kid02_part92),(kid02_part93),(kid02_part94),(kid02_part95),(kid02_part96),(kid02_part97),(kid02_part98),(kid02_part99),(kid02_part100),(kid02_part101)])

theorem kid02_part77_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part77) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid02_part78),(kid02_part79),(kid02_part80),(kid02_part81),(kid02_part82),(kid02_part83),(kid02_part84),(kid02_part85),(kid02_part86),(kid02_part87),(kid02_part88),(kid02_part89),(kid02_part90),(kid02_part91),(kid02_part92),(kid02_part93),(kid02_part94),(kid02_part95),(kid02_part96),(kid02_part97),(kid02_part98),(kid02_part99),(kid02_part100),(kid02_part101)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part78_checked

  · exact kid02_part84_checked

  · exact kid02_part90_checked

  · exact kid02_part96_checked

  · exact kid02_part79_checked

  · exact kid02_part85_checked

  · exact kid02_part91_checked

  · exact kid02_part97_checked

  · exact kid02_part80_checked

  · exact kid02_part86_checked

  · exact kid02_part92_checked

  · exact kid02_part98_checked

  · exact kid02_part81_checked

  · exact kid02_part87_checked

  · exact kid02_part93_checked

  · exact kid02_part99_checked

  · exact kid02_part82_checked

  · exact kid02_part88_checked

  · exact kid02_part94_checked

  · exact kid02_part100_checked

  · exact kid02_part83_checked

  · exact kid02_part89_checked

  · exact kid02_part95_checked

  · exact kid02_part101_checked

def kid02_part5 : Audit := .split 9 (4,false) (byMove [(kid02_part6),(kid02_part7),(kid02_part8),(kid02_part9),(kid02_part10),(kid02_part11),(kid02_part36),(kid02_part37),(kid02_part38),(kid02_part39),(kid02_part40),(kid02_part41),(kid02_part42),(kid02_part43),(kid02_part44),(kid02_part45),(kid02_part46),(kid02_part47),(kid02_part72),(kid02_part73),(kid02_part74),(kid02_part75),(kid02_part76),(kid02_part77)])

theorem kid02_part5_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (kid02_part5) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid02_part6),(kid02_part7),(kid02_part8),(kid02_part9),(kid02_part10),(kid02_part11),(kid02_part36),(kid02_part37),(kid02_part38),(kid02_part39),(kid02_part40),(kid02_part41),(kid02_part42),(kid02_part43),(kid02_part44),(kid02_part45),(kid02_part46),(kid02_part47),(kid02_part72),(kid02_part73),(kid02_part74),(kid02_part75),(kid02_part76),(kid02_part77)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part6_checked

  · exact kid02_part36_checked

  · exact kid02_part42_checked

  · exact kid02_part72_checked

  · exact kid02_part7_checked

  · exact kid02_part37_checked

  · exact kid02_part43_checked

  · exact kid02_part73_checked

  · exact kid02_part8_checked

  · exact kid02_part38_checked

  · exact kid02_part44_checked

  · exact kid02_part74_checked

  · exact kid02_part9_checked

  · exact kid02_part39_checked

  · exact kid02_part45_checked

  · exact kid02_part75_checked

  · exact kid02_part10_checked

  · exact kid02_part40_checked

  · exact kid02_part46_checked

  · exact kid02_part76_checked

  · exact kid02_part11_checked

  · exact kid02_part41_checked

  · exact kid02_part47_checked

  · exact kid02_part77_checked

def kid02_part103 : Audit := .cycle 1 10 true (0)
theorem kid02_part103_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part103) = true := by rfl

def kid02_part104 : Audit := .cycle 12 1 false (0)
theorem kid02_part104_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part104) = true := by rfl

def kid02_part105 : Audit := .cycle 13 1 false (-1)
theorem kid02_part105_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part105) = true := by rfl

def kid02_part106 : Audit := .cycle 0 11 true (0)
theorem kid02_part106_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part106) = true := by rfl

def kid02_part108 : Audit := .cycle 0 11 false (3)
theorem kid02_part108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part108) = true := by rfl

def kid02_part109 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 false (3),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 0 21 false (3),
.cycle 11 10 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 true (-2),
.cycle 19 2 true (-2),
.cycle 17 5 false (1),
.last 23 (5,true),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 34 1 false (-2),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 1 23 false (3),
.cycle 20 1 true (-2),
.cycle 9 12 false (1)
])
theorem kid02_part109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part109) = true := by rfl

def kid02_part110 : Audit := .cycle 12 1 false (0)
theorem kid02_part110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part110) = true := by rfl

def kid02_part111 : Audit := .cycle 11 1 false (-1)
theorem kid02_part111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part111) = true := by rfl

def kid02_part112 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 12 true (-1),
.cycle 11 10 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 11 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 10 13 false (3),
.cycle 1 11 false (3),
.cycle 11 9 false (1),
.cycle 1 14 true (-1),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
])
theorem kid02_part112_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part112) = true := by rfl

def kid02_part113 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 13 false (3),
.cycle 11 10 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 true (-2),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 24 (5,true),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 1 15 false (3),
.cycle 12 1 true (-2),
.cycle 9 4 false (1)
])
theorem kid02_part113_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part113) = true := by rfl

def kid02_part114 : Audit := .cycle 0 11 true (0)
theorem kid02_part114_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part114) = true := by rfl

def kid02_part115 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 false (3),
.cycle 11 10 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 0 21 true (0),
.cycle 11 10 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 true (0),
.cycle 19 2 true (0),
.cycle 17 5 false (3),
.last 23 (5,true),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 12 9 false (3),
.cycle 1 23 true (0),
.cycle 20 1 true (0),
.cycle 9 12 true (0)
])
theorem kid02_part115_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part115) = true := by rfl

def kid02_part116 : Audit := .cycle 12 1 false (2)
theorem kid02_part116_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part116) = true := by rfl

def kid02_part117 : Audit := .cycle 11 1 false (1)
theorem kid02_part117_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part117) = true := by rfl

def kid02_part118 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 11 10 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 11 5 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 11 9 false (3),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid02_part118_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part118) = true := by rfl

def kid02_part119 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 0 13 true (0),
.cycle 11 10 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 true (0),
.cycle 11 2 true (0),
.cycle 11 5 false (1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 11 9 false (2),
.cycle 1 15 true (0),
.cycle 12 1 true (0),
.cycle 9 4 true (0)
])
theorem kid02_part119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part119) = true := by rfl

def kid02_part120 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 false (3),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 0 16 false (3),
.cycle 12 10 true (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 true (-3),
.cycle 14 2 true (-3),
.cycle 11 5 false (0),
.last 18 (5,true),
.cycle 0 18 false (3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 16 false (1),
.cycle 1 15 false (3),
.cycle 12 9 false (0),
.cycle 1 18 false (3),
.cycle 15 1 true (-3),
.cycle 9 7 false (1)
])
theorem kid02_part120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part120) = true := by rfl

def kid02_part121 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 false (3),
.last 23 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 14 true (-1),
.last 23 (4,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 27 1 false (-1),
.cycle 1 13 false (3),
.last 22 (4,false),
.cycle 1 16 true (-1),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid02_part121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part121) = true := by rfl

def kid02_part122 : Audit := .cycle 0 13 true (-1)
theorem kid02_part122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part122) = true := by rfl

def kid02_part123 : Audit := .cycle 11 1 false (-1)
theorem kid02_part123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part123) = true := by rfl

def kid02_part124 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 1 12 true (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 28 (5,true),
.cycle 1 15 false (3),
.last 13 (5,true),
.cycle 0 13 true (-1),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid02_part124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part124) = true := by rfl

def kid02_part125 : Audit := .split 12 (4,false) (byMove [
.cycle 14 17 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 18 false (3),
.last 15 (5,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.cycle 0 22 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (-2),
.cycle 1 22 false (3),
.last 15 (5,true),
.cycle 9 4 false (1)
])
theorem kid02_part125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part125) = true := by rfl

def kid02_part126 : Audit := .cycle 0 11 true (0)
theorem kid02_part126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part126) = true := by rfl

def kid02_part127 : Audit := .cycle 1 10 true (0)
theorem kid02_part127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part127) = true := by rfl

def kid02_part128 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 false (3),
.cycle 11 10 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 18 2 false (0),
.cycle 0 20 true (-1),
.cycle 11 10 true (-1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 19 1 true (-1),
.cycle 18 2 true (-1),
.cycle 16 5 false (2),
.last 22 (5,true),
.cycle 0 22 true (-2),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 18 2 false (0),
.cycle 2 29 false (3),
.cycle 1 19 false (3),
.cycle 11 9 false (2),
.cycle 1 22 true (-1),
.cycle 19 1 true (-1),
.cycle 9 11 false (2)
])
theorem kid02_part128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part128) = true := by rfl

def kid02_part129 : Audit := .cycle 1 13 true (0)
theorem kid02_part129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part129) = true := by rfl

def kid02_part130 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.last 20 (5,true),
.cycle 1 13 true (0),
.cycle 10 3 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid02_part130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part130) = true := by rfl

def kid02_part131 : Audit := .cycle 9 2 true (0)
theorem kid02_part131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part131) = true := by rfl

def kid02_part107 : Audit := .split 10 (4,true) (byMove [(kid02_part108),(kid02_part109),(kid02_part110),(kid02_part111),(kid02_part112),(kid02_part113),(kid02_part114),(kid02_part115),(kid02_part116),(kid02_part117),(kid02_part118),(kid02_part119),(kid02_part120),(kid02_part121),(kid02_part122),(kid02_part123),(kid02_part124),(kid02_part125),(kid02_part126),(kid02_part127),(kid02_part128),(kid02_part129),(kid02_part130),(kid02_part131)])

theorem kid02_part107_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part107) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid02_part108),(kid02_part109),(kid02_part110),(kid02_part111),(kid02_part112),(kid02_part113),(kid02_part114),(kid02_part115),(kid02_part116),(kid02_part117),(kid02_part118),(kid02_part119),(kid02_part120),(kid02_part121),(kid02_part122),(kid02_part123),(kid02_part124),(kid02_part125),(kid02_part126),(kid02_part127),(kid02_part128),(kid02_part129),(kid02_part130),(kid02_part131)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part108_checked

  · exact kid02_part114_checked

  · exact kid02_part120_checked

  · exact kid02_part126_checked

  · exact kid02_part109_checked

  · exact kid02_part115_checked

  · exact kid02_part121_checked

  · exact kid02_part127_checked

  · exact kid02_part110_checked

  · exact kid02_part116_checked

  · exact kid02_part122_checked

  · exact kid02_part128_checked

  · exact kid02_part111_checked

  · exact kid02_part117_checked

  · exact kid02_part123_checked

  · exact kid02_part129_checked

  · exact kid02_part112_checked

  · exact kid02_part118_checked

  · exact kid02_part124_checked

  · exact kid02_part130_checked

  · exact kid02_part113_checked

  · exact kid02_part119_checked

  · exact kid02_part125_checked

  · exact kid02_part131_checked

def kid02_part132 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 false (3),
.cycle 19 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 12 true (-1),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 12 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 23 (4,true),
.cycle 1 11 false (3),
.cycle 19 1 false (-1),
.cycle 1 14 true (-1),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 19 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 12 1 false (2),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 11 1 false (1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 1 12 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 23 (4,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 9 12 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 11 1 true (1),
.cycle 9 4 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid02_part132_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part132) = true := by rfl

def kid02_part133 : Audit := .cycle 0 10 true (0)
theorem kid02_part133_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part133) = true := by rfl

def kid02_part134 : Audit := .cycle 1 9 true (1)
theorem kid02_part134_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part134) = true := by rfl

def kid02_part135 : Audit := .cycle 20 1 false (2)
theorem kid02_part135_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part135) = true := by rfl

def kid02_part136 : Audit := .cycle 17 1 false (1)
theorem kid02_part136_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part136) = true := by rfl

def kid02_part137 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (2),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (0),
.cycle 0 15 true (0),
.cycle 21 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 5 false (1),
.cycle 15 5 false (2),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 9 6 true (0)
]),
.split 13 (5,true) (byMove [
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 14 5 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 10 4 true (1),
.cycle 9 5 true (1),
.cycle 15 8 false (1),
.cycle 16 1 false (0),
.cycle 0 32 true (-2),
.cycle 1 15 true (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (-1),
.cycle 9 5 true (1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 1 14 true (0),
.cycle 15 1 false (3),
.last 13 (5,true),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.last 16 (5,true),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 1 14 true (0),
.cycle 13 3 true (1),
.last 13 (5,true)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 14 (5,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 10 3 true (1),
.cycle 9 4 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 9 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid02_part137_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part137) = true := by rfl

def kid02_part138 : Audit := .cycle 9 1 true (1)
theorem kid02_part138_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part138) = true := by rfl

def kid02_part139 : Audit := .cycle 11 4 false (1)
theorem kid02_part139_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part139) = true := by rfl

def kid02_part140 : Audit := .cycle 12 1 false (0)
theorem kid02_part140_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part140) = true := by rfl

def kid02_part141 : Audit := .cycle 0 20 true (-2)
theorem kid02_part141_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part141) = true := by rfl

def kid02_part142 : Audit := .cycle 1 11 true (0)
theorem kid02_part142_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part142) = true := by rfl

def kid02_part144 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 16 true (-1),
.cycle 0 16 false (3),
.last 17 (4,false),
.cycle 0 15 true (-1),
.last 24 (4,false),
.last 24 (4,false),
.last 22 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 1 16 true (-1),
.cycle 10 5 false (1),
.last 17 (4,false),
.cycle 12 15 true (0),
.cycle 12 14 true (-1),
.cycle 2 13 false (3),
.cycle 1 17 true (-1),
.last 15 (4,false),
.cycle 12 6 true (-1)
])
theorem kid02_part144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part144) = true := by rfl

def kid02_part145 : Audit := .cycle 0 14 true (-1)
theorem kid02_part145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part145) = true := by rfl

def kid02_part146 : Audit := .cycle 12 1 false (0)
theorem kid02_part146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part146) = true := by rfl

def kid02_part147 : Audit := .cycle 11 1 false (-1)
theorem kid02_part147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part147) = true := by rfl

def kid02_part148 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.last 28 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 1 17 false (3),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 14 1 true (0),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 1 21 false (3),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 16 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid02_part148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part148) = true := by rfl

def kid02_part149 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.cycle 0 20 true (-2),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 11 4 false (-1),
.last 14 (5,true),
.cycle 7 8 false (3),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid02_part149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part149) = true := by rfl

def kid02_part150 : Audit := .cycle 1 11 true (0)
theorem kid02_part150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part150) = true := by rfl

def kid02_part151 : Audit := .cycle 13 1 false (1)
theorem kid02_part151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part151) = true := by rfl

def kid02_part152 : Audit := .split 13 (4,false) (byMove [
.last 17 (5,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 1 14 true (-1),
.cycle 16 1 false (0),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 16 1 false (2),
.last 14 (5,true),
.cycle 11 5 false (1),
.last 16 (5,true),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 8 17 false (3),
.cycle 11 4 false (1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 11 11 false (2),
.last 14 (5,true)
])
theorem kid02_part152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part152) = true := by rfl

def kid02_part153 : Audit := .cycle 0 12 true (0)
theorem kid02_part153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part153) = true := by rfl

def kid02_part154 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.cycle 25 1 false (3),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 12 1 true (2),
.last 15 (5,true),
.cycle 12 5 false (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (5,true),
.cycle 1 15 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid02_part154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part154) = true := by rfl

def kid02_part155 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.last 21 (4,false),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.last 21 (4,false),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 11 3 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.last 20 (4,false),
.cycle 1 14 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid02_part155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part155) = true := by rfl

def kid02_part156 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.last 22 (5,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 48 (5,true),
.cycle 18 1 false (-2),
.cycle 13 3 false (-1),
.last 20 (5,true),
.cycle 10 6 false (0),
.last 16 (5,true),
.cycle 11 5 false (0),
.last 18 (5,true),
.last 52 (5,true),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 39 (5,true),
.cycle 12 4 false (0),
.last 17 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.last 16 (5,true)
])
theorem kid02_part156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part156) = true := by rfl

def kid02_part157 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (-2),
.last 23 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.last 26 (4,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.last 20 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 31 1 false (-1),
.cycle 29 1 false (-1),
.cycle 0 16 true (-1),
.last 20 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid02_part157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part157) = true := by rfl

def kid02_part158 : Audit := .cycle 1 13 true (-1)
theorem kid02_part158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part158) = true := by rfl

def kid02_part159 : Audit := .cycle 11 1 false (-1)
theorem kid02_part159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part159) = true := by rfl

def kid02_part160 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 1 17 false (3),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.cycle 1 13 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 1 21 false (3),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 11 4 false (0),
.last 13 (5,true),
.cycle 1 13 true (-1),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid02_part160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part160) = true := by rfl

def kid02_part161 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 40 (5,true),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.cycle 0 20 true (-2),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 40 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 11 4 false (-1),
.last 14 (5,true),
.cycle 5 8 false (3),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid02_part161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part161) = true := by rfl

def kid02_part162 : Audit := .cycle 1 11 true (0)
theorem kid02_part162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part162) = true := by rfl

def kid02_part163 : Audit := .split 14 (4,false) (byMove [
.last 18 (5,true),
.cycle 35 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 1 15 false (3),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 16 true (-2),
.cycle 1 15 false (3),
.last 15 (5,true),
.cycle 11 5 false (1),
.last 17 (5,true),
.cycle 1 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 28 (5,true),
.cycle 11 4 false (1),
.last 16 (5,true),
.cycle 7 20 false (3),
.last 28 (5,true),
.last 15 (5,true)
])
theorem kid02_part163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part163) = true := by rfl

def kid02_part164 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.last 22 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 21 (4,false),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid02_part164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part164) = true := by rfl

def kid02_part165 : Audit := .cycle 0 12 true (0)
theorem kid02_part165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part165) = true := by rfl

def kid02_part166 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (0),
.cycle 39 1 false (-3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 2 22 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 12 1 true (2),
.last 15 (5,true),
.last 16 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.cycle 1 14 true (0),
.cycle 10 3 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid02_part166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part166) = true := by rfl

def kid02_part167 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 9 4 true (0),
.last 14 (4,false),
.cycle 0 12 true (0),
.last 21 (4,false),
.last 21 (4,false),
.last 19 (4,false),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 1 13 true (0),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid02_part167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part167) = true := by rfl

def kid02_part143 : Audit := .split 10 (4,true) (byMove [(kid02_part144),(kid02_part145),(kid02_part146),(kid02_part147),(kid02_part148),(kid02_part149),(kid02_part150),(kid02_part151),(kid02_part152),(kid02_part153),(kid02_part154),(kid02_part155),(kid02_part156),(kid02_part157),(kid02_part158),(kid02_part159),(kid02_part160),(kid02_part161),(kid02_part162),(kid02_part163),(kid02_part164),(kid02_part165),(kid02_part166),(kid02_part167)])

theorem kid02_part143_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part143) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid02_part144),(kid02_part145),(kid02_part146),(kid02_part147),(kid02_part148),(kid02_part149),(kid02_part150),(kid02_part151),(kid02_part152),(kid02_part153),(kid02_part154),(kid02_part155),(kid02_part156),(kid02_part157),(kid02_part158),(kid02_part159),(kid02_part160),(kid02_part161),(kid02_part162),(kid02_part163),(kid02_part164),(kid02_part165),(kid02_part166),(kid02_part167)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part144_checked

  · exact kid02_part150_checked

  · exact kid02_part156_checked

  · exact kid02_part162_checked

  · exact kid02_part145_checked

  · exact kid02_part151_checked

  · exact kid02_part157_checked

  · exact kid02_part163_checked

  · exact kid02_part146_checked

  · exact kid02_part152_checked

  · exact kid02_part158_checked

  · exact kid02_part164_checked

  · exact kid02_part147_checked

  · exact kid02_part153_checked

  · exact kid02_part159_checked

  · exact kid02_part165_checked

  · exact kid02_part148_checked

  · exact kid02_part154_checked

  · exact kid02_part160_checked

  · exact kid02_part166_checked

  · exact kid02_part149_checked

  · exact kid02_part155_checked

  · exact kid02_part161_checked

  · exact kid02_part167_checked

def kid02_part168 : Audit := .split 10 (5,true) (byMove [
.cycle 1 15 false (3),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 28 (4,true),
.last 15 (4,true),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 1 11 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 12 (4,false),
.cycle 12 1 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 1 14 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
]),
.cycle 12 1 false (2),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 1 13 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 28 (4,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 1 13 true (-1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 1 11 true (0),
.cycle 13 1 false (-1),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 32 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 12 (4,false),
.last 17 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.last 13 (4,false),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
]),
.cycle 9 3 true (0)
])
theorem kid02_part168_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part168) = true := by rfl

def kid02_part169 : Audit := .cycle 0 10 true (0)
theorem kid02_part169_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part169) = true := by rfl

def kid02_part170 : Audit := .cycle 1 9 true (1)
theorem kid02_part170_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part170) = true := by rfl

def kid02_part171 : Audit := .cycle 2 8 true (1)
theorem kid02_part171_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part171) = true := by rfl

def kid02_part172 : Audit := .cycle 1 12 true (1)
theorem kid02_part172_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part172) = true := by rfl

def kid02_part174 : Audit := .cycle 1 11 true (1)
theorem kid02_part174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part174) = true := by rfl

def kid02_part175 : Audit := .cycle 17 1 false (-1)
theorem kid02_part175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part175) = true := by rfl

def kid02_part176 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 13 true (0),
.cycle 20 3 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 3 false (2),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 1 15 true (0),
.cycle 13 3 false (1),
.cycle 9 4 true (0)
])
theorem kid02_part176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part176) = true := by rfl

def kid02_part177 : Audit := .cycle 0 12 true (0)
theorem kid02_part177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part177) = true := by rfl

def kid02_part178 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 9 3 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
])
theorem kid02_part178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part178) = true := by rfl

def kid02_part179 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 4 true (1),
.cycle 9 3 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
])
theorem kid02_part179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part179) = true := by rfl

def kid02_part180 : Audit := .cycle 0 11 true (0)
theorem kid02_part180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part180) = true := by rfl

def kid02_part181 : Audit := .cycle 1 10 true (1)
theorem kid02_part181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part181) = true := by rfl

def kid02_part182 : Audit := .cycle 0 23 true (0)
theorem kid02_part182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part182) = true := by rfl

def kid02_part183 : Audit := .cycle 3 8 true (1)
theorem kid02_part183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part183) = true := by rfl

def kid02_part184 : Audit := .cycle 10 1 true (2)
theorem kid02_part184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part184) = true := by rfl

def kid02_part185 : Audit := .cycle 9 2 true (1)
theorem kid02_part185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part185) = true := by rfl

def kid02_part186 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 5 false (-1),
.cycle 15 5 false (0),
.cycle 0 15 true (0),
.cycle 20 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 17 5 false (1),
.cycle 15 5 false (2),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 17 5 false (-1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 1 17 true (0),
.cycle 15 5 false (1),
.cycle 9 6 true (0)
])
theorem kid02_part186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part186) = true := by rfl

def kid02_part187 : Audit := .cycle 17 1 false (-1)
theorem kid02_part187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part187) = true := by rfl

def kid02_part188 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.cycle 13 3 false (0),
.cycle 15 3 false (1),
.cycle 23 3 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 1 16 true (0),
.last 14 (4,true),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.cycle 13 3 false (1),
.last 14 (4,true)
])
theorem kid02_part188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part188) = true := by rfl

def kid02_part189 : Audit := .cycle 1 12 true (1)
theorem kid02_part189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part189) = true := by rfl

def kid02_part190 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 29 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 10 3 true (1),
.last 12 (5,true)
])
theorem kid02_part190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part190) = true := by rfl

def kid02_part191 : Audit := .split 11 (5,true) (byMove [
.cycle 1 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 1 44 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 1 14 true (0),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (1)
])
theorem kid02_part191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part191) = true := by rfl

def kid02_part192 : Audit := .cycle 0 11 true (0)
theorem kid02_part192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part192) = true := by rfl

def kid02_part193 : Audit := .cycle 1 10 true (1)
theorem kid02_part193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part193) = true := by rfl

def kid02_part194 : Audit := .cycle 2 9 true (1)
theorem kid02_part194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part194) = true := by rfl

def kid02_part195 : Audit := .cycle 1 13 true (1)
theorem kid02_part195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part195) = true := by rfl

def kid02_part196 : Audit := .cycle 10 1 true (2)
theorem kid02_part196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part196) = true := by rfl

def kid02_part197 : Audit := .cycle 9 2 true (1)
theorem kid02_part197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part197) = true := by rfl

def kid02_part173 : Audit := .split 10 (4,false) (byMove [(kid02_part174),(kid02_part175),(kid02_part176),(kid02_part177),(kid02_part178),(kid02_part179),(kid02_part180),(kid02_part181),(kid02_part182),(kid02_part183),(kid02_part184),(kid02_part185),(kid02_part186),(kid02_part187),(kid02_part188),(kid02_part189),(kid02_part190),(kid02_part191),(kid02_part192),(kid02_part193),(kid02_part194),(kid02_part195),(kid02_part196),(kid02_part197)])

theorem kid02_part173_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part173) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid02_part174),(kid02_part175),(kid02_part176),(kid02_part177),(kid02_part178),(kid02_part179),(kid02_part180),(kid02_part181),(kid02_part182),(kid02_part183),(kid02_part184),(kid02_part185),(kid02_part186),(kid02_part187),(kid02_part188),(kid02_part189),(kid02_part190),(kid02_part191),(kid02_part192),(kid02_part193),(kid02_part194),(kid02_part195),(kid02_part196),(kid02_part197)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part174_checked

  · exact kid02_part180_checked

  · exact kid02_part186_checked

  · exact kid02_part192_checked

  · exact kid02_part175_checked

  · exact kid02_part181_checked

  · exact kid02_part187_checked

  · exact kid02_part193_checked

  · exact kid02_part176_checked

  · exact kid02_part182_checked

  · exact kid02_part188_checked

  · exact kid02_part194_checked

  · exact kid02_part177_checked

  · exact kid02_part183_checked

  · exact kid02_part189_checked

  · exact kid02_part195_checked

  · exact kid02_part178_checked

  · exact kid02_part184_checked

  · exact kid02_part190_checked

  · exact kid02_part196_checked

  · exact kid02_part179_checked

  · exact kid02_part185_checked

  · exact kid02_part191_checked

  · exact kid02_part197_checked

def kid02_part198 : Audit := .cycle 9 1 true (1)
theorem kid02_part198_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part198) = true := by rfl

def kid02_part102 : Audit := .split 9 (5,false) (byMove [(kid02_part103),(kid02_part104),(kid02_part105),(kid02_part106),(kid02_part107),(kid02_part132),(kid02_part133),(kid02_part134),(kid02_part135),(kid02_part136),(kid02_part137),(kid02_part138),(kid02_part139),(kid02_part140),(kid02_part141),(kid02_part142),(kid02_part143),(kid02_part168),(kid02_part169),(kid02_part170),(kid02_part171),(kid02_part172),(kid02_part173),(kid02_part198)])

theorem kid02_part102_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (kid02_part102) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid02_part103),(kid02_part104),(kid02_part105),(kid02_part106),(kid02_part107),(kid02_part132),(kid02_part133),(kid02_part134),(kid02_part135),(kid02_part136),(kid02_part137),(kid02_part138),(kid02_part139),(kid02_part140),(kid02_part141),(kid02_part142),(kid02_part143),(kid02_part168),(kid02_part169),(kid02_part170),(kid02_part171),(kid02_part172),(kid02_part173),(kid02_part198)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part103_checked

  · exact kid02_part133_checked

  · exact kid02_part139_checked

  · exact kid02_part169_checked

  · exact kid02_part104_checked

  · exact kid02_part134_checked

  · exact kid02_part140_checked

  · exact kid02_part170_checked

  · exact kid02_part105_checked

  · exact kid02_part135_checked

  · exact kid02_part141_checked

  · exact kid02_part171_checked

  · exact kid02_part106_checked

  · exact kid02_part136_checked

  · exact kid02_part142_checked

  · exact kid02_part172_checked

  · exact kid02_part107_checked

  · exact kid02_part137_checked

  · exact kid02_part143_checked

  · exact kid02_part173_checked

  · exact kid02_part132_checked

  · exact kid02_part138_checked

  · exact kid02_part168_checked

  · exact kid02_part198_checked

def kid02_part199 : Audit := .cycle 0 9 true (0)
theorem kid02_part199_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,0⟩)) (kid02_part199) = true := by rfl

def kid02_part200 : Audit := .cycle 1 8 true (1)
theorem kid02_part200_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,1⟩)) (kid02_part200) = true := by rfl

def kid02_part201 : Audit := .cycle 1 20 true (0)
theorem kid02_part201_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,2⟩)) (kid02_part201) = true := by rfl

def kid02_part202 : Audit := .cycle 16 1 false (2)
theorem kid02_part202_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,3⟩)) (kid02_part202) = true := by rfl

def kid02_part204 : Audit := .cycle 0 10 true (0)
theorem kid02_part204_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part204) = true := by rfl

def kid02_part205 : Audit := .cycle 1 9 true (1)
theorem kid02_part205_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part205) = true := by rfl

def kid02_part206 : Audit := .cycle 20 1 false (2)
theorem kid02_part206_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part206) = true := by rfl

def kid02_part207 : Audit := .cycle 17 1 false (1)
theorem kid02_part207_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part207) = true := by rfl

def kid02_part208 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 17 1 false (-1),
.cycle 10 6 false (2),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 1 13 false (3),
.cycle 21 1 false (1),
.cycle 1 16 true (-1),
.cycle 11 3 false (1),
.cycle 13 1 true (-1)
]),
.cycle 0 13 true (0),
.cycle 21 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 22 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 17 1 false (1),
.cycle 10 6 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 1 false (3),
.cycle 1 16 true (0),
.cycle 11 3 true (0),
.cycle 13 1 true (1)
]),
.cycle 16 1 false (0),
.cycle 10 5 false (2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.last 20 (5,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 1 14 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 17 1 false (-1),
.cycle 20 1 false (-2),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 16 1 false (0),
.cycle 10 5 false (2),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.cycle 12 2 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 9 14 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 10 4 true (0),
.cycle 13 1 true (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 3 true (0),
.cycle 1 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 11 3 true (0),
.cycle 13 1 true (1)
])
])
theorem kid02_part208_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part208) = true := by rfl

def kid02_part209 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 21 2 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 16 2 false (0),
.last 17 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 2 false (2),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (0),
.cycle 12 2 true (0),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 9 2 true (2),
.cycle 10 1 true (2),
.cycle 17 5 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 16 2 false (0),
.last 17 (4,true),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (4,true),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 18 2 false (2),
.cycle 11 2 true (0),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.last 14 (4,true),
.cycle 1 14 true (0),
.last 13 (4,true),
.cycle 15 1 false (3),
.cycle 17 1 false (-1),
.last 15 (4,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.last 14 (4,true),
.cycle 1 14 true (0),
.last 13 (4,true),
.cycle 13 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 13 4 false (1),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.cycle 21 7 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 4 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 10 3 true (2)
]),
.cycle 10 1 true (2)
])
theorem kid02_part209_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part209) = true := by rfl

def kid02_part210 : Audit := .cycle 0 10 true (0)
theorem kid02_part210_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part210) = true := by rfl

def kid02_part211 : Audit := .cycle 1 9 true (1)
theorem kid02_part211_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part211) = true := by rfl

def kid02_part212 : Audit := .split 22 (4,true) (byMove [
.cycle 0 39 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.split 23 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 36 1 false (8),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 26 1 false (4),
.cycle 23 1 false (3),
.cycle 29 1 false (7),
.cycle 50 1 false (12),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 28 1 false (8),
.last 25 (5,true),
.cycle 0 30 true (0),
.cycle 45 16 true (5),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (3),
.cycle 0 41 true (0),
.cycle 1 39 true (0),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.cycle 8 17 true (0),
.last 25 (5,true)
]),
.cycle 1 23 true (0),
.cycle 25 1 false (5),
.cycle 26 1 false (8),
.cycle 0 24 true (0),
.cycle 26 1 false (8),
.split 23 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 34 1 false (8),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.cycle 26 1 false (6),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 34 1 false (10),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.cycle 26 1 false (8),
.last 24 (5,false),
.cycle 29 1 false (7),
.last 39 (5,false),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 28 1 false (8),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 33 1 false (9),
.cycle 1 26 true (0),
.cycle 37 1 false (11),
.last 24 (5,false)
]),
.cycle 30 1 false (8),
.cycle 24 15 true (4),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 30 1 false (8),
.split 23 (5,false) (byMove [
.cycle 30 17 true (4),
.cycle 1 27 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 1 27 true (0),
.cycle 23 1 false (3),
.cycle 29 1 false (7),
.cycle 26 1 false (4),
.cycle 30 1 false (8),
.cycle 1 25 true (0),
.cycle 22 2 true (3),
.last 24 (5,true),
.cycle 38 1 false (8),
.cycle 30 1 false (2),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 20 4 true (2),
.cycle 23 1 false (3),
.cycle 1 41 true (0),
.cycle 30 1 false (8),
.cycle 24 15 true (4),
.cycle 1 25 true (0),
.last 25 (5,true),
.last 24 (5,true)
]),
.cycle 1 23 true (0),
.cycle 27 1 false (7),
.cycle 46 1 false (12),
.cycle 0 24 true (0),
.cycle 22 30 true (4),
.split 23 (5,true) (byMove [
.cycle 1 24 true (0),
.cycle 26 1 false (4),
.cycle 27 1 false (7),
.cycle 0 25 true (0),
.last 25 (5,false),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 58 1 false (12),
.cycle 36 1 false (10),
.cycle 32 1 false (8),
.last 37 (5,false),
.last 24 (5,false),
.cycle 29 1 false (7),
.cycle 26 1 false (4),
.last 26 (5,false),
.cycle 1 25 true (0),
.cycle 22 2 true (4),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 1 26 true (0),
.cycle 22 30 true (4),
.last 24 (5,false)
])
])
theorem kid02_part212_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part212) = true := by rfl

def kid02_part213 : Audit := .cycle 1 20 true (0)
theorem kid02_part213_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part213) = true := by rfl

def kid02_part214 : Audit := .cycle 9 1 true (3)
theorem kid02_part214_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part214) = true := by rfl

def kid02_part216 : Audit := .cycle 0 11 true (0)
theorem kid02_part216_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part216) = true := by rfl

def kid02_part217 : Audit := .cycle 1 10 true (1)
theorem kid02_part217_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part217) = true := by rfl

def kid02_part218 : Audit := .split 21 (5,true) (byMove [
.cycle 0 37 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 1 22 true (0),
.cycle 24 1 false (4),
.cycle 26 1 false (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 25 1 false (5),
.cycle 33 1 false (5),
.last 24 (4,true),
.cycle 1 24 true (0),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 24 1 false (2),
.cycle 1 22 true (0),
.cycle 27 1 false (5),
.cycle 45 1 false (9),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 42 1 false (8)
])
theorem kid02_part218_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part218) = true := by rfl

def kid02_part219 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 25 1 false (3),
.cycle 32 1 false (4),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 1 22 true (0),
.cycle 1 24 true (0),
.cycle 0 22 true (0)
])
theorem kid02_part219_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part219) = true := by rfl

def kid02_part220 : Audit := .cycle 9 2 true (3)
theorem kid02_part220_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part220) = true := by rfl

def kid02_part221 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 24 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 19 1 false (1),
.cycle 11 7 false (3),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 1 17 true (0),
.cycle 12 4 true (0),
.cycle 13 2 true (0)
])
theorem kid02_part221_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part221) = true := by rfl

def kid02_part222 : Audit := .cycle 0 11 true (0)
theorem kid02_part222_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part222) = true := by rfl

def kid02_part223 : Audit := .cycle 1 10 true (1)
theorem kid02_part223_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part223) = true := by rfl

def kid02_part224 : Audit := .split 23 (5,true) (byMove [
.last 27 (4,true),
.cycle 1 91 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.last 27 (4,true),
.cycle 33 1 false (9),
.cycle 0 29 true (0),
.cycle 26 1 false (4),
.last 25 (4,true),
.cycle 31 1 false (9),
.last 24 (4,true),
.cycle 29 1 false (9),
.cycle 45 1 false (9),
.last 26 (4,true),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 22 2 true (2),
.last 26 (4,true),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.last 25 (4,true),
.cycle 5 19 true (0),
.last 24 (4,true),
.cycle 26 11 true (6)
])
theorem kid02_part224_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part224) = true := by rfl

def kid02_part225 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 27 1 false (7),
.cycle 24 1 false (4),
.last 23 (4,true),
.cycle 1 23 true (0),
.last 22 (4,true),
.cycle 25 1 false (7),
.cycle 37 1 false (7),
.last 24 (4,true),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 29 1 false (7),
.cycle 1 37 true (0),
.cycle 1 25 true (0),
.last 23 (4,true),
.cycle 1 23 true (0),
.last 22 (4,true),
.cycle 3 22 true (0)
])
theorem kid02_part225_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part225) = true := by rfl

def kid02_part226 : Audit := .cycle 9 2 true (3)
theorem kid02_part226_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part226) = true := by rfl

def kid02_part227 : Audit := .cycle 10 1 true (4)
theorem kid02_part227_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part227) = true := by rfl

def kid02_part228 : Audit := .cycle 7 5 true (2)
theorem kid02_part228_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part228) = true := by rfl

def kid02_part229 : Audit := .cycle 8 4 true (2)
theorem kid02_part229_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part229) = true := by rfl

def kid02_part230 : Audit := .cycle 0 13 true (0)
theorem kid02_part230_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part230) = true := by rfl

def kid02_part231 : Audit := .split 19 (5,true) (byMove [
.cycle 0 33 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 1 20 true (0),
.cycle 22 1 false (4),
.cycle 23 1 false (5),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 22 1 false (4),
.cycle 30 1 false (4),
.last 22 (4,true),
.cycle 1 22 true (0),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 21 1 false (1),
.cycle 1 20 true (0),
.cycle 24 1 false (4),
.cycle 40 1 false (8),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 1 23 true (0)
])
theorem kid02_part231_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part231) = true := by rfl

def kid02_part232 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 9 4 true (3),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (4,true),
.cycle 1 25 true (0),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 11 2 true (3),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.last 14 (4,true)
])
theorem kid02_part232_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part232) = true := by rfl

def kid02_part233 : Audit := .split 14 (5,true) (byMove [
.last 18 (4,true),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 1 20 true (0),
.cycle 17 1 false (1),
.last 16 (4,true),
.cycle 21 1 false (5),
.last 15 (4,true),
.cycle 19 1 false (5),
.cycle 39 1 false (5),
.last 17 (4,true),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 15 1 false (-1),
.cycle 1 20 true (0),
.cycle 1 22 true (0),
.last 16 (4,true),
.cycle 1 23 true (0),
.last 15 (4,true),
.cycle 17 3 true (3)
])
theorem kid02_part233_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part233) = true := by rfl

def kid02_part234 : Audit := .cycle 0 11 true (0)
theorem kid02_part234_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part234) = true := by rfl

def kid02_part235 : Audit := .cycle 1 10 true (1)
theorem kid02_part235_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part235) = true := by rfl

def kid02_part236 : Audit := .cycle 2 9 true (1)
theorem kid02_part236_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part236) = true := by rfl

def kid02_part237 : Audit := .cycle 1 13 true (1)
theorem kid02_part237_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part237) = true := by rfl

def kid02_part238 : Audit := .cycle 9 2 true (3)
theorem kid02_part238_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part238) = true := by rfl

def kid02_part239 : Audit := .cycle 10 1 true (4)
theorem kid02_part239_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part239) = true := by rfl

def kid02_part215 : Audit := .split 10 (5,false) (byMove [(kid02_part216),(kid02_part217),(kid02_part218),(kid02_part219),(kid02_part220),(kid02_part221),(kid02_part222),(kid02_part223),(kid02_part224),(kid02_part225),(kid02_part226),(kid02_part227),(kid02_part228),(kid02_part229),(kid02_part230),(kid02_part231),(kid02_part232),(kid02_part233),(kid02_part234),(kid02_part235),(kid02_part236),(kid02_part237),(kid02_part238),(kid02_part239)])

theorem kid02_part215_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part215) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid02_part216),(kid02_part217),(kid02_part218),(kid02_part219),(kid02_part220),(kid02_part221),(kid02_part222),(kid02_part223),(kid02_part224),(kid02_part225),(kid02_part226),(kid02_part227),(kid02_part228),(kid02_part229),(kid02_part230),(kid02_part231),(kid02_part232),(kid02_part233),(kid02_part234),(kid02_part235),(kid02_part236),(kid02_part237),(kid02_part238),(kid02_part239)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part216_checked

  · exact kid02_part222_checked

  · exact kid02_part228_checked

  · exact kid02_part234_checked

  · exact kid02_part217_checked

  · exact kid02_part223_checked

  · exact kid02_part229_checked

  · exact kid02_part235_checked

  · exact kid02_part218_checked

  · exact kid02_part224_checked

  · exact kid02_part230_checked

  · exact kid02_part236_checked

  · exact kid02_part219_checked

  · exact kid02_part225_checked

  · exact kid02_part231_checked

  · exact kid02_part237_checked

  · exact kid02_part220_checked

  · exact kid02_part226_checked

  · exact kid02_part232_checked

  · exact kid02_part238_checked

  · exact kid02_part221_checked

  · exact kid02_part227_checked

  · exact kid02_part233_checked

  · exact kid02_part239_checked

def kid02_part240 : Audit := .cycle 7 4 true (2)
theorem kid02_part240_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part240) = true := by rfl

def kid02_part241 : Audit := .cycle 8 3 true (2)
theorem kid02_part241_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part241) = true := by rfl

def kid02_part242 : Audit := .cycle 0 12 true (0)
theorem kid02_part242_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part242) = true := by rfl

def kid02_part243 : Audit := .cycle 17 1 false (1)
theorem kid02_part243_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part243) = true := by rfl

def kid02_part244 : Audit := .split 12 (4,true) (byMove [
.cycle 14 27 true (0),
.cycle 9 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.last 26 (5,true),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 22 22 true (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 15 (5,true),
.cycle 17 1 false (-1),
.cycle 10 6 false (2),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.last 23 (5,true),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.cycle 11 3 false (1),
.last 15 (5,true)
]),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.split 13 (5,true) (byMove [
.last 18 (5,false),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 16 (5,false),
.cycle 1 15 true (0),
.cycle 16 1 false (4),
.last 16 (5,false),
.cycle 17 1 false (1),
.last 27 (5,false),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 1 21 true (0),
.cycle 16 1 false (2),
.last 16 (5,false),
.cycle 1 15 true (0),
.cycle 14 3 true (2),
.last 16 (5,false)
]),
.cycle 16 1 false (0),
.cycle 59 1 false (-1),
.cycle 18 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.last 35 (5,true),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 24 1 false (4),
.cycle 18 1 false (2),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 17 1 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.cycle 16 1 false (0),
.last 27 (5,true),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 10 6 true (0),
.cycle 15 1 false (1),
.cycle 18 16 true (2),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.split 13 (5,true) (byMove [
.last 18 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 18 1 false (2),
.last 15 (5,false),
.last 15 (5,false),
.cycle 6 8 true (0),
.cycle 22 1 false (2),
.last 16 (5,false),
.cycle 1 15 true (0),
.last 21 (5,false),
.last 16 (5,false),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 22 (5,false),
.cycle 18 1 false (2),
.cycle 12 2 true (0),
.last 15 (5,false),
.cycle 1 21 true (0),
.cycle 10 6 true (0),
.last 16 (5,false),
.cycle 1 15 true (0),
.cycle 14 3 true (2),
.last 16 (5,false)
])
])
theorem kid02_part244_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part244) = true := by rfl

def kid02_part246 : Audit := .cycle 12 5 true (2)
theorem kid02_part246_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part246) = true := by rfl

def kid02_part247 : Audit := .cycle 0 14 true (0)
theorem kid02_part247_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part247) = true := by rfl

def kid02_part248 : Audit := .cycle 21 1 false (1)
theorem kid02_part248_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part248) = true := by rfl

def kid02_part249 : Audit := .cycle 7 13 true (0)
theorem kid02_part249_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part249) = true := by rfl

def kid02_part250 : Audit := .split 12 (5,true) (byMove [
.last 18 (4,true),
.last 23 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (4,true),
.cycle 15 1 false (1),
.cycle 14 2 false (2),
.cycle 17 2 false (3),
.last 13 (4,true),
.cycle 14 2 false (2),
.cycle 16 2 false (0),
.last 15 (4,true),
.last 20 (4,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (4,true),
.cycle 15 2 false (1),
.last 16 (4,true),
.cycle 7 8 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid02_part250_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part250) = true := by rfl

def kid02_part251 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 7 13 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.last 22 (4,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 15 6 true (2),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.cycle 4 17 true (0),
.last 15 (4,true),
.cycle 11 2 true (0)
])
theorem kid02_part251_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part251) = true := by rfl

def kid02_part252 : Audit := .cycle 1 11 true (1)
theorem kid02_part252_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part252) = true := by rfl

def kid02_part253 : Audit := .cycle 24 1 false (2)
theorem kid02_part253_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part253) = true := by rfl

def kid02_part254 : Audit := .cycle 8 3 true (2)
theorem kid02_part254_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part254) = true := by rfl

def kid02_part255 : Audit := .cycle 0 12 true (0)
theorem kid02_part255_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part255) = true := by rfl

def kid02_part256 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (8),
.cycle 1 24 true (0),
.cycle 9 3 true (2),
.cycle 9 4 true (2),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 9 4 true (2)
])
theorem kid02_part256_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part256) = true := by rfl

def kid02_part257 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 3 false (0),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,true),
.cycle 1 24 true (0),
.cycle 9 3 true (2),
.cycle 12 1 true (4),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 3 false (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 12 1 true (4)
])
theorem kid02_part257_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part257) = true := by rfl

def kid02_part258 : Audit := .cycle 17 5 false (1)
theorem kid02_part258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part258) = true := by rfl

def kid02_part259 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 20, 16, 128, 256, 8, 128, 4096, 20, 4096],[128, 20, 16, 1, 4, 4096, 128, 20, 16, 1, 4, 4096, 4096],5120⟩,
.cycle 0 27 true (0),
.cycle 9 5 true (1),
.last 32 (5,true),
.cycle 33 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.last 28 (5,true)
])
theorem kid02_part259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part259) = true := by rfl

def kid02_part260 : Audit := .cycle 1 13 true (1)
theorem kid02_part260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part260) = true := by rfl

def kid02_part261 : Audit := .cycle 18 1 false (0)
theorem kid02_part261_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part261) = true := by rfl

def kid02_part262 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 23 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.cycle 15 1 false (1),
.last 14 (4,true),
.cycle 17 2 false (3),
.last 13 (4,true),
.cycle 16 2 false (4),
.cycle 16 2 false (0),
.last 15 (4,true),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (4,true),
.cycle 15 2 false (1),
.last 14 (4,true),
.cycle 5 8 true (0),
.last 13 (4,true),
.last 17 (4,true)
])
theorem kid02_part262_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part262) = true := by rfl

def kid02_part263 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.last 14 (4,true),
.cycle 18 1 false (2),
.last 13 (4,true),
.cycle 16 1 false (4),
.cycle 17 1 false (-1),
.last 15 (4,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 6 true (0),
.cycle 16 1 false (0),
.last 14 (4,true),
.cycle 5 8 true (0),
.last 13 (4,true),
.cycle 14 3 true (2)
])
theorem kid02_part263_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part263) = true := by rfl

def kid02_part264 : Audit := .cycle 1 11 true (1)
theorem kid02_part264_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part264) = true := by rfl

def kid02_part265 : Audit := .cycle 7 4 true (2)
theorem kid02_part265_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part265) = true := by rfl

def kid02_part266 : Audit := .cycle 8 3 true (2)
theorem kid02_part266_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part266) = true := by rfl

def kid02_part267 : Audit := .cycle 0 12 true (0)
theorem kid02_part267_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part267) = true := by rfl

def kid02_part268 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.last 14 (5,true)
])
theorem kid02_part268_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part268) = true := by rfl

def kid02_part269 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 12 1 true (4)
])
theorem kid02_part269_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part269) = true := by rfl

def kid02_part245 : Audit := .split 10 (5,false) (byMove [(kid02_part246),(kid02_part247),(kid02_part248),(kid02_part249),(kid02_part250),(kid02_part251),(kid02_part252),(kid02_part253),(kid02_part254),(kid02_part255),(kid02_part256),(kid02_part257),(kid02_part258),(kid02_part259),(kid02_part260),(kid02_part261),(kid02_part262),(kid02_part263),(kid02_part264),(kid02_part265),(kid02_part266),(kid02_part267),(kid02_part268),(kid02_part269)])

theorem kid02_part245_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part245) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid02_part246),(kid02_part247),(kid02_part248),(kid02_part249),(kid02_part250),(kid02_part251),(kid02_part252),(kid02_part253),(kid02_part254),(kid02_part255),(kid02_part256),(kid02_part257),(kid02_part258),(kid02_part259),(kid02_part260),(kid02_part261),(kid02_part262),(kid02_part263),(kid02_part264),(kid02_part265),(kid02_part266),(kid02_part267),(kid02_part268),(kid02_part269)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part246_checked

  · exact kid02_part252_checked

  · exact kid02_part258_checked

  · exact kid02_part264_checked

  · exact kid02_part247_checked

  · exact kid02_part253_checked

  · exact kid02_part259_checked

  · exact kid02_part265_checked

  · exact kid02_part248_checked

  · exact kid02_part254_checked

  · exact kid02_part260_checked

  · exact kid02_part266_checked

  · exact kid02_part249_checked

  · exact kid02_part255_checked

  · exact kid02_part261_checked

  · exact kid02_part267_checked

  · exact kid02_part250_checked

  · exact kid02_part256_checked

  · exact kid02_part262_checked

  · exact kid02_part268_checked

  · exact kid02_part251_checked

  · exact kid02_part257_checked

  · exact kid02_part263_checked

  · exact kid02_part269_checked

def kid02_part270 : Audit := .cycle 0 10 true (0)
theorem kid02_part270_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part270) = true := by rfl

def kid02_part271 : Audit := .cycle 1 9 true (1)
theorem kid02_part271_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part271) = true := by rfl

def kid02_part272 : Audit := .cycle 2 8 true (1)
theorem kid02_part272_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part272) = true := by rfl

def kid02_part273 : Audit := .cycle 1 12 true (1)
theorem kid02_part273_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part273) = true := by rfl

def kid02_part274 : Audit := .cycle 9 1 true (3)
theorem kid02_part274_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part274) = true := by rfl

def kid02_part276 : Audit := .cycle 1 11 true (1)
theorem kid02_part276_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part276) = true := by rfl

def kid02_part277 : Audit := .split 21 (5,true) (byMove [
.cycle 1 22 true (0),
.cycle 24 1 false (2),
.cycle 27 1 false (3),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 36 1 false (2),
.cycle 0 22 true (0),
.cycle 56 1 false (6),
.cycle 12 10 true (0),
.cycle 32 1 false (4),
.cycle 36 1 false (4),
.cycle 1 22 true (0),
.cycle 29 1 false (3),
.cycle 24 1 false (2),
.last 23 (4,true),
.cycle 1 23 true (0),
.last 22 (4,true),
.cycle 1 27 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 24 true (0),
.cycle 40 1 false (4),
.cycle 29 1 false (3)
])
theorem kid02_part277_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part277) = true := by rfl

def kid02_part278 : Audit := .cycle 8 3 true (2)
theorem kid02_part278_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part278) = true := by rfl

def kid02_part279 : Audit := .cycle 0 12 true (0)
theorem kid02_part279_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part279) = true := by rfl

def kid02_part280 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 9 3 true (3),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 19 (5,true),
.last 13 (5,true),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
])
theorem kid02_part280_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part280) = true := by rfl

def kid02_part281 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (4,true),
.cycle 0 23 true (0),
.cycle 9 3 true (3),
.cycle 17 1 false (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 1 21 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
])
theorem kid02_part281_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part281) = true := by rfl

def kid02_part282 : Audit := .cycle 0 11 true (0)
theorem kid02_part282_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part282) = true := by rfl

def kid02_part283 : Audit := .cycle 1 10 true (1)
theorem kid02_part283_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part283) = true := by rfl

def kid02_part284 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 36 1 false (2),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 39 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.cycle 9 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 34, 16, 1, 64, 32, 64],64⟩,
.cycle 6 15 true (2),
.cycle 36 1 false (2),
.last 22 (4,true),
.cycle 1 22 true (1),
.last 21 (4,true),
.last 24 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 12 true (3),
.cycle 10 11 true (3)
])
theorem kid02_part284_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part284) = true := by rfl

def kid02_part285 : Audit := .cycle 3 8 true (1)
theorem kid02_part285_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part285) = true := by rfl

def kid02_part286 : Audit := .cycle 9 2 true (3)
theorem kid02_part286_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part286) = true := by rfl

def kid02_part287 : Audit := .cycle 10 1 true (4)
theorem kid02_part287_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part287) = true := by rfl

def kid02_part288 : Audit := .cycle 6 5 true (2)
theorem kid02_part288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part288) = true := by rfl

def kid02_part289 : Audit := .split 21 (5,true) (byMove [
.cycle 1 37 true (0),
.cycle 24 1 false (2),
.cycle 30 1 false (4),
.cycle 30 1 false (4),
.last 22 (4,true),
.cycle 14 16 true (0),
.cycle 1 22 true (0),
.cycle 34 1 false (4),
.cycle 8 14 true (0),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 22 15 true (4),
.cycle 34 1 false (4),
.cycle 24 1 false (2),
.last 23 (4,true),
.cycle 30 1 false (4),
.last 22 (4,true),
.last 26 (4,true),
.cycle 1 22 true (0),
.cycle 1 35 true (0),
.cycle 2 33 true (0),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 22 5 true (3)
])
theorem kid02_part289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part289) = true := by rfl

def kid02_part290 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 9 4 true (3),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.last 21 (5,true),
.last 14 (5,true),
.cycle 1 16 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
])
theorem kid02_part290_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part290) = true := by rfl

def kid02_part291 : Audit := .cycle 1 12 true (1)
theorem kid02_part291_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part291) = true := by rfl

def kid02_part292 : Audit := .split 11 (4,true) (byMove [
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.last 14 (5,true),
.cycle 1 12 true (1),
.last 23 (5,true),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true),
.last 16 (5,true),
.cycle 8 8 true (2),
.cycle 1 14 true (1),
.last 19 (5,true),
.last 13 (5,true),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true)
])
theorem kid02_part292_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part292) = true := by rfl

def kid02_part293 : Audit := .split 11 (5,true) (byMove [
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 37 1 false (5),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 24 1 false (6),
.cycle 6 11 true (2),
.last 14 (4,true),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (3)
])
theorem kid02_part293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part293) = true := by rfl

def kid02_part294 : Audit := .cycle 0 11 true (0)
theorem kid02_part294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part294) = true := by rfl

def kid02_part295 : Audit := .cycle 1 10 true (1)
theorem kid02_part295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part295) = true := by rfl

def kid02_part296 : Audit := .cycle 2 9 true (1)
theorem kid02_part296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part296) = true := by rfl

def kid02_part297 : Audit := .cycle 1 13 true (1)
theorem kid02_part297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part297) = true := by rfl

def kid02_part298 : Audit := .cycle 9 2 true (3)
theorem kid02_part298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part298) = true := by rfl

def kid02_part299 : Audit := .cycle 10 1 true (4)
theorem kid02_part299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part299) = true := by rfl

def kid02_part275 : Audit := .split 10 (5,false) (byMove [(kid02_part276),(kid02_part277),(kid02_part278),(kid02_part279),(kid02_part280),(kid02_part281),(kid02_part282),(kid02_part283),(kid02_part284),(kid02_part285),(kid02_part286),(kid02_part287),(kid02_part288),(kid02_part289),(kid02_part290),(kid02_part291),(kid02_part292),(kid02_part293),(kid02_part294),(kid02_part295),(kid02_part296),(kid02_part297),(kid02_part298),(kid02_part299)])

theorem kid02_part275_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part275) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid02_part276),(kid02_part277),(kid02_part278),(kid02_part279),(kid02_part280),(kid02_part281),(kid02_part282),(kid02_part283),(kid02_part284),(kid02_part285),(kid02_part286),(kid02_part287),(kid02_part288),(kid02_part289),(kid02_part290),(kid02_part291),(kid02_part292),(kid02_part293),(kid02_part294),(kid02_part295),(kid02_part296),(kid02_part297),(kid02_part298),(kid02_part299)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part276_checked

  · exact kid02_part282_checked

  · exact kid02_part288_checked

  · exact kid02_part294_checked

  · exact kid02_part277_checked

  · exact kid02_part283_checked

  · exact kid02_part289_checked

  · exact kid02_part295_checked

  · exact kid02_part278_checked

  · exact kid02_part284_checked

  · exact kid02_part290_checked

  · exact kid02_part296_checked

  · exact kid02_part279_checked

  · exact kid02_part285_checked

  · exact kid02_part291_checked

  · exact kid02_part297_checked

  · exact kid02_part280_checked

  · exact kid02_part286_checked

  · exact kid02_part292_checked

  · exact kid02_part298_checked

  · exact kid02_part281_checked

  · exact kid02_part287_checked

  · exact kid02_part293_checked

  · exact kid02_part299_checked

def kid02_part203 : Audit := .split 9 (4,false) (byMove [(kid02_part204),(kid02_part205),(kid02_part206),(kid02_part207),(kid02_part208),(kid02_part209),(kid02_part210),(kid02_part211),(kid02_part212),(kid02_part213),(kid02_part214),(kid02_part215),(kid02_part240),(kid02_part241),(kid02_part242),(kid02_part243),(kid02_part244),(kid02_part245),(kid02_part270),(kid02_part271),(kid02_part272),(kid02_part273),(kid02_part274),(kid02_part275)])

theorem kid02_part203_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (kid02_part203) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid02_part204),(kid02_part205),(kid02_part206),(kid02_part207),(kid02_part208),(kid02_part209),(kid02_part210),(kid02_part211),(kid02_part212),(kid02_part213),(kid02_part214),(kid02_part215),(kid02_part240),(kid02_part241),(kid02_part242),(kid02_part243),(kid02_part244),(kid02_part245),(kid02_part270),(kid02_part271),(kid02_part272),(kid02_part273),(kid02_part274),(kid02_part275)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part204_checked

  · exact kid02_part210_checked

  · exact kid02_part240_checked

  · exact kid02_part270_checked

  · exact kid02_part205_checked

  · exact kid02_part211_checked

  · exact kid02_part241_checked

  · exact kid02_part271_checked

  · exact kid02_part206_checked

  · exact kid02_part212_checked

  · exact kid02_part242_checked

  · exact kid02_part272_checked

  · exact kid02_part207_checked

  · exact kid02_part213_checked

  · exact kid02_part243_checked

  · exact kid02_part273_checked

  · exact kid02_part208_checked

  · exact kid02_part214_checked

  · exact kid02_part244_checked

  · exact kid02_part274_checked

  · exact kid02_part209_checked

  · exact kid02_part215_checked

  · exact kid02_part245_checked

  · exact kid02_part275_checked

def kid02_part301 : Audit := .cycle 0 10 true (0)
theorem kid02_part301_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part301) = true := by rfl

def kid02_part302 : Audit := .cycle 1 9 true (1)
theorem kid02_part302_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part302) = true := by rfl

def kid02_part303 : Audit := .cycle 20 1 false (2)
theorem kid02_part303_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part303) = true := by rfl

def kid02_part304 : Audit := .cycle 17 1 false (1)
theorem kid02_part304_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part304) = true := by rfl

def kid02_part305 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 12 2 true (0)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 21 2 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 16 2 false (0),
.last 17 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 2 false (2),
.cycle 1 15 true (0),
.last 14 (5,true),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (2),
.cycle 17 5 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.last 14 (5,true),
.cycle 1 14 true (0),
.cycle 15 1 false (3),
.last 13 (5,true),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 1 14 true (0),
.cycle 13 3 true (1),
.last 13 (5,true)
]),
.split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 16 2 false (0),
.last 17 (5,true),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (5,true),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 18 2 false (2),
.last 14 (5,true),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (2),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 3 false (0),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 10 3 true (2),
.cycle 9 4 true (2),
.cycle 21 7 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (2),
.cycle 11 2 true (2)
])
])
theorem kid02_part305_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part305) = true := by rfl

def kid02_part306 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 10 6 false (2),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 27 (4,true),
.cycle 1 13 false (3),
.cycle 21 1 false (1),
.cycle 1 16 true (-1),
.cycle 13 1 true (-1),
.cycle 11 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 21 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 22 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 14 1 false (2),
.cycle 17 1 false (1),
.cycle 10 6 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 1 false (3),
.cycle 1 16 true (0),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
]),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 10 5 false (2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 20 (4,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 1 14 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 17 1 false (-1),
.cycle 20 1 false (-2),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 27 (4,true),
.cycle 16 1 false (0),
.cycle 10 5 false (2),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 1 15 true (0),
.split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 9 14 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 13 1 true (1),
.cycle 10 4 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 3 true (0),
.cycle 1 15 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
]),
.cycle 11 2 true (0)
])
theorem kid02_part306_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part306) = true := by rfl

def kid02_part307 : Audit := .cycle 0 10 true (0)
theorem kid02_part307_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part307) = true := by rfl

def kid02_part308 : Audit := .cycle 1 9 true (1)
theorem kid02_part308_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part308) = true := by rfl

def kid02_part309 : Audit := .split 22 (5,true) (byMove [
.cycle 0 39 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.split 23 (4,false) (byMove [
.cycle 0 28 true (0),
.cycle 36 1 false (8),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 23 1 false (3),
.cycle 26 1 false (4),
.cycle 29 1 false (7),
.cycle 50 1 false (12),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 25 (4,true),
.cycle 28 1 false (8),
.cycle 0 30 true (0),
.cycle 45 16 true (5),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (3),
.cycle 30 1 false (8),
.cycle 0 41 true (0),
.cycle 1 39 true (0),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.last 25 (4,true),
.cycle 8 17 true (0)
]),
.cycle 0 26 true (0),
.cycle 1 23 true (0),
.cycle 25 1 false (5),
.cycle 26 1 false (8),
.cycle 0 24 true (0),
.split 23 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 34 1 false (8),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.last 24 (4,false),
.cycle 26 1 false (6),
.cycle 0 24 true (0),
.cycle 34 1 false (10),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.last 24 (4,false),
.cycle 26 1 false (8),
.cycle 29 1 false (7),
.last 39 (4,false),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 24 (4,false),
.cycle 28 1 false (8),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 33 1 false (9),
.cycle 1 26 true (0),
.last 24 (4,false),
.cycle 37 1 false (11)
]),
.cycle 26 1 false (8),
.cycle 30 1 false (8),
.cycle 24 15 true (4),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.split 23 (4,false) (byMove [
.cycle 30 17 true (4),
.cycle 1 27 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 23 1 false (3),
.cycle 1 27 true (0),
.cycle 29 1 false (7),
.cycle 26 1 false (4),
.cycle 30 1 false (8),
.cycle 1 25 true (0),
.last 24 (4,true),
.cycle 22 2 true (3),
.cycle 38 1 false (8),
.cycle 30 1 false (2),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (3),
.cycle 20 4 true (2),
.cycle 1 41 true (0),
.cycle 30 1 false (8),
.cycle 24 15 true (4),
.cycle 1 25 true (0),
.last 24 (4,true),
.last 25 (4,true)
]),
.cycle 30 1 false (8),
.cycle 1 23 true (0),
.cycle 27 1 false (7),
.cycle 46 1 false (12),
.cycle 0 24 true (0),
.split 23 (4,true) (byMove [
.cycle 1 24 true (0),
.cycle 26 1 false (4),
.cycle 27 1 false (7),
.cycle 0 25 true (0),
.last 25 (4,false),
.last 25 (4,false),
.cycle 0 24 true (0),
.cycle 58 1 false (12),
.cycle 36 1 false (10),
.cycle 32 1 false (8),
.last 24 (4,false),
.last 37 (4,false),
.cycle 29 1 false (7),
.cycle 26 1 false (4),
.last 26 (4,false),
.cycle 1 25 true (0),
.last 25 (4,false),
.cycle 22 2 true (4),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 1 26 true (0),
.last 24 (4,false),
.cycle 22 30 true (4)
]),
.cycle 22 30 true (4)
])
theorem kid02_part309_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part309) = true := by rfl

def kid02_part310 : Audit := .cycle 1 20 true (0)
theorem kid02_part310_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part310) = true := by rfl

def kid02_part312 : Audit := .cycle 0 11 true (0)
theorem kid02_part312_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part312) = true := by rfl

def kid02_part313 : Audit := .cycle 1 10 true (1)
theorem kid02_part313_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part313) = true := by rfl

def kid02_part314 : Audit := .split 21 (4,true) (byMove [
.cycle 0 37 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (3),
.cycle 1 22 true (0),
.cycle 24 1 false (4),
.cycle 26 1 false (6),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.last 22 (5,true),
.cycle 33 1 false (5),
.last 24 (5,true),
.cycle 1 24 true (0),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 20 2 true (2),
.cycle 1 22 true (0),
.cycle 27 1 false (5),
.cycle 45 1 false (9),
.cycle 0 23 true (0),
.cycle 42 1 false (8),
.last 22 (5,true)
])
theorem kid02_part314_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part314) = true := by rfl

def kid02_part315 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 21 1 false (3),
.cycle 22 1 false (4),
.cycle 25 1 false (3),
.cycle 32 1 false (4),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 1 22 true (0),
.cycle 0 22 true (0),
.cycle 1 24 true (0)
])
theorem kid02_part315_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part315) = true := by rfl

def kid02_part316 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 24 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (2),
.cycle 19 1 false (1),
.cycle 11 7 false (3),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 1 17 true (0),
.cycle 13 2 true (0),
.cycle 12 4 true (0)
])
theorem kid02_part316_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part316) = true := by rfl

def kid02_part317 : Audit := .cycle 9 2 true (3)
theorem kid02_part317_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part317) = true := by rfl

def kid02_part318 : Audit := .cycle 0 11 true (0)
theorem kid02_part318_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part318) = true := by rfl

def kid02_part319 : Audit := .cycle 1 10 true (1)
theorem kid02_part319_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part319) = true := by rfl

def kid02_part320 : Audit := .split 23 (4,true) (byMove [
.last 27 (5,true),
.cycle 1 91 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.last 27 (5,true),
.cycle 0 29 true (0),
.cycle 26 1 false (4),
.last 25 (5,true),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.last 24 (5,true),
.cycle 45 1 false (9),
.last 26 (5,true),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.last 26 (5,true),
.cycle 22 2 true (2),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.last 25 (5,true),
.cycle 5 19 true (0),
.cycle 26 11 true (6),
.last 24 (5,true)
])
theorem kid02_part320_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part320) = true := by rfl

def kid02_part321 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 1 25 true (0),
.cycle 27 1 false (7),
.cycle 24 1 false (4),
.last 23 (5,true),
.cycle 1 23 true (0),
.cycle 25 1 false (7),
.last 22 (5,true),
.cycle 37 1 false (7),
.last 24 (5,true),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 29 1 false (7),
.cycle 20 2 true (2),
.cycle 1 37 true (0),
.cycle 1 25 true (0),
.last 23 (5,true),
.cycle 1 23 true (0),
.cycle 3 22 true (0),
.last 22 (5,true)
])
theorem kid02_part321_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part321) = true := by rfl

def kid02_part322 : Audit := .cycle 10 1 true (4)
theorem kid02_part322_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part322) = true := by rfl

def kid02_part323 : Audit := .cycle 9 2 true (3)
theorem kid02_part323_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part323) = true := by rfl

def kid02_part324 : Audit := .cycle 7 5 true (2)
theorem kid02_part324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part324) = true := by rfl

def kid02_part325 : Audit := .cycle 8 4 true (2)
theorem kid02_part325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part325) = true := by rfl

def kid02_part326 : Audit := .cycle 0 13 true (0)
theorem kid02_part326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part326) = true := by rfl

def kid02_part327 : Audit := .split 19 (4,true) (byMove [
.cycle 0 33 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 1 20 true (0),
.cycle 22 1 false (4),
.cycle 23 1 false (5),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.last 20 (5,true),
.cycle 30 1 false (4),
.last 22 (5,true),
.cycle 1 22 true (0),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 1 20 true (0),
.cycle 24 1 false (4),
.cycle 40 1 false (8),
.cycle 0 21 true (0),
.cycle 1 23 true (0),
.last 20 (5,true)
])
theorem kid02_part327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part327) = true := by rfl

def kid02_part328 : Audit := .split 14 (4,true) (byMove [
.last 18 (5,true),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 1 20 true (0),
.cycle 17 1 false (1),
.last 16 (5,true),
.cycle 21 1 false (5),
.cycle 19 1 false (5),
.last 15 (5,true),
.cycle 39 1 false (5),
.last 17 (5,true),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 1 20 true (0),
.cycle 1 22 true (0),
.last 16 (5,true),
.cycle 1 23 true (0),
.cycle 17 3 true (3),
.last 15 (5,true)
])
theorem kid02_part328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part328) = true := by rfl

def kid02_part329 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (5,true),
.cycle 1 25 true (0),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 9 4 true (3)
])
theorem kid02_part329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part329) = true := by rfl

def kid02_part330 : Audit := .cycle 0 11 true (0)
theorem kid02_part330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part330) = true := by rfl

def kid02_part331 : Audit := .cycle 1 10 true (1)
theorem kid02_part331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part331) = true := by rfl

def kid02_part332 : Audit := .cycle 2 9 true (1)
theorem kid02_part332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part332) = true := by rfl

def kid02_part333 : Audit := .cycle 1 13 true (1)
theorem kid02_part333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part333) = true := by rfl

def kid02_part334 : Audit := .cycle 10 1 true (4)
theorem kid02_part334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part334) = true := by rfl

def kid02_part335 : Audit := .cycle 9 2 true (3)
theorem kid02_part335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part335) = true := by rfl

def kid02_part311 : Audit := .split 10 (4,false) (byMove [(kid02_part312),(kid02_part313),(kid02_part314),(kid02_part315),(kid02_part316),(kid02_part317),(kid02_part318),(kid02_part319),(kid02_part320),(kid02_part321),(kid02_part322),(kid02_part323),(kid02_part324),(kid02_part325),(kid02_part326),(kid02_part327),(kid02_part328),(kid02_part329),(kid02_part330),(kid02_part331),(kid02_part332),(kid02_part333),(kid02_part334),(kid02_part335)])

theorem kid02_part311_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part311) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid02_part312),(kid02_part313),(kid02_part314),(kid02_part315),(kid02_part316),(kid02_part317),(kid02_part318),(kid02_part319),(kid02_part320),(kid02_part321),(kid02_part322),(kid02_part323),(kid02_part324),(kid02_part325),(kid02_part326),(kid02_part327),(kid02_part328),(kid02_part329),(kid02_part330),(kid02_part331),(kid02_part332),(kid02_part333),(kid02_part334),(kid02_part335)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part312_checked

  · exact kid02_part318_checked

  · exact kid02_part324_checked

  · exact kid02_part330_checked

  · exact kid02_part313_checked

  · exact kid02_part319_checked

  · exact kid02_part325_checked

  · exact kid02_part331_checked

  · exact kid02_part314_checked

  · exact kid02_part320_checked

  · exact kid02_part326_checked

  · exact kid02_part332_checked

  · exact kid02_part315_checked

  · exact kid02_part321_checked

  · exact kid02_part327_checked

  · exact kid02_part333_checked

  · exact kid02_part316_checked

  · exact kid02_part322_checked

  · exact kid02_part328_checked

  · exact kid02_part334_checked

  · exact kid02_part317_checked

  · exact kid02_part323_checked

  · exact kid02_part329_checked

  · exact kid02_part335_checked

def kid02_part336 : Audit := .cycle 9 1 true (3)
theorem kid02_part336_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part336) = true := by rfl

def kid02_part337 : Audit := .cycle 7 4 true (2)
theorem kid02_part337_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part337) = true := by rfl

def kid02_part338 : Audit := .cycle 8 3 true (2)
theorem kid02_part338_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part338) = true := by rfl

def kid02_part339 : Audit := .cycle 0 12 true (0)
theorem kid02_part339_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part339) = true := by rfl

def kid02_part340 : Audit := .cycle 17 1 false (1)
theorem kid02_part340_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part340) = true := by rfl

def kid02_part342 : Audit := .cycle 12 5 true (2)
theorem kid02_part342_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part342) = true := by rfl

def kid02_part343 : Audit := .cycle 0 14 true (0)
theorem kid02_part343_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part343) = true := by rfl

def kid02_part344 : Audit := .cycle 21 1 false (1)
theorem kid02_part344_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part344) = true := by rfl

def kid02_part345 : Audit := .cycle 7 13 true (0)
theorem kid02_part345_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part345) = true := by rfl

def kid02_part346 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 7 13 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.last 22 (5,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 6 true (2),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.cycle 4 17 true (0),
.cycle 11 2 true (0),
.last 15 (5,true)
])
theorem kid02_part346_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part346) = true := by rfl

def kid02_part347 : Audit := .split 12 (4,true) (byMove [
.last 18 (5,true),
.last 23 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (5,true),
.cycle 15 1 false (1),
.cycle 14 2 false (2),
.cycle 17 2 false (3),
.cycle 14 2 false (2),
.last 13 (5,true),
.cycle 16 2 false (0),
.last 15 (5,true),
.last 20 (5,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (5,true),
.cycle 15 2 false (1),
.last 16 (5,true),
.cycle 7 8 true (0),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid02_part347_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part347) = true := by rfl

def kid02_part348 : Audit := .cycle 1 11 true (1)
theorem kid02_part348_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part348) = true := by rfl

def kid02_part349 : Audit := .cycle 24 1 false (2)
theorem kid02_part349_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part349) = true := by rfl

def kid02_part350 : Audit := .cycle 8 3 true (2)
theorem kid02_part350_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part350) = true := by rfl

def kid02_part351 : Audit := .cycle 0 12 true (0)
theorem kid02_part351_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part351) = true := by rfl

def kid02_part352 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,true),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 14 (5,true)
])
theorem kid02_part352_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part352) = true := by rfl

def kid02_part353 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 4 true (2),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (8),
.cycle 1 24 true (0),
.cycle 9 4 true (2),
.cycle 9 3 true (2),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (2),
.last 13 (4,true)
])
theorem kid02_part353_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part353) = true := by rfl

def kid02_part354 : Audit := .cycle 17 5 false (1)
theorem kid02_part354_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part354) = true := by rfl

def kid02_part355 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (-1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 36, 128, 256, 8, 128, 36, 4096, 4096],[128, 36, 32, 1, 4096, 4, 128, 36, 32, 1, 4096, 4, 4096],6144⟩,
.cycle 0 27 true (0),
.last 32 (4,true),
.cycle 9 5 true (1),
.cycle 33 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 25 1 false (-1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 28 (4,true),
.last 15 (4,true)
])
theorem kid02_part355_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part355) = true := by rfl

def kid02_part356 : Audit := .cycle 1 13 true (1)
theorem kid02_part356_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part356) = true := by rfl

def kid02_part357 : Audit := .cycle 18 1 false (0)
theorem kid02_part357_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part357) = true := by rfl

def kid02_part358 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.last 14 (5,true),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
.last 13 (5,true),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 6 true (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.last 13 (5,true)
])
theorem kid02_part358_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part358) = true := by rfl

def kid02_part359 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.last 23 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.cycle 15 1 false (1),
.last 14 (5,true),
.cycle 17 2 false (3),
.cycle 16 2 false (4),
.last 13 (5,true),
.cycle 16 2 false (0),
.last 15 (5,true),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (5,true),
.cycle 15 2 false (1),
.last 14 (5,true),
.cycle 5 8 true (0),
.last 17 (5,true),
.last 13 (5,true)
])
theorem kid02_part359_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part359) = true := by rfl

def kid02_part360 : Audit := .cycle 1 11 true (1)
theorem kid02_part360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part360) = true := by rfl

def kid02_part361 : Audit := .cycle 7 4 true (2)
theorem kid02_part361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part361) = true := by rfl

def kid02_part362 : Audit := .cycle 8 3 true (2)
theorem kid02_part362_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part362) = true := by rfl

def kid02_part363 : Audit := .cycle 0 12 true (0)
theorem kid02_part363_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part363) = true := by rfl

def kid02_part364 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 13 1 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 15 3 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 14 (5,true)
])
theorem kid02_part364_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part364) = true := by rfl

def kid02_part365 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.last 13 (4,true)
])
theorem kid02_part365_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part365) = true := by rfl

def kid02_part341 : Audit := .split 10 (4,false) (byMove [(kid02_part342),(kid02_part343),(kid02_part344),(kid02_part345),(kid02_part346),(kid02_part347),(kid02_part348),(kid02_part349),(kid02_part350),(kid02_part351),(kid02_part352),(kid02_part353),(kid02_part354),(kid02_part355),(kid02_part356),(kid02_part357),(kid02_part358),(kid02_part359),(kid02_part360),(kid02_part361),(kid02_part362),(kid02_part363),(kid02_part364),(kid02_part365)])

theorem kid02_part341_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part341) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid02_part342),(kid02_part343),(kid02_part344),(kid02_part345),(kid02_part346),(kid02_part347),(kid02_part348),(kid02_part349),(kid02_part350),(kid02_part351),(kid02_part352),(kid02_part353),(kid02_part354),(kid02_part355),(kid02_part356),(kid02_part357),(kid02_part358),(kid02_part359),(kid02_part360),(kid02_part361),(kid02_part362),(kid02_part363),(kid02_part364),(kid02_part365)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part342_checked

  · exact kid02_part348_checked

  · exact kid02_part354_checked

  · exact kid02_part360_checked

  · exact kid02_part343_checked

  · exact kid02_part349_checked

  · exact kid02_part355_checked

  · exact kid02_part361_checked

  · exact kid02_part344_checked

  · exact kid02_part350_checked

  · exact kid02_part356_checked

  · exact kid02_part362_checked

  · exact kid02_part345_checked

  · exact kid02_part351_checked

  · exact kid02_part357_checked

  · exact kid02_part363_checked

  · exact kid02_part346_checked

  · exact kid02_part352_checked

  · exact kid02_part358_checked

  · exact kid02_part364_checked

  · exact kid02_part347_checked

  · exact kid02_part353_checked

  · exact kid02_part359_checked

  · exact kid02_part365_checked

def kid02_part366 : Audit := .split 12 (5,true) (byMove [
.cycle 14 27 true (0),
.cycle 9 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 26 (4,true),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 22 22 true (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 10 6 false (2),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 7 false (2),
.last 23 (4,true),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.last 15 (4,true),
.cycle 11 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.split 13 (4,true) (byMove [
.last 18 (4,false),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 16 1 false (4),
.cycle 17 1 false (1),
.last 27 (4,false),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 1 21 true (0),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 14 3 true (2)
]),
.cycle 16 1 false (4),
.cycle 16 1 false (0),
.cycle 59 1 false (-1),
.cycle 18 1 false (2),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 35 (4,true),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 24 1 false (4),
.cycle 18 1 false (2),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 17 1 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 7 false (2),
.cycle 16 1 false (0),
.last 27 (4,true),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 10 6 true (0),
.cycle 15 1 false (1),
.cycle 18 16 true (2),
.cycle 5 8 true (0),
.split 13 (4,true) (byMove [
.last 18 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 18 1 false (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 6 8 true (0),
.cycle 22 1 false (2),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 16 (4,false),
.last 21 (4,false),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 22 (4,false),
.cycle 18 1 false (2),
.last 15 (4,false),
.cycle 12 2 true (0),
.cycle 1 21 true (0),
.cycle 10 6 true (0),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 14 3 true (2)
]),
.cycle 14 3 true (2)
])
theorem kid02_part366_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part366) = true := by rfl

def kid02_part367 : Audit := .cycle 0 10 true (0)
theorem kid02_part367_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part367) = true := by rfl

def kid02_part368 : Audit := .cycle 1 9 true (1)
theorem kid02_part368_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part368) = true := by rfl

def kid02_part369 : Audit := .cycle 2 8 true (1)
theorem kid02_part369_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part369) = true := by rfl

def kid02_part370 : Audit := .cycle 1 12 true (1)
theorem kid02_part370_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part370) = true := by rfl

def kid02_part372 : Audit := .cycle 1 11 true (1)
theorem kid02_part372_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part372) = true := by rfl

def kid02_part373 : Audit := .split 21 (4,true) (byMove [
.cycle 1 22 true (0),
.cycle 24 1 false (2),
.cycle 27 1 false (3),
.cycle 0 23 true (0),
.cycle 36 1 false (2),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 56 1 false (6),
.cycle 12 10 true (0),
.cycle 32 1 false (4),
.cycle 1 22 true (0),
.cycle 36 1 false (4),
.cycle 29 1 false (3),
.cycle 24 1 false (2),
.last 23 (5,true),
.cycle 1 23 true (0),
.cycle 1 27 true (0),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 24 true (0),
.cycle 29 1 false (3),
.cycle 40 1 false (4)
])
theorem kid02_part373_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part373) = true := by rfl

def kid02_part374 : Audit := .cycle 8 3 true (2)
theorem kid02_part374_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part374) = true := by rfl

def kid02_part375 : Audit := .cycle 0 12 true (0)
theorem kid02_part375_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part375) = true := by rfl

def kid02_part376 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (5,true),
.cycle 0 23 true (0),
.cycle 17 1 false (1),
.cycle 9 3 true (3),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 1 21 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid02_part376_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part376) = true := by rfl

def kid02_part377 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 21 1 false (1),
.last 16 (4,true),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 9 4 true (3),
.cycle 9 3 true (3),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid02_part377_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part377) = true := by rfl

def kid02_part378 : Audit := .cycle 0 11 true (0)
theorem kid02_part378_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part378) = true := by rfl

def kid02_part379 : Audit := .cycle 1 10 true (1)
theorem kid02_part379_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part379) = true := by rfl

def kid02_part380 : Audit := .split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 36 1 false (2),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.cycle 39 1 false (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 16, 64],[2, 18, 32, 1, 16, 64, 64],64⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.cycle 36 1 false (2),
.last 22 (5,true),
.cycle 1 22 true (1),
.last 24 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 11 true (3),
.cycle 9 12 true (3)
])
theorem kid02_part380_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part380) = true := by rfl

def kid02_part381 : Audit := .cycle 3 8 true (1)
theorem kid02_part381_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part381) = true := by rfl

def kid02_part382 : Audit := .cycle 10 1 true (4)
theorem kid02_part382_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part382) = true := by rfl

def kid02_part383 : Audit := .cycle 9 2 true (3)
theorem kid02_part383_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part383) = true := by rfl

def kid02_part384 : Audit := .cycle 6 5 true (2)
theorem kid02_part384_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part384) = true := by rfl

def kid02_part385 : Audit := .split 21 (4,true) (byMove [
.cycle 1 37 true (0),
.cycle 24 1 false (2),
.cycle 30 1 false (4),
.cycle 30 1 false (4),
.cycle 14 16 true (0),
.last 22 (5,true),
.cycle 1 22 true (0),
.cycle 34 1 false (4),
.cycle 8 14 true (0),
.cycle 0 23 true (0),
.cycle 22 15 true (4),
.last 22 (5,true),
.cycle 34 1 false (4),
.cycle 24 1 false (2),
.last 23 (5,true),
.cycle 30 1 false (4),
.last 26 (5,true),
.last 22 (5,true),
.cycle 1 22 true (0),
.cycle 1 35 true (0),
.cycle 2 33 true (0),
.cycle 0 23 true (0),
.cycle 22 5 true (3),
.last 22 (5,true)
])
theorem kid02_part385_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part385) = true := by rfl

def kid02_part386 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 0 16 true (0),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 0 16 true (0),
.cycle 9 4 true (3),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 1 16 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3)
])
theorem kid02_part386_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part386) = true := by rfl

def kid02_part387 : Audit := .cycle 1 12 true (1)
theorem kid02_part387_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part387) = true := by rfl

def kid02_part388 : Audit := .split 11 (4,true) (byMove [
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.cycle 1 12 true (1),
.cycle 37 1 false (5),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 24 1 false (6),
.last 12 (5,true),
.cycle 6 11 true (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.last 12 (5,true)
])
theorem kid02_part388_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part388) = true := by rfl

def kid02_part389 : Audit := .split 11 (5,true) (byMove [
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 18 3 false (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3),
.last 16 (4,true),
.cycle 8 8 true (2),
.cycle 1 14 true (1),
.last 19 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3)
])
theorem kid02_part389_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part389) = true := by rfl

def kid02_part390 : Audit := .cycle 0 11 true (0)
theorem kid02_part390_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part390) = true := by rfl

def kid02_part391 : Audit := .cycle 1 10 true (1)
theorem kid02_part391_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part391) = true := by rfl

def kid02_part392 : Audit := .cycle 2 9 true (1)
theorem kid02_part392_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part392) = true := by rfl

def kid02_part393 : Audit := .cycle 1 13 true (1)
theorem kid02_part393_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part393) = true := by rfl

def kid02_part394 : Audit := .cycle 10 1 true (4)
theorem kid02_part394_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part394) = true := by rfl

def kid02_part395 : Audit := .cycle 9 2 true (3)
theorem kid02_part395_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part395) = true := by rfl

def kid02_part371 : Audit := .split 10 (4,false) (byMove [(kid02_part372),(kid02_part373),(kid02_part374),(kid02_part375),(kid02_part376),(kid02_part377),(kid02_part378),(kid02_part379),(kid02_part380),(kid02_part381),(kid02_part382),(kid02_part383),(kid02_part384),(kid02_part385),(kid02_part386),(kid02_part387),(kid02_part388),(kid02_part389),(kid02_part390),(kid02_part391),(kid02_part392),(kid02_part393),(kid02_part394),(kid02_part395)])

theorem kid02_part371_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part371) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid02_part372),(kid02_part373),(kid02_part374),(kid02_part375),(kid02_part376),(kid02_part377),(kid02_part378),(kid02_part379),(kid02_part380),(kid02_part381),(kid02_part382),(kid02_part383),(kid02_part384),(kid02_part385),(kid02_part386),(kid02_part387),(kid02_part388),(kid02_part389),(kid02_part390),(kid02_part391),(kid02_part392),(kid02_part393),(kid02_part394),(kid02_part395)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part372_checked

  · exact kid02_part378_checked

  · exact kid02_part384_checked

  · exact kid02_part390_checked

  · exact kid02_part373_checked

  · exact kid02_part379_checked

  · exact kid02_part385_checked

  · exact kid02_part391_checked

  · exact kid02_part374_checked

  · exact kid02_part380_checked

  · exact kid02_part386_checked

  · exact kid02_part392_checked

  · exact kid02_part375_checked

  · exact kid02_part381_checked

  · exact kid02_part387_checked

  · exact kid02_part393_checked

  · exact kid02_part376_checked

  · exact kid02_part382_checked

  · exact kid02_part388_checked

  · exact kid02_part394_checked

  · exact kid02_part377_checked

  · exact kid02_part383_checked

  · exact kid02_part389_checked

  · exact kid02_part395_checked

def kid02_part396 : Audit := .cycle 9 1 true (3)
theorem kid02_part396_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part396) = true := by rfl

def kid02_part300 : Audit := .split 9 (5,false) (byMove [(kid02_part301),(kid02_part302),(kid02_part303),(kid02_part304),(kid02_part305),(kid02_part306),(kid02_part307),(kid02_part308),(kid02_part309),(kid02_part310),(kid02_part311),(kid02_part336),(kid02_part337),(kid02_part338),(kid02_part339),(kid02_part340),(kid02_part341),(kid02_part366),(kid02_part367),(kid02_part368),(kid02_part369),(kid02_part370),(kid02_part371),(kid02_part396)])

theorem kid02_part300_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (kid02_part300) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid02_part301),(kid02_part302),(kid02_part303),(kid02_part304),(kid02_part305),(kid02_part306),(kid02_part307),(kid02_part308),(kid02_part309),(kid02_part310),(kid02_part311),(kid02_part336),(kid02_part337),(kid02_part338),(kid02_part339),(kid02_part340),(kid02_part341),(kid02_part366),(kid02_part367),(kid02_part368),(kid02_part369),(kid02_part370),(kid02_part371),(kid02_part396)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part301_checked

  · exact kid02_part307_checked

  · exact kid02_part337_checked

  · exact kid02_part367_checked

  · exact kid02_part302_checked

  · exact kid02_part308_checked

  · exact kid02_part338_checked

  · exact kid02_part368_checked

  · exact kid02_part303_checked

  · exact kid02_part309_checked

  · exact kid02_part339_checked

  · exact kid02_part369_checked

  · exact kid02_part304_checked

  · exact kid02_part310_checked

  · exact kid02_part340_checked

  · exact kid02_part370_checked

  · exact kid02_part305_checked

  · exact kid02_part311_checked

  · exact kid02_part341_checked

  · exact kid02_part371_checked

  · exact kid02_part306_checked

  · exact kid02_part336_checked

  · exact kid02_part366_checked

  · exact kid02_part396_checked

def kid02_part397 : Audit := .cycle 13 3 false (1)
theorem kid02_part397_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,0⟩)) (kid02_part397) = true := by rfl

def kid02_part398 : Audit := .cycle 17 1 false (-1)
theorem kid02_part398_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,1⟩)) (kid02_part398) = true := by rfl

def kid02_part399 : Audit := .cycle 0 11 true (0)
theorem kid02_part399_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,2⟩)) (kid02_part399) = true := by rfl

def kid02_part400 : Audit := .cycle 14 1 false (0)
theorem kid02_part400_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,3⟩)) (kid02_part400) = true := by rfl

def kid02_part402 : Audit := .split 13 (4,true) (byMove [
.cycle 10 4 true (0),
.cycle 16 1 false (0),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.cycle 0 16 false (3),
.split 14 (5,true) (byMove [
.cycle 0 19 true (-1),
.cycle 11 14 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 16 false (3),
.last 15 (5,false),
.cycle 11 9 false (2),
.last 18 (5,false),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 11 6 true (0),
.last 15 (5,false),
.cycle 11 9 false (2),
.last 18 (5,false),
.cycle 11 11 false (2),
.cycle 15 1 false (-1),
.cycle 11 6 false (2),
.last 15 (5,false),
.last 19 (5,false),
.cycle 11 4 true (0),
.cycle 0 17 true (0),
.cycle 11 11 false (2),
.cycle 9 6 true (0),
.last 15 (5,false)
]),
.cycle 1 14 true (0),
.cycle 11 13 false (2),
.cycle 8 6 true (0),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 11 13 false (2),
.cycle 1 17 true (0),
.cycle 1 16 true (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 11 14 true (1),
.cycle 1 32 true (-1),
.cycle 11 13 false (3),
.cycle 0 16 true (0),
.last 15 (5,false),
.cycle 11 14 false (2),
.cycle 11 4 true (1),
.cycle 0 17 true (0),
.cycle 11 11 false (2),
.cycle 9 6 true (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 11 13 true (1),
.cycle 1 17 true (0),
.cycle 1 16 true (0),
.last 15 (5,false)
]),
.cycle 11 8 false (2),
.cycle 16 1 false (0),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.cycle 11 6 false (2),
.split 14 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 1 20 true (-2),
.last 15 (5,false),
.cycle 11 9 false (2),
.cycle 17 1 false (1),
.cycle 11 7 false (2),
.cycle 1 16 true (0),
.last 16 (5,false),
.last 17 (5,false),
.cycle 11 9 false (2),
.last 18 (5,false),
.cycle 11 11 false (2),
.cycle 15 1 false (-1),
.cycle 11 6 false (2),
.last 15 (5,false),
.last 19 (5,false),
.cycle 11 8 false (2),
.last 17 (5,false),
.cycle 1 16 true (0),
.cycle 13 2 true (0),
.last 17 (5,false)
]),
.cycle 1 14 true (0),
.cycle 11 10 false (2),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 1 16 true (0),
.split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 11 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 0 16 true (0),
.last 15 (5,false),
.cycle 11 14 false (2),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 1 16 true (0),
.cycle 13 2 true (1),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 1 16 true (0),
.last 15 (5,false)
])
])
theorem kid02_part402_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part402) = true := by rfl

def kid02_part403 : Audit := .cycle 12 1 false (0)
theorem kid02_part403_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part403) = true := by rfl

def kid02_part404 : Audit := .cycle 13 1 false (-1)
theorem kid02_part404_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part404) = true := by rfl

def kid02_part405 : Audit := .cycle 15 1 false (-1)
theorem kid02_part405_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part405) = true := by rfl

def kid02_part406 : Audit := .split 10 (4,true) (byMove [
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 14 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 18 (5,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (5,true),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.last 18 (5,true),
.cycle 9 3 false (1),
.last 14 (5,true)
]),
.cycle 14 1 false (0),
.cycle 16 1 false (2),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 11 1 false (1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.last 12 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 12 (5,true)
]),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 16 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.last 29 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 18 (5,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (5,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 7 7 false (3),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 1 15 true (0),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 16 1 false (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.cycle 12 4 true (2),
.last 12 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 1 12 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 12 (5,true)
])
])
theorem kid02_part406_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part406) = true := by rfl

def kid02_part408 : Audit := .cycle 0 15 true (-1)
theorem kid02_part408_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part408) = true := by rfl

def kid02_part409 : Audit := .split 20 (5,false) (byMove [
.cycle 22 34 true (-2),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 17 5 false (1),
.last 23 (4,true),
.cycle 0 30 true (-2),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.cycle 10 12 true (-2),
.cycle 17 5 false (1),
.last 23 (4,true),
.cycle 17 7 false (1),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 24 (4,true),
.last 23 (4,true),
.cycle 0 30 true (-2),
.cycle 14 7 false (1),
.cycle 9 12 false (1),
.cycle 17 6 false (1)
])
theorem kid02_part409_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part409) = true := by rfl

def kid02_part410 : Audit := .cycle 12 1 false (0)
theorem kid02_part410_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part410) = true := by rfl

def kid02_part411 : Audit := .cycle 11 1 false (-1)
theorem kid02_part411_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part411) = true := by rfl

def kid02_part412 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 17 true (-2),
.last 25 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 18 1 true (0),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 33 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 27 (4,true),
.cycle 0 19 true (-2),
.cycle 9 4 false (1),
.last 17 (4,true)
])
theorem kid02_part412_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part412) = true := by rfl

def kid02_part413 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 true (-1),
.cycle 15 1 true (1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.last 17 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 0 30 true (-2),
.last 17 (4,true),
.cycle 9 3 false (1),
.cycle 18 1 true (-2)
])
theorem kid02_part413_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part413) = true := by rfl

def kid02_part414 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (2),
.last 18 (4,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 14 2 true (-1),
.cycle 0 18 true (-1),
.cycle 11 5 false (2),
.last 18 (4,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 9 7 false (2),
.cycle 0 18 true (-1)
])
theorem kid02_part414_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part414) = true := by rfl

def kid02_part415 : Audit := .split 13 (4,true) (byMove [
.cycle 15 4 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.cycle 1 14 true (0),
.cycle 16 1 false (2),
.last 16 (5,false),
.cycle 0 15 true (0),
.last 16 (5,false),
.last 24 (5,false),
.last 18 (5,false),
.cycle 11 3 false (2),
.cycle 1 16 true (0),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.cycle 1 14 true (0),
.last 17 (5,false),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 26 (5,false),
.last 24 (5,false)
])
theorem kid02_part415_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part415) = true := by rfl

def kid02_part416 : Audit := .cycle 0 13 true (0)
theorem kid02_part416_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part416) = true := by rfl

def kid02_part417 : Audit := .cycle 11 1 false (1)
theorem kid02_part417_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part417) = true := by rfl

def kid02_part418 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.cycle 11 5 false (2),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 11 2 true (0),
.cycle 16 1 true (2),
.cycle 11 5 false (1),
.last 15 (4,true),
.cycle 11 7 false (2),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 9 4 true (0),
.cycle 16 1 true (2)
])
theorem kid02_part418_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part418) = true := by rfl

def kid02_part419 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3),
.cycle 11 5 false (1),
.last 14 (4,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.last 18 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3)
])
theorem kid02_part419_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part419) = true := by rfl

def kid02_part420 : Audit := .split 15 (5,false) (byMove [
.last 23 (4,true),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 11 5 false (0),
.last 18 (4,true),
.last 21 (4,true),
.cycle 16 1 false (-2),
.cycle 14 2 true (-3),
.cycle 10 7 false (0),
.cycle 11 5 false (0),
.last 18 (4,true),
.cycle 11 7 false (0),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.last 18 (4,true),
.last 21 (4,true),
.cycle 12 7 false (0),
.cycle 9 7 false (1),
.last 21 (4,true)
])
theorem kid02_part420_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part420) = true := by rfl

def kid02_part421 : Audit := .split 13 (4,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.last 16 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.cycle 10 4 true (-1),
.last 18 (5,false),
.cycle 11 3 false (0),
.last 22 (5,false),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 11 22 true (-1),
.last 17 (5,false),
.cycle 12 2 true (-1),
.cycle 7 9 false (3),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1)
])
theorem kid02_part421_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part421) = true := by rfl

def kid02_part422 : Audit := .split 17 (5,false) (byMove [
.cycle 0 22 true (-2),
.cycle 14 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (2),
.last 20 (4,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 16 2 true (-1),
.cycle 0 22 true (-1),
.cycle 13 5 false (2),
.last 20 (4,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.last 20 (4,true),
.cycle 0 20 true (-1),
.cycle 14 7 false (2),
.cycle 9 9 false (2),
.last 21 (4,true)
])
theorem kid02_part422_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part422) = true := by rfl

def kid02_part423 : Audit := .cycle 11 1 false (-1)
theorem kid02_part423_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part423) = true := by rfl

def kid02_part424 : Audit := .split 12 (5,false) (byMove [
.cycle 14 26 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 5 false (0),
.last 15 (4,true),
.cycle 0 22 true (-2),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.cycle 11 5 false (-1),
.last 15 (4,true),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 22 true (-2),
.cycle 11 7 false (0),
.cycle 9 4 false (1),
.last 15 (4,true)
])
theorem kid02_part424_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part424) = true := by rfl

def kid02_part425 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 0 24 true (-2),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.last 17 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 18 (4,true),
.last 13 (4,true),
.cycle 7 7 false (3),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid02_part425_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part425) = true := by rfl

def kid02_part426 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.last 17 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.last 19 (5,false),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 18 (5,false),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.cycle 0 16 true (0)
])
theorem kid02_part426_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part426) = true := by rfl

def kid02_part427 : Audit := .split 13 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 16 1 false (0),
.last 16 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.cycle 10 4 true (0),
.cycle 1 14 true (0),
.last 23 (5,false),
.cycle 8 6 true (0),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 1 14 true (0),
.last 18 (5,false),
.cycle 16 1 false (0),
.last 16 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.cycle 1 14 true (0),
.last 20 (5,false),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 1 16 true (0),
.cycle 1 14 true (0)
])
theorem kid02_part427_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part427) = true := by rfl

def kid02_part428 : Audit := .cycle 0 13 true (0)
theorem kid02_part428_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part428) = true := by rfl

def kid02_part429 : Audit := .split 17 (5,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 14 5 false (2),
.last 20 (4,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 16 2 true (-1),
.cycle 1 22 true (-1),
.cycle 14 5 false (2),
.last 20 (4,true),
.cycle 14 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.last 20 (4,true),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 9 9 false (2),
.cycle 1 22 true (-1)
])
theorem kid02_part429_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part429) = true := by rfl

def kid02_part430 : Audit := .cycle 9 2 true (0)
theorem kid02_part430_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part430) = true := by rfl

def kid02_part431 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 18 1 false (-2),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 1 12 true (0),
.last 24 (4,true),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.cycle 12 7 false (0),
.cycle 18 1 false (-2),
.last 12 (4,true),
.cycle 13 3 true (1),
.cycle 1 12 true (0),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3)
])
theorem kid02_part431_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part431) = true := by rfl

def kid02_part407 : Audit := .split 10 (5,true) (byMove [(kid02_part408),(kid02_part409),(kid02_part410),(kid02_part411),(kid02_part412),(kid02_part413),(kid02_part414),(kid02_part415),(kid02_part416),(kid02_part417),(kid02_part418),(kid02_part419),(kid02_part420),(kid02_part421),(kid02_part422),(kid02_part423),(kid02_part424),(kid02_part425),(kid02_part426),(kid02_part427),(kid02_part428),(kid02_part429),(kid02_part430),(kid02_part431)])

theorem kid02_part407_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part407) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid02_part408),(kid02_part409),(kid02_part410),(kid02_part411),(kid02_part412),(kid02_part413),(kid02_part414),(kid02_part415),(kid02_part416),(kid02_part417),(kid02_part418),(kid02_part419),(kid02_part420),(kid02_part421),(kid02_part422),(kid02_part423),(kid02_part424),(kid02_part425),(kid02_part426),(kid02_part427),(kid02_part428),(kid02_part429),(kid02_part430),(kid02_part431)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part408_checked

  · exact kid02_part414_checked

  · exact kid02_part420_checked

  · exact kid02_part426_checked

  · exact kid02_part409_checked

  · exact kid02_part415_checked

  · exact kid02_part421_checked

  · exact kid02_part427_checked

  · exact kid02_part410_checked

  · exact kid02_part416_checked

  · exact kid02_part422_checked

  · exact kid02_part428_checked

  · exact kid02_part411_checked

  · exact kid02_part417_checked

  · exact kid02_part423_checked

  · exact kid02_part429_checked

  · exact kid02_part412_checked

  · exact kid02_part418_checked

  · exact kid02_part424_checked

  · exact kid02_part430_checked

  · exact kid02_part413_checked

  · exact kid02_part419_checked

  · exact kid02_part425_checked

  · exact kid02_part431_checked

def kid02_part432 : Audit := .cycle 1 10 true (1)
theorem kid02_part432_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part432) = true := by rfl

def kid02_part433 : Audit := .cycle 21 1 false (1)
theorem kid02_part433_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part433) = true := by rfl

def kid02_part434 : Audit := .cycle 8 2 true (1)
theorem kid02_part434_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part434) = true := by rfl

def kid02_part435 : Audit := .cycle 0 11 true (0)
theorem kid02_part435_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part435) = true := by rfl

def kid02_part436 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 11 1 true (1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 true (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 28 (5,true),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 7 6 true (1),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
]),
.cycle 14 5 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 12 4 true (-2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 30 (5,true),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 15 (5,true),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
])
theorem kid02_part436_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part436) = true := by rfl

def kid02_part438 : Audit := .cycle 0 11 true (0)
theorem kid02_part438_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part438) = true := by rfl

def kid02_part439 : Audit := .cycle 1 10 true (1)
theorem kid02_part439_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part439) = true := by rfl

def kid02_part440 : Audit := .cycle 21 1 false (1)
theorem kid02_part440_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part440) = true := by rfl

def kid02_part441 : Audit := .cycle 1 13 true (0)
theorem kid02_part441_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part441) = true := by rfl

def kid02_part442 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 11 2 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
])
theorem kid02_part442_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part442) = true := by rfl

def kid02_part443 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1)
])
theorem kid02_part443_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part443) = true := by rfl

def kid02_part444 : Audit := .cycle 0 11 true (0)
theorem kid02_part444_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part444) = true := by rfl

def kid02_part445 : Audit := .cycle 1 10 true (1)
theorem kid02_part445_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part445) = true := by rfl

def kid02_part446 : Audit := .cycle 1 24 true (0)
theorem kid02_part446_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part446) = true := by rfl

def kid02_part447 : Audit := .cycle 20 1 false (2)
theorem kid02_part447_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part447) = true := by rfl

def kid02_part448 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.cycle 26 1 false (4),
.cycle 11 2 true (3),
.cycle 18 1 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 28 (4,true),
.last 26 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 24 (4,true),
.cycle 9 4 true (1),
.last 17 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid02_part448_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part448) = true := by rfl

def kid02_part449 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (2),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (8),
.cycle 1 24 true (0),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid02_part449_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part449) = true := by rfl

def kid02_part450 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 15 5 false (1),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 17 5 false (1)
])
theorem kid02_part450_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part450) = true := by rfl

def kid02_part451 : Audit := .split 13 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 8 6 true (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 10 4 true (1),
.cycle 15 8 false (1),
.cycle 16 1 false (0),
.cycle 11 22 true (-2),
.cycle 23 1 false (-1),
.cycle 14 5 false (0),
.last 18 (5,false),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 25 1 false (-1)
])
theorem kid02_part451_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part451) = true := by rfl

def kid02_part452 : Audit := .cycle 0 13 true (0)
theorem kid02_part452_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part452) = true := by rfl

def kid02_part453 : Audit := .cycle 18 1 false (0)
theorem kid02_part453_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part453) = true := by rfl

def kid02_part454 : Audit := .cycle 9 2 true (1)
theorem kid02_part454_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part454) = true := by rfl

def kid02_part455 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 29 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid02_part455_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part455) = true := by rfl

def kid02_part456 : Audit := .cycle 0 11 true (0)
theorem kid02_part456_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part456) = true := by rfl

def kid02_part457 : Audit := .cycle 1 10 true (1)
theorem kid02_part457_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part457) = true := by rfl

def kid02_part458 : Audit := .cycle 2 9 true (1)
theorem kid02_part458_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part458) = true := by rfl

def kid02_part459 : Audit := .cycle 1 13 true (1)
theorem kid02_part459_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part459) = true := by rfl

def kid02_part460 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.cycle 9 13 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (1),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid02_part460_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part460) = true := by rfl

def kid02_part461 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 18 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid02_part461_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part461) = true := by rfl

def kid02_part437 : Audit := .split 10 (5,true) (byMove [(kid02_part438),(kid02_part439),(kid02_part440),(kid02_part441),(kid02_part442),(kid02_part443),(kid02_part444),(kid02_part445),(kid02_part446),(kid02_part447),(kid02_part448),(kid02_part449),(kid02_part450),(kid02_part451),(kid02_part452),(kid02_part453),(kid02_part454),(kid02_part455),(kid02_part456),(kid02_part457),(kid02_part458),(kid02_part459),(kid02_part460),(kid02_part461)])

theorem kid02_part437_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part437) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid02_part438),(kid02_part439),(kid02_part440),(kid02_part441),(kid02_part442),(kid02_part443),(kid02_part444),(kid02_part445),(kid02_part446),(kid02_part447),(kid02_part448),(kid02_part449),(kid02_part450),(kid02_part451),(kid02_part452),(kid02_part453),(kid02_part454),(kid02_part455),(kid02_part456),(kid02_part457),(kid02_part458),(kid02_part459),(kid02_part460),(kid02_part461)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part438_checked

  · exact kid02_part444_checked

  · exact kid02_part450_checked

  · exact kid02_part456_checked

  · exact kid02_part439_checked

  · exact kid02_part445_checked

  · exact kid02_part451_checked

  · exact kid02_part457_checked

  · exact kid02_part440_checked

  · exact kid02_part446_checked

  · exact kid02_part452_checked

  · exact kid02_part458_checked

  · exact kid02_part441_checked

  · exact kid02_part447_checked

  · exact kid02_part453_checked

  · exact kid02_part459_checked

  · exact kid02_part442_checked

  · exact kid02_part448_checked

  · exact kid02_part454_checked

  · exact kid02_part460_checked

  · exact kid02_part443_checked

  · exact kid02_part449_checked

  · exact kid02_part455_checked

  · exact kid02_part461_checked

def kid02_part462 : Audit := .cycle 11 4 false (1)
theorem kid02_part462_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part462) = true := by rfl

def kid02_part463 : Audit := .cycle 12 1 false (0)
theorem kid02_part463_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part463) = true := by rfl

def kid02_part464 : Audit := .split 23 (4,true) (byMove [
.cycle 20 4 true (0),
.cycle 26 1 false (0),
.cycle 16 8 true (-2),
.cycle 1 31 true (-2),
.cycle 21 8 true (-2),
.split 24 (5,true) (byMove [
.cycle 0 29 true (-2),
.cycle 13 16 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 21 8 true (-2),
.last 25 (5,false),
.cycle 1 31 true (-2),
.last 28 (5,false),
.cycle 0 27 true (-2),
.cycle 25 1 false (1),
.cycle 1 28 true (-2),
.last 25 (5,false),
.last 66 (5,false),
.last 28 (5,false),
.cycle 1 33 true (-2),
.cycle 25 1 false (-1),
.cycle 17 8 true (-2),
.last 25 (5,false),
.last 29 (5,false),
.cycle 21 4 true (0),
.cycle 0 27 true (-2),
.cycle 1 33 true (-2),
.cycle 9 16 true (-2),
.last 25 (5,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 1, 64, 64],96⟩,
.cycle 1 35 true (-2),
.cycle 8 16 true (-2),
.cycle 0 25 true (-2),
.cycle 0 28 true (-2),
.split 24 (5,true) (byMove [
.cycle 21 23 true (0),
.cycle 1 24 true (-2),
.cycle 1 35 true (-2),
.cycle 1 27 true (-2),
.cycle 1 36 true (-2),
.last 25 (5,false),
.cycle 0 25 true (-2),
.cycle 1 36 true (-2),
.cycle 1 46 true (-2),
.cycle 13 15 true (-2),
.cycle 0 28 true (-2),
.last 25 (5,false),
.cycle 1 36 true (-2),
.cycle 21 4 true (1),
.cycle 0 27 true (-2),
.cycle 1 33 true (-2),
.cycle 9 16 true (-2),
.last 25 (5,false),
.cycle 22 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 32, 2, 64],96⟩,
.cycle 1 35 true (-2),
.cycle 1 27 true (-2),
.last 44 (5,false),
.last 25 (5,false)
]),
.cycle 14 10 true (-2),
.cycle 26 1 false (0),
.cycle 10 14 true (-2),
.cycle 1 31 true (-2),
.cycle 11 14 true (-2),
.split 24 (5,true) (byMove [
.cycle 21 5 false (2),
.cycle 1 28 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 15 14 true (-2),
.last 25 (5,false),
.cycle 1 31 true (-2),
.cycle 27 1 false (1),
.cycle 1 35 true (-2),
.cycle 1 26 true (-2),
.last 26 (5,false),
.last 27 (5,false),
.cycle 15 11 false (2),
.last 28 (5,false),
.cycle 1 33 true (-2),
.cycle 25 1 false (-1),
.cycle 11 14 true (-2),
.last 25 (5,false),
.last 29 (5,false),
.cycle 15 10 true (-2),
.last 27 (5,false),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 1, 1073741824, 8192, 16384, 8, 128, 16384, 1073741824, 33554432, 67108864, 2097152, 128, 1073741824, 1073741824, 33554432, 67108864, 2097152, 16512, 262144, 1073741824, 33554432, 67108864, 134217728, 1327775872, 1327775872, 1073741824, 1073741824],[128, 16512, 128, 1, 1073741824, 512, 8192, 16384, 1073741824, 1, 1, 32768, 33554432, 1073741824, 128, 262144, 262144, 134217728, 33554432, 16512, 1107296256, 262144, 1073741824, 134217728, 33554432, 1327775872, 1327775872, 16777216, 1090519040, 134217728, 1073741824],2144286816⟩,
.cycle 23 2 true (0),
.last 27 (5,false)
]),
.cycle 20 20 true (0),
.cycle 1 32 true (-2),
.cycle 22 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 8, 64, 64],96⟩,
.cycle 23 5 true (1),
.split 24 (5,true) (byMove [
.cycle 20 23 true (0),
.cycle 1 30 true (-2),
.cycle 1 32 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 32, 15, 64],96⟩,
.last 26 (5,false),
.last 27 (5,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 32, 1, 64],96⟩,
.cycle 1 36 true (-2),
.cycle 0 51 true (-2),
.cycle 3 22 true (-2),
.cycle 0 28 true (-2),
.last 25 (5,false),
.cycle 1 36 true (-2),
.cycle 15 10 true (-2),
.cycle 10 18 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 32, 15, 64],96⟩,
.cycle 23 2 true (1),
.last 27 (5,false),
.cycle 22 18 true (1),
.cycle 21 20 true (1),
.cycle 22 17 true (0),
.cycle 19 31 true (-1),
.last 30 (5,false),
.last 25 (5,false)
])
])
theorem kid02_part464_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part464) = true := by rfl

def kid02_part465 : Audit := .cycle 15 1 false (-1)
theorem kid02_part465_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part465) = true := by rfl

def kid02_part466 : Audit := .split 10 (4,true) (byMove [
.cycle 12 4 true (-1),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 1 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 13 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 5 false (1),
.last 15 (5,true),
.cycle 1 14 true (-1),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 1 12 true (0),
.cycle 13 1 false (3),
.split 11 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 22 1 false (2),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false)
]),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 16 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 9 10 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 5 false (1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 5 7 false (3),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 1 15 true (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 1 12 true (0),
.cycle 11 3 true (1),
.split 11 (5,true) (byMove [
.cycle 1 17 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 1 12 true (0),
.cycle 1 15 true (0),
.cycle 2 13 true (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false)
])
])
theorem kid02_part466_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part466) = true := by rfl

def kid02_part468 : Audit := .split 14 (4,true) (byMove [
.cycle 12 4 true (-1),
.cycle 17 1 false (-1),
.last 17 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.cycle 1 20 true (-2),
.cycle 6 9 false (3),
.last 24 (5,false),
.cycle 8 7 false (2),
.cycle 1 16 true (-1),
.last 18 (5,false),
.cycle 12 21 true (0),
.last 19 (5,false),
.cycle 17 1 false (-1),
.last 17 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.cycle 10 5 false (1),
.cycle 12 19 true (0),
.last 21 (5,false),
.cycle 13 2 true (0),
.cycle 1 16 true (-1),
.cycle 15 7 true (1),
.cycle 12 21 true (0)
])
theorem kid02_part468_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part468) = true := by rfl

def kid02_part469 : Audit := .cycle 1 14 true (-1)
theorem kid02_part469_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part469) = true := by rfl

def kid02_part470 : Audit := .cycle 12 1 false (0)
theorem kid02_part470_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part470) = true := by rfl

def kid02_part471 : Audit := .cycle 11 1 false (-1)
theorem kid02_part471_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part471) = true := by rfl

def kid02_part472 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.last 23 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 11 4 false (-1),
.last 14 (4,true),
.cycle 7 8 false (3),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid02_part472_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part472) = true := by rfl

def kid02_part473 : Audit := .split 11 (5,false) (byMove [
.cycle 1 16 true (-2),
.last 28 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 13 5 false (1),
.last 14 (4,true),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 17 1 true (1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 15 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 1 14 true (-1),
.last 23 (4,true),
.cycle 9 3 false (1),
.cycle 25 1 true (-3)
])
theorem kid02_part473_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part473) = true := by rfl

def kid02_part474 : Audit := .split 15 (5,false) (byMove [
.last 19 (4,true),
.cycle 1 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (2),
.cycle 18 1 false (0),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.last 16 (4,true),
.cycle 1 17 true (-1),
.cycle 12 5 false (2),
.last 18 (4,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 19 (4,true),
.cycle 12 4 false (2),
.last 17 (4,true),
.cycle 1 17 true (-1),
.last 16 (4,true),
.cycle 1 17 true (-1)
])
theorem kid02_part474_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part474) = true := by rfl

def kid02_part475 : Audit := .cycle 13 1 false (1)
theorem kid02_part475_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part475) = true := by rfl

def kid02_part476 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 16 1 false (0),
.cycle 11 3 false (1),
.cycle 1 21 true (-1),
.last 14 (4,true),
.cycle 10 4 true (-1),
.cycle 11 5 false (1),
.last 16 (4,true),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.last 17 (4,true),
.cycle 11 4 false (1),
.last 15 (4,true),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 8 7 false (2)
])
theorem kid02_part476_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part476) = true := by rfl

def kid02_part477 : Audit := .cycle 1 12 true (0)
theorem kid02_part477_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part477) = true := by rfl

def kid02_part478 : Audit := .split 11 (4,true) (byMove [
.cycle 13 4 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.cycle 11 3 false (1),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (0),
.last 15 (5,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 14 (5,false)
])
theorem kid02_part478_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part478) = true := by rfl

def kid02_part479 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 27 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 2 false (3),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 26 1 false (4),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.last 16 (4,true),
.cycle 13 1 true (3),
.cycle 13 5 false (3),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 2 false (3),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 24 (4,true),
.cycle 1 16 true (0),
.cycle 11 4 true (1),
.cycle 13 1 true (3)
])
theorem kid02_part479_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part479) = true := by rfl

def kid02_part480 : Audit := .split 15 (5,false) (byMove [
.last 19 (4,true),
.last 22 (4,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 5 false (0),
.cycle 18 1 false (-2),
.cycle 13 3 false (-1),
.last 20 (4,true),
.last 16 (4,true),
.cycle 10 6 false (0),
.cycle 11 5 false (0),
.last 18 (4,true),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.cycle 12 4 false (0),
.last 17 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.cycle 12 6 false (0)
])
theorem kid02_part480_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part480) = true := by rfl

def kid02_part481 : Audit := .split 13 (4,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 16 1 false (0),
.last 16 (5,false),
.last 19 (5,false),
.last 18 (5,false),
.cycle 10 4 true (-1),
.last 18 (5,false),
.cycle 11 3 false (0),
.last 20 (5,false),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 11 26 true (-1),
.last 17 (5,false),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.cycle 27 1 false (-1),
.cycle 17 1 false (-1)
])
theorem kid02_part481_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part481) = true := by rfl

def kid02_part482 : Audit := .split 17 (5,false) (byMove [
.last 21 (4,true),
.cycle 1 21 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (2),
.cycle 20 1 false (0),
.cycle 15 3 false (1),
.cycle 1 19 true (-1),
.last 18 (4,true),
.cycle 1 21 true (-1),
.cycle 14 5 false (2),
.last 20 (4,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.cycle 14 4 false (2),
.last 19 (4,true),
.cycle 1 19 true (-1),
.last 18 (4,true),
.cycle 15 4 false (1)
])
theorem kid02_part482_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part482) = true := by rfl

def kid02_part483 : Audit := .cycle 11 1 false (-1)
theorem kid02_part483_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part483) = true := by rfl

def kid02_part484 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 5 false (0),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.last 23 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 11 5 false (-1),
.last 15 (4,true),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 11 4 false (-1),
.last 14 (4,true),
.cycle 5 8 false (3),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid02_part484_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part484) = true := by rfl

def kid02_part485 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 11 5 false (1),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.cycle 1 19 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 11 4 false (0),
.last 13 (4,true),
.cycle 5 7 false (3),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid02_part485_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part485) = true := by rfl

def kid02_part486 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.last 17 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.last 19 (5,false),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 18 (5,false),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.cycle 1 18 true (0),
.cycle 0 16 true (0)
])
theorem kid02_part486_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part486) = true := by rfl

def kid02_part487 : Audit := .split 14 (5,false) (byMove [
.last 18 (4,true),
.last 21 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 5 false (1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.last 19 (4,true),
.last 15 (4,true),
.cycle 10 5 false (1),
.cycle 11 5 false (1),
.last 17 (4,true),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 11 4 false (1),
.last 16 (4,true),
.last 19 (4,true),
.last 15 (4,true),
.last 18 (4,true)
])
theorem kid02_part487_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part487) = true := by rfl

def kid02_part488 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 1 14 true (0),
.last 16 (5,false),
.last 25 (5,false),
.last 17 (5,false),
.cycle 11 3 false (1),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 17 true (0),
.last 16 (5,false),
.cycle 11 2 true (0),
.cycle 1 14 true (0),
.cycle 13 5 true (1),
.cycle 2 15 true (0)
])
theorem kid02_part488_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part488) = true := by rfl

def kid02_part489 : Audit := .cycle 1 12 true (0)
theorem kid02_part489_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part489) = true := by rfl

def kid02_part490 : Audit := .split 11 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.cycle 9 4 true (0),
.cycle 1 12 true (0),
.last 21 (5,false),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.cycle 14 1 false (0),
.last 14 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 1 12 true (0),
.last 18 (5,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 16 (5,false)
])
theorem kid02_part490_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part490) = true := by rfl

def kid02_part491 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 2 36 true (0),
.cycle 8 19 true (0),
.cycle 3 11 true (0),
.last 16 (4,true),
.cycle 13 1 true (3),
.last 17 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.cycle 1 15 true (0),
.last 14 (4,true),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 11 4 true (1),
.cycle 13 1 true (3)
])
theorem kid02_part491_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part491) = true := by rfl

def kid02_part467 : Audit := .split 10 (5,true) (byMove [(kid02_part468),(kid02_part469),(kid02_part470),(kid02_part471),(kid02_part472),(kid02_part473),(kid02_part474),(kid02_part475),(kid02_part476),(kid02_part477),(kid02_part478),(kid02_part479),(kid02_part480),(kid02_part481),(kid02_part482),(kid02_part483),(kid02_part484),(kid02_part485),(kid02_part486),(kid02_part487),(kid02_part488),(kid02_part489),(kid02_part490),(kid02_part491)])

theorem kid02_part467_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part467) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid02_part468),(kid02_part469),(kid02_part470),(kid02_part471),(kid02_part472),(kid02_part473),(kid02_part474),(kid02_part475),(kid02_part476),(kid02_part477),(kid02_part478),(kid02_part479),(kid02_part480),(kid02_part481),(kid02_part482),(kid02_part483),(kid02_part484),(kid02_part485),(kid02_part486),(kid02_part487),(kid02_part488),(kid02_part489),(kid02_part490),(kid02_part491)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part468_checked

  · exact kid02_part474_checked

  · exact kid02_part480_checked

  · exact kid02_part486_checked

  · exact kid02_part469_checked

  · exact kid02_part475_checked

  · exact kid02_part481_checked

  · exact kid02_part487_checked

  · exact kid02_part470_checked

  · exact kid02_part476_checked

  · exact kid02_part482_checked

  · exact kid02_part488_checked

  · exact kid02_part471_checked

  · exact kid02_part477_checked

  · exact kid02_part483_checked

  · exact kid02_part489_checked

  · exact kid02_part472_checked

  · exact kid02_part478_checked

  · exact kid02_part484_checked

  · exact kid02_part490_checked

  · exact kid02_part473_checked

  · exact kid02_part479_checked

  · exact kid02_part485_checked

  · exact kid02_part491_checked

def kid02_part492 : Audit := .cycle 1 10 true (1)
theorem kid02_part492_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part492) = true := by rfl

def kid02_part493 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 22 true (-2),
.split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.cycle 11 4 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.last 15 (5,true),
.cycle 15 3 false (-1),
.cycle 11 4 false (1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.last 17 (5,true),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.cycle 9 5 false (2),
.last 15 (5,true)
]),
.cycle 1 13 true (0),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 1 14 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 1 14 true (0),
.last 14 (5,false),
.cycle 15 3 false (1),
.cycle 11 4 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 1 16 true (0),
.cycle 1 14 true (0),
.last 14 (5,false)
]),
.cycle 14 3 false (0),
.cycle 11 3 false (1),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.split 13 (5,false) (byMove [
.last 18 (5,true),
.cycle 1 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.cycle 16 1 false (0),
.cycle 14 3 false (0),
.cycle 1 15 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 15 3 false (-1),
.cycle 11 4 false (1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.cycle 14 3 false (0),
.cycle 11 3 false (1),
.cycle 1 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 1 13 true (0),
.cycle 13 3 false (1),
.cycle 11 2 true (0),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.split 13 (5,true) (byMove [
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 14 3 false (0),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 1 14 true (0),
.last 14 (5,false),
.cycle 15 3 false (1),
.cycle 16 1 false (0),
.cycle 14 3 false (0),
.cycle 1 15 true (0),
.cycle 12 2 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 1 14 true (0),
.last 14 (5,false)
])
])
theorem kid02_part493_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part493) = true := by rfl

def kid02_part494 : Audit := .split 11 (4,true) (byMove [
.cycle 10 4 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 36 true (-2),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 24 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 16 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 16 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.cycle 10 4 true (0),
.cycle 0 15 true (0),
.last 21 (5,false),
.cycle 9 4 true (0),
.last 13 (5,false)
]),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 2 12 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 2 12 true (1),
.last 13 (5,false),
.cycle 15 7 false (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 13 (5,false)
]),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 10 18 true (-2),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 16 true (-1),
.last 13 (5,false),
.last 19 (5,false),
.cycle 15 1 false (1),
.last 17 (5,false),
.cycle 1 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 16 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.cycle 1 14 true (0),
.cycle 11 2 true (0),
.last 15 (5,false)
]),
.cycle 1 12 true (1),
.cycle 13 5 false (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 21 1 false (-1),
.cycle 13 5 false (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.last 13 (5,false),
.cycle 15 7 false (1),
.cycle 21 1 false (-1),
.cycle 13 5 false (1),
.cycle 1 14 true (1),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 13 (5,false)
])
])
theorem kid02_part494_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part494) = true := by rfl

def kid02_part495 : Audit := .cycle 0 11 true (0)
theorem kid02_part495_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part495) = true := by rfl

def kid02_part496 : Audit := .split 10 (4,true) (byMove [
.cycle 1 11 true (1),
.cycle 17 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 13 1 true (-1),
.split 11 (5,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.last 12 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 3 8 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (5,true),
.cycle 0 23 true (0),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
]),
.cycle 16 5 false (0),
.cycle 17 1 false (-1),
.cycle 17 3 false (1),
.cycle 1 12 true (1),
.cycle 11 3 false (1),
.split 11 (5,true) (byMove [
.cycle 13 5 false (2),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 13 (5,false),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 1 41 true (-2),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 13 (5,false),
.cycle 1 12 true (1),
.last 15 (5,false),
.last 17 (5,false),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 16 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
])
theorem kid02_part496_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part496) = true := by rfl

def kid02_part498 : Audit := .cycle 1 11 true (1)
theorem kid02_part498_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part498) = true := by rfl

def kid02_part499 : Audit := .cycle 17 1 false (-1)
theorem kid02_part499_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part499) = true := by rfl

def kid02_part500 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 13 true (0),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 1 13 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 13 3 false (1)
])
theorem kid02_part500_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part500) = true := by rfl

def kid02_part501 : Audit := .cycle 0 12 true (0)
theorem kid02_part501_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part501) = true := by rfl

def kid02_part502 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.cycle 12 3 false (0),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid02_part502_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part502) = true := by rfl

def kid02_part503 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (4,true),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 11 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 2 true (-1),
.cycle 13 1 true (-1),
.cycle 11 7 false (1),
.last 16 (4,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 11 4 false (1),
.cycle 13 1 false (-1),
.cycle 10 15 false (3),
.cycle 1 13 false (3),
.cycle 11 11 false (1),
.cycle 1 16 true (-1),
.cycle 13 2 true (-1),
.cycle 13 1 true (-1)
])
theorem kid02_part503_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part503) = true := by rfl

def kid02_part504 : Audit := .cycle 0 11 true (0)
theorem kid02_part504_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part504) = true := by rfl

def kid02_part505 : Audit := .cycle 1 10 true (1)
theorem kid02_part505_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part505) = true := by rfl

def kid02_part506 : Audit := .cycle 0 23 true (0)
theorem kid02_part506_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part506) = true := by rfl

def kid02_part507 : Audit := .cycle 3 8 true (1)
theorem kid02_part507_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part507) = true := by rfl

def kid02_part508 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 5 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (1),
.cycle 9 14 true (1),
.last 16 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid02_part508_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part508) = true := by rfl

def kid02_part509 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 36, 2048, 4, 8192, 16384, 8, 128, 131072, 4, 8192, 16384, 8, 128, 131072, 4, 262144],[128, 36, 32, 1, 262144, 32, 8192, 4, 262144, 1, 262144, 32, 8192, 262144, 262144, 1, 262144, 32, 262144],262144⟩,
.cycle 0 23 true (0),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.cycle 25 1 false (5),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid02_part509_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part509) = true := by rfl

def kid02_part510 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 17 5 false (1),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 15 5 false (1)
])
theorem kid02_part510_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part510) = true := by rfl

def kid02_part511 : Audit := .cycle 17 1 false (-1)
theorem kid02_part511_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part511) = true := by rfl

def kid02_part512 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 3 false (1),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 1 14 true (0),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 1 17 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 1 14 true (0),
.last 16 (5,false),
.cycle 13 3 false (1)
])
theorem kid02_part512_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part512) = true := by rfl

def kid02_part513 : Audit := .cycle 1 12 true (1)
theorem kid02_part513_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part513) = true := by rfl

def kid02_part514 : Audit := .split 11 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 14 (5,false),
.last 16 (5,false),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 11 18 true (-2),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 1 12 true (1),
.cycle 14 5 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 10 2 true (1)
])
theorem kid02_part514_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part514) = true := by rfl

def kid02_part515 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (4,true),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 16 1 false (0),
.cycle 11 5 false (1),
.cycle 1 23 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 11 7 false (1),
.last 16 (4,true),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 11 4 false (1),
.cycle 13 1 false (-1),
.last 17 (4,true),
.cycle 11 6 false (1),
.last 15 (4,true),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid02_part515_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part515) = true := by rfl

def kid02_part516 : Audit := .cycle 0 11 true (0)
theorem kid02_part516_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part516) = true := by rfl

def kid02_part517 : Audit := .cycle 1 10 true (1)
theorem kid02_part517_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part517) = true := by rfl

def kid02_part518 : Audit := .cycle 2 9 true (1)
theorem kid02_part518_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part518) = true := by rfl

def kid02_part519 : Audit := .cycle 1 13 true (1)
theorem kid02_part519_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part519) = true := by rfl

def kid02_part520 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid02_part520_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part520) = true := by rfl

def kid02_part521 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 15 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid02_part521_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part521) = true := by rfl

def kid02_part497 : Audit := .split 10 (5,true) (byMove [(kid02_part498),(kid02_part499),(kid02_part500),(kid02_part501),(kid02_part502),(kid02_part503),(kid02_part504),(kid02_part505),(kid02_part506),(kid02_part507),(kid02_part508),(kid02_part509),(kid02_part510),(kid02_part511),(kid02_part512),(kid02_part513),(kid02_part514),(kid02_part515),(kid02_part516),(kid02_part517),(kid02_part518),(kid02_part519),(kid02_part520),(kid02_part521)])

theorem kid02_part497_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part497) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid02_part498),(kid02_part499),(kid02_part500),(kid02_part501),(kid02_part502),(kid02_part503),(kid02_part504),(kid02_part505),(kid02_part506),(kid02_part507),(kid02_part508),(kid02_part509),(kid02_part510),(kid02_part511),(kid02_part512),(kid02_part513),(kid02_part514),(kid02_part515),(kid02_part516),(kid02_part517),(kid02_part518),(kid02_part519),(kid02_part520),(kid02_part521)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part498_checked

  · exact kid02_part504_checked

  · exact kid02_part510_checked

  · exact kid02_part516_checked

  · exact kid02_part499_checked

  · exact kid02_part505_checked

  · exact kid02_part511_checked

  · exact kid02_part517_checked

  · exact kid02_part500_checked

  · exact kid02_part506_checked

  · exact kid02_part512_checked

  · exact kid02_part518_checked

  · exact kid02_part501_checked

  · exact kid02_part507_checked

  · exact kid02_part513_checked

  · exact kid02_part519_checked

  · exact kid02_part502_checked

  · exact kid02_part508_checked

  · exact kid02_part514_checked

  · exact kid02_part520_checked

  · exact kid02_part503_checked

  · exact kid02_part509_checked

  · exact kid02_part515_checked

  · exact kid02_part521_checked

def kid02_part401 : Audit := .split 9 (4,false) (byMove [(kid02_part402),(kid02_part403),(kid02_part404),(kid02_part405),(kid02_part406),(kid02_part407),(kid02_part432),(kid02_part433),(kid02_part434),(kid02_part435),(kid02_part436),(kid02_part437),(kid02_part462),(kid02_part463),(kid02_part464),(kid02_part465),(kid02_part466),(kid02_part467),(kid02_part492),(kid02_part493),(kid02_part494),(kid02_part495),(kid02_part496),(kid02_part497)])

theorem kid02_part401_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (kid02_part401) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid02_part402),(kid02_part403),(kid02_part404),(kid02_part405),(kid02_part406),(kid02_part407),(kid02_part432),(kid02_part433),(kid02_part434),(kid02_part435),(kid02_part436),(kid02_part437),(kid02_part462),(kid02_part463),(kid02_part464),(kid02_part465),(kid02_part466),(kid02_part467),(kid02_part492),(kid02_part493),(kid02_part494),(kid02_part495),(kid02_part496),(kid02_part497)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part402_checked

  · exact kid02_part432_checked

  · exact kid02_part462_checked

  · exact kid02_part492_checked

  · exact kid02_part403_checked

  · exact kid02_part433_checked

  · exact kid02_part463_checked

  · exact kid02_part493_checked

  · exact kid02_part404_checked

  · exact kid02_part434_checked

  · exact kid02_part464_checked

  · exact kid02_part494_checked

  · exact kid02_part405_checked

  · exact kid02_part435_checked

  · exact kid02_part465_checked

  · exact kid02_part495_checked

  · exact kid02_part406_checked

  · exact kid02_part436_checked

  · exact kid02_part466_checked

  · exact kid02_part496_checked

  · exact kid02_part407_checked

  · exact kid02_part437_checked

  · exact kid02_part467_checked

  · exact kid02_part497_checked

def kid02_part523 : Audit := .split 13 (5,true) (byMove [
.cycle 10 4 true (0),
.cycle 16 1 false (0),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.split 14 (4,true) (byMove [
.cycle 0 19 true (-1),
.cycle 11 14 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 0 16 false (3),
.cycle 11 9 false (2),
.last 18 (4,false),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 11 6 true (0),
.cycle 11 9 false (2),
.last 18 (4,false),
.cycle 11 11 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 11 6 false (2),
.last 19 (4,false),
.cycle 11 4 true (0),
.cycle 0 17 true (0),
.cycle 11 11 false (2),
.last 15 (4,false),
.cycle 9 6 true (0)
]),
.cycle 0 16 false (3),
.cycle 1 14 true (0),
.cycle 11 13 false (2),
.cycle 8 6 true (0),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 11 13 false (2),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 11 14 true (1),
.cycle 1 32 true (-1),
.cycle 11 13 false (3),
.last 15 (4,false),
.cycle 0 16 true (0),
.cycle 11 14 false (2),
.cycle 11 4 true (1),
.cycle 0 17 true (0),
.cycle 11 11 false (2),
.last 15 (4,false),
.cycle 9 6 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 11 13 true (1),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 1 16 true (0)
]),
.cycle 0 16 true (0),
.cycle 11 8 false (2),
.cycle 16 1 false (0),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 1 20 true (-2),
.cycle 11 9 false (2),
.cycle 17 1 false (1),
.cycle 11 7 false (2),
.cycle 1 16 true (0),
.last 17 (4,false),
.last 16 (4,false),
.cycle 11 9 false (2),
.last 18 (4,false),
.cycle 11 11 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 11 6 false (2),
.last 19 (4,false),
.cycle 11 8 false (2),
.last 17 (4,false),
.cycle 1 16 true (0),
.last 17 (4,false),
.cycle 13 2 true (0)
]),
.cycle 11 6 false (2),
.cycle 1 14 true (0),
.cycle 11 10 false (2),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 0 16 true (0),
.last 17 (4,false),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 11 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.cycle 0 16 true (0),
.cycle 11 14 false (2),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 1 16 true (0),
.last 17 (4,false),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 1 16 true (0)
]),
.cycle 1 16 true (0)
])
theorem kid02_part523_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part523) = true := by rfl

def kid02_part524 : Audit := .cycle 12 1 false (0)
theorem kid02_part524_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part524) = true := by rfl

def kid02_part525 : Audit := .cycle 13 1 false (-1)
theorem kid02_part525_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part525) = true := by rfl

def kid02_part526 : Audit := .cycle 15 1 false (-1)
theorem kid02_part526_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part526) = true := by rfl

def kid02_part528 : Audit := .cycle 0 15 true (-1)
theorem kid02_part528_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part528) = true := by rfl

def kid02_part529 : Audit := .split 20 (4,false) (byMove [
.cycle 22 34 true (-2),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 17 5 false (1),
.last 23 (5,true),
.cycle 0 30 true (-2),
.cycle 21 1 false (-1),
.cycle 10 12 true (-2),
.cycle 19 2 true (-2),
.cycle 17 5 false (1),
.last 23 (5,true),
.cycle 17 7 false (1),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 30 true (-2),
.cycle 14 7 false (1),
.cycle 17 6 false (1),
.cycle 9 12 false (1)
])
theorem kid02_part529_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part529) = true := by rfl

def kid02_part530 : Audit := .cycle 12 1 false (0)
theorem kid02_part530_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part530) = true := by rfl

def kid02_part531 : Audit := .cycle 11 1 false (-1)
theorem kid02_part531_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part531) = true := by rfl

def kid02_part532 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 true (1),
.cycle 11 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 17 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 0 30 true (-2),
.last 17 (5,true),
.cycle 18 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid02_part532_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part532) = true := by rfl

def kid02_part533 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.last 25 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 18 1 true (0),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 33 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 27 (5,true),
.cycle 0 19 true (-2),
.last 17 (5,true),
.cycle 9 4 false (1)
])
theorem kid02_part533_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part533) = true := by rfl

def kid02_part534 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.last 18 (5,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 0 18 true (-1),
.cycle 14 2 true (-1),
.cycle 11 5 false (2),
.last 18 (5,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 0 18 true (-1),
.cycle 9 7 false (2)
])
theorem kid02_part534_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part534) = true := by rfl

def kid02_part535 : Audit := .split 13 (5,true) (byMove [
.cycle 15 4 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.cycle 1 14 true (0),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 0 15 true (0),
.last 24 (4,false),
.last 16 (4,false),
.last 18 (4,false),
.cycle 11 3 false (2),
.cycle 1 16 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.cycle 1 14 true (0),
.last 17 (4,false),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 24 (4,false),
.last 26 (4,false)
])
theorem kid02_part535_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part535) = true := by rfl

def kid02_part536 : Audit := .cycle 0 13 true (0)
theorem kid02_part536_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part536) = true := by rfl

def kid02_part537 : Audit := .cycle 11 1 false (1)
theorem kid02_part537_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part537) = true := by rfl

def kid02_part538 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true),
.cycle 11 5 false (1),
.last 14 (5,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 1 12 true (0),
.last 18 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true)
])
theorem kid02_part538_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part538) = true := by rfl

def kid02_part539 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 5 false (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 1 true (2),
.cycle 11 2 true (0),
.cycle 11 5 false (1),
.last 15 (5,true),
.cycle 11 7 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 16 1 true (2),
.cycle 9 4 true (0)
])
theorem kid02_part539_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part539) = true := by rfl

def kid02_part540 : Audit := .split 15 (4,false) (byMove [
.last 23 (5,true),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 11 5 false (0),
.last 18 (5,true),
.last 21 (5,true),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 14 2 true (-3),
.cycle 11 5 false (0),
.last 18 (5,true),
.cycle 11 7 false (0),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.last 18 (5,true),
.last 21 (5,true),
.cycle 12 7 false (0),
.last 21 (5,true),
.cycle 9 7 false (1)
])
theorem kid02_part540_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part540) = true := by rfl

def kid02_part541 : Audit := .split 13 (5,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 19 (4,false),
.cycle 10 4 true (-1),
.last 16 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.last 22 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 11 22 true (-1),
.last 17 (4,false),
.cycle 12 2 true (-1),
.cycle 7 9 false (3),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1)
])
theorem kid02_part541_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part541) = true := by rfl

def kid02_part542 : Audit := .split 17 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 14 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.last 20 (5,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 0 22 true (-1),
.cycle 16 2 true (-1),
.cycle 13 5 false (2),
.last 20 (5,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (-1),
.cycle 14 7 false (2),
.last 21 (5,true),
.cycle 9 9 false (2)
])
theorem kid02_part542_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part542) = true := by rfl

def kid02_part543 : Audit := .cycle 11 1 false (-1)
theorem kid02_part543_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part543) = true := by rfl

def kid02_part544 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 14 1 false (0),
.cycle 0 24 true (-2),
.cycle 18 1 false (0),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 17 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 18 (5,true),
.last 13 (5,true),
.cycle 7 7 false (3),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid02_part544_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part544) = true := by rfl

def kid02_part545 : Audit := .split 12 (4,false) (byMove [
.cycle 14 26 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.last 15 (5,true),
.cycle 0 22 true (-2),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 22 true (-2),
.cycle 11 7 false (0),
.last 15 (5,true),
.cycle 9 4 false (1)
])
theorem kid02_part545_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part545) = true := by rfl

def kid02_part546 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.last 19 (4,false),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 18 (4,false),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 0 18 true (0)
])
theorem kid02_part546_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part546) = true := by rfl

def kid02_part547 : Audit := .split 13 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 19 (4,false),
.cycle 10 4 true (0),
.last 16 (4,false),
.cycle 1 14 true (0),
.last 23 (4,false),
.cycle 8 6 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.last 16 (4,false),
.last 18 (4,false),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 19 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.cycle 1 14 true (0),
.last 20 (4,false),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 1 16 true (0)
])
theorem kid02_part547_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part547) = true := by rfl

def kid02_part548 : Audit := .cycle 0 13 true (0)
theorem kid02_part548_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part548) = true := by rfl

def kid02_part549 : Audit := .split 17 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 14 5 false (2),
.last 20 (5,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 1 22 true (-1),
.cycle 16 2 true (-1),
.cycle 14 5 false (2),
.last 20 (5,true),
.cycle 14 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 1 22 true (-1),
.cycle 9 9 false (2)
])
theorem kid02_part549_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part549) = true := by rfl

def kid02_part550 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 18 1 false (-2),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 1 12 true (0),
.last 24 (5,true),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true),
.cycle 13 5 false (1),
.cycle 14 1 false (0),
.cycle 12 7 false (0),
.cycle 18 1 false (-2),
.cycle 13 3 true (1),
.last 12 (5,true),
.cycle 1 12 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true)
])
theorem kid02_part550_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part550) = true := by rfl

def kid02_part551 : Audit := .cycle 9 2 true (0)
theorem kid02_part551_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part551) = true := by rfl

def kid02_part527 : Audit := .split 10 (4,true) (byMove [(kid02_part528),(kid02_part529),(kid02_part530),(kid02_part531),(kid02_part532),(kid02_part533),(kid02_part534),(kid02_part535),(kid02_part536),(kid02_part537),(kid02_part538),(kid02_part539),(kid02_part540),(kid02_part541),(kid02_part542),(kid02_part543),(kid02_part544),(kid02_part545),(kid02_part546),(kid02_part547),(kid02_part548),(kid02_part549),(kid02_part550),(kid02_part551)])

theorem kid02_part527_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part527) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid02_part528),(kid02_part529),(kid02_part530),(kid02_part531),(kid02_part532),(kid02_part533),(kid02_part534),(kid02_part535),(kid02_part536),(kid02_part537),(kid02_part538),(kid02_part539),(kid02_part540),(kid02_part541),(kid02_part542),(kid02_part543),(kid02_part544),(kid02_part545),(kid02_part546),(kid02_part547),(kid02_part548),(kid02_part549),(kid02_part550),(kid02_part551)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part528_checked

  · exact kid02_part534_checked

  · exact kid02_part540_checked

  · exact kid02_part546_checked

  · exact kid02_part529_checked

  · exact kid02_part535_checked

  · exact kid02_part541_checked

  · exact kid02_part547_checked

  · exact kid02_part530_checked

  · exact kid02_part536_checked

  · exact kid02_part542_checked

  · exact kid02_part548_checked

  · exact kid02_part531_checked

  · exact kid02_part537_checked

  · exact kid02_part543_checked

  · exact kid02_part549_checked

  · exact kid02_part532_checked

  · exact kid02_part538_checked

  · exact kid02_part544_checked

  · exact kid02_part550_checked

  · exact kid02_part533_checked

  · exact kid02_part539_checked

  · exact kid02_part545_checked

  · exact kid02_part551_checked

def kid02_part552 : Audit := .split 10 (5,true) (byMove [
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 12 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 18 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.last 18 (4,true),
.last 14 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (2),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (4),
.cycle 15 1 false (-1),
.last 15 (4,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
]),
.cycle 11 1 false (1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 16 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.last 29 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 18 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 7 7 false (3),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 1 15 true (0),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 16 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 4 true (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 12 true (0),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
]),
.cycle 9 2 true (0)
])
theorem kid02_part552_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part552) = true := by rfl

def kid02_part553 : Audit := .cycle 1 10 true (1)
theorem kid02_part553_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part553) = true := by rfl

def kid02_part554 : Audit := .cycle 21 1 false (1)
theorem kid02_part554_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part554) = true := by rfl

def kid02_part555 : Audit := .cycle 8 2 true (1)
theorem kid02_part555_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part555) = true := by rfl

def kid02_part556 : Audit := .cycle 0 11 true (0)
theorem kid02_part556_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part556) = true := by rfl

def kid02_part558 : Audit := .cycle 0 11 true (0)
theorem kid02_part558_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part558) = true := by rfl

def kid02_part559 : Audit := .cycle 1 10 true (1)
theorem kid02_part559_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part559) = true := by rfl

def kid02_part560 : Audit := .cycle 21 1 false (1)
theorem kid02_part560_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part560) = true := by rfl

def kid02_part561 : Audit := .cycle 1 13 true (0)
theorem kid02_part561_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part561) = true := by rfl

def kid02_part562 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1)
])
theorem kid02_part562_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part562) = true := by rfl

def kid02_part563 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
])
theorem kid02_part563_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part563) = true := by rfl

def kid02_part564 : Audit := .cycle 0 11 true (0)
theorem kid02_part564_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part564) = true := by rfl

def kid02_part565 : Audit := .cycle 1 10 true (1)
theorem kid02_part565_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part565) = true := by rfl

def kid02_part566 : Audit := .cycle 1 24 true (0)
theorem kid02_part566_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part566) = true := by rfl

def kid02_part567 : Audit := .cycle 20 1 false (2)
theorem kid02_part567_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part567) = true := by rfl

def kid02_part568 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (8),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid02_part568_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part568) = true := by rfl

def kid02_part569 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (5,true),
.cycle 26 1 false (4),
.cycle 18 1 false (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 28 (5,true),
.last 26 (5,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 7 7 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.last 24 (5,true),
.last 17 (5,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid02_part569_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part569) = true := by rfl

def kid02_part570 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.last 17 (4,false),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.cycle 17 5 false (1),
.last 17 (4,false)
])
theorem kid02_part570_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part570) = true := by rfl

def kid02_part571 : Audit := .split 13 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.last 18 (4,false),
.last 16 (4,false),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 8 6 true (1),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.last 16 (4,false),
.cycle 15 8 false (1),
.cycle 16 1 false (0),
.cycle 11 22 true (-2),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 14 5 false (0),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 25 1 false (-1),
.last 16 (4,false)
])
theorem kid02_part571_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part571) = true := by rfl

def kid02_part572 : Audit := .cycle 0 13 true (0)
theorem kid02_part572_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part572) = true := by rfl

def kid02_part573 : Audit := .cycle 18 1 false (0)
theorem kid02_part573_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part573) = true := by rfl

def kid02_part574 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 29 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid02_part574_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part574) = true := by rfl

def kid02_part575 : Audit := .cycle 9 2 true (1)
theorem kid02_part575_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part575) = true := by rfl

def kid02_part576 : Audit := .cycle 0 11 true (0)
theorem kid02_part576_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part576) = true := by rfl

def kid02_part577 : Audit := .cycle 1 10 true (1)
theorem kid02_part577_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part577) = true := by rfl

def kid02_part578 : Audit := .cycle 2 9 true (1)
theorem kid02_part578_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part578) = true := by rfl

def kid02_part579 : Audit := .cycle 1 13 true (1)
theorem kid02_part579_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part579) = true := by rfl

def kid02_part580 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 18 (5,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid02_part580_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part580) = true := by rfl

def kid02_part581 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (5,true),
.cycle 9 13 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid02_part581_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part581) = true := by rfl

def kid02_part557 : Audit := .split 10 (4,true) (byMove [(kid02_part558),(kid02_part559),(kid02_part560),(kid02_part561),(kid02_part562),(kid02_part563),(kid02_part564),(kid02_part565),(kid02_part566),(kid02_part567),(kid02_part568),(kid02_part569),(kid02_part570),(kid02_part571),(kid02_part572),(kid02_part573),(kid02_part574),(kid02_part575),(kid02_part576),(kid02_part577),(kid02_part578),(kid02_part579),(kid02_part580),(kid02_part581)])

theorem kid02_part557_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part557) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid02_part558),(kid02_part559),(kid02_part560),(kid02_part561),(kid02_part562),(kid02_part563),(kid02_part564),(kid02_part565),(kid02_part566),(kid02_part567),(kid02_part568),(kid02_part569),(kid02_part570),(kid02_part571),(kid02_part572),(kid02_part573),(kid02_part574),(kid02_part575),(kid02_part576),(kid02_part577),(kid02_part578),(kid02_part579),(kid02_part580),(kid02_part581)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part558_checked

  · exact kid02_part564_checked

  · exact kid02_part570_checked

  · exact kid02_part576_checked

  · exact kid02_part559_checked

  · exact kid02_part565_checked

  · exact kid02_part571_checked

  · exact kid02_part577_checked

  · exact kid02_part560_checked

  · exact kid02_part566_checked

  · exact kid02_part572_checked

  · exact kid02_part578_checked

  · exact kid02_part561_checked

  · exact kid02_part567_checked

  · exact kid02_part573_checked

  · exact kid02_part579_checked

  · exact kid02_part562_checked

  · exact kid02_part568_checked

  · exact kid02_part574_checked

  · exact kid02_part580_checked

  · exact kid02_part563_checked

  · exact kid02_part569_checked

  · exact kid02_part575_checked

  · exact kid02_part581_checked

def kid02_part582 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 12 1 true (2),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 12 1 true (2)
]),
.cycle 11 1 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 28 (4,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.cycle 7 6 true (1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3),
.cycle 14 5 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 4 true (-2),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 30 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 15 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid02_part582_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part582) = true := by rfl

def kid02_part583 : Audit := .cycle 11 4 false (1)
theorem kid02_part583_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part583) = true := by rfl

def kid02_part584 : Audit := .cycle 12 1 false (0)
theorem kid02_part584_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part584) = true := by rfl

def kid02_part585 : Audit := .split 23 (5,true) (byMove [
.cycle 20 4 true (0),
.cycle 26 1 false (0),
.cycle 16 8 true (-2),
.cycle 1 31 true (-2),
.split 24 (4,true) (byMove [
.cycle 0 29 true (-2),
.cycle 13 16 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 21 8 true (-2),
.cycle 1 31 true (-2),
.last 28 (4,false),
.cycle 0 27 true (-2),
.cycle 25 1 false (1),
.last 25 (4,false),
.cycle 1 28 true (-2),
.last 66 (4,false),
.last 28 (4,false),
.cycle 1 33 true (-2),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 17 8 true (-2),
.last 29 (4,false),
.cycle 21 4 true (0),
.cycle 0 27 true (-2),
.cycle 1 33 true (-2),
.last 25 (4,false),
.cycle 9 16 true (-2)
]),
.cycle 21 8 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 1, 64],80⟩,
.cycle 1 35 true (-2),
.cycle 8 16 true (-2),
.cycle 0 25 true (-2),
.split 24 (4,true) (byMove [
.cycle 21 23 true (0),
.cycle 1 24 true (-2),
.cycle 1 35 true (-2),
.cycle 1 27 true (-2),
.last 25 (4,false),
.cycle 1 36 true (-2),
.cycle 0 25 true (-2),
.cycle 1 36 true (-2),
.cycle 1 46 true (-2),
.cycle 13 15 true (-2),
.last 25 (4,false),
.cycle 0 28 true (-2),
.cycle 1 36 true (-2),
.cycle 21 4 true (1),
.cycle 0 27 true (-2),
.cycle 1 33 true (-2),
.last 25 (4,false),
.cycle 9 16 true (-2),
.cycle 22 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 2, 16, 64],80⟩,
.cycle 1 35 true (-2),
.cycle 1 27 true (-2),
.last 25 (4,false),
.last 44 (4,false)
]),
.cycle 0 28 true (-2),
.cycle 14 10 true (-2),
.cycle 26 1 false (0),
.cycle 10 14 true (-2),
.cycle 1 31 true (-2),
.split 24 (4,true) (byMove [
.cycle 21 5 false (2),
.cycle 1 28 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 15 14 true (-2),
.cycle 1 31 true (-2),
.cycle 27 1 false (1),
.cycle 1 35 true (-2),
.cycle 1 26 true (-2),
.last 27 (4,false),
.last 26 (4,false),
.cycle 15 11 false (2),
.last 28 (4,false),
.cycle 1 33 true (-2),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 11 14 true (-2),
.last 29 (4,false),
.cycle 15 10 true (-2),
.last 27 (4,false),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 1073741824, 1, 8192, 16384, 8, 128, 1073741824, 16384, 33554432, 67108864, 2097152, 128, 1073741824, 1073741824, 33554432, 67108864, 2097152, 16512, 1073741824, 262144, 33554432, 67108864, 134217728, 1327775872, 1073741824, 1327775872, 1073741824],[128, 16512, 128, 1, 512, 1073741824, 8192, 16384, 1073741824, 1, 32768, 1, 33554432, 1073741824, 128, 262144, 134217728, 262144, 33554432, 16512, 1107296256, 262144, 134217728, 1073741824, 33554432, 1327775872, 1327775872, 16777216, 134217728, 1090519040, 1073741824],2144285776⟩,
.last 27 (4,false),
.cycle 23 2 true (0)
]),
.cycle 11 14 true (-2),
.cycle 20 20 true (0),
.cycle 1 32 true (-2),
.cycle 22 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 8, 64],80⟩,
.split 24 (4,true) (byMove [
.cycle 20 23 true (0),
.cycle 1 30 true (-2),
.cycle 1 32 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 15, 16, 64],80⟩,
.last 27 (4,false),
.last 26 (4,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 1, 16, 64],80⟩,
.cycle 1 36 true (-2),
.cycle 0 51 true (-2),
.cycle 3 22 true (-2),
.last 25 (4,false),
.cycle 0 28 true (-2),
.cycle 1 36 true (-2),
.cycle 15 10 true (-2),
.cycle 10 18 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 15, 16, 64],80⟩,
.last 27 (4,false),
.cycle 23 2 true (1),
.cycle 22 18 true (1),
.cycle 21 20 true (1),
.cycle 22 17 true (0),
.cycle 19 31 true (-1),
.last 25 (4,false),
.last 30 (4,false)
]),
.cycle 23 5 true (1)
])
theorem kid02_part585_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part585) = true := by rfl

def kid02_part586 : Audit := .cycle 15 1 false (-1)
theorem kid02_part586_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part586) = true := by rfl

def kid02_part588 : Audit := .split 14 (5,true) (byMove [
.cycle 12 4 true (-1),
.cycle 17 1 false (-1),
.last 17 (4,false),
.last 20 (4,false),
.cycle 1 20 true (-2),
.last 17 (4,false),
.cycle 6 9 false (3),
.last 24 (4,false),
.cycle 8 7 false (2),
.cycle 1 16 true (-1),
.cycle 12 21 true (0),
.last 18 (4,false),
.last 19 (4,false),
.cycle 17 1 false (-1),
.last 17 (4,false),
.last 20 (4,false),
.cycle 10 5 false (1),
.last 17 (4,false),
.cycle 12 19 true (0),
.last 21 (4,false),
.cycle 13 2 true (0),
.cycle 1 16 true (-1),
.cycle 12 21 true (0),
.cycle 15 7 true (1)
])
theorem kid02_part588_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part588) = true := by rfl

def kid02_part589 : Audit := .cycle 1 14 true (-1)
theorem kid02_part589_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part589) = true := by rfl

def kid02_part590 : Audit := .cycle 12 1 false (0)
theorem kid02_part590_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part590) = true := by rfl

def kid02_part591 : Audit := .cycle 11 1 false (-1)
theorem kid02_part591_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part591) = true := by rfl

def kid02_part592 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (-2),
.last 28 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 13 5 false (1),
.last 14 (5,true),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 17 1 true (1),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 15 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (-1),
.last 23 (5,true),
.cycle 25 1 true (-3),
.cycle 9 3 false (1)
])
theorem kid02_part592_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part592) = true := by rfl

def kid02_part593 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.last 23 (5,true),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 11 4 false (-1),
.last 14 (5,true),
.cycle 7 8 false (3),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid02_part593_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part593) = true := by rfl

def kid02_part594 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.cycle 1 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.cycle 18 1 false (0),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 1 17 true (-1),
.last 16 (5,true),
.cycle 12 5 false (2),
.last 18 (5,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 19 (5,true),
.cycle 12 4 false (2),
.last 17 (5,true),
.cycle 1 17 true (-1),
.cycle 1 17 true (-1),
.last 16 (5,true)
])
theorem kid02_part594_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part594) = true := by rfl

def kid02_part595 : Audit := .cycle 13 1 false (1)
theorem kid02_part595_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part595) = true := by rfl

def kid02_part596 : Audit := .split 13 (4,false) (byMove [
.last 17 (5,true),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 5 false (1),
.cycle 16 1 false (0),
.cycle 11 3 false (1),
.cycle 1 21 true (-1),
.cycle 10 4 true (-1),
.last 14 (5,true),
.cycle 11 5 false (1),
.last 16 (5,true),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.last 17 (5,true),
.cycle 11 4 false (1),
.last 15 (5,true),
.cycle 5 9 false (3),
.cycle 8 7 false (2),
.last 14 (5,true)
])
theorem kid02_part596_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part596) = true := by rfl

def kid02_part597 : Audit := .cycle 1 12 true (0)
theorem kid02_part597_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part597) = true := by rfl

def kid02_part598 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 27 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.cycle 26 1 false (4),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.last 16 (5,true),
.cycle 13 5 false (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 24 (5,true),
.cycle 1 16 true (0),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid02_part598_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part598) = true := by rfl

def kid02_part599 : Audit := .split 11 (5,true) (byMove [
.cycle 13 4 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 14 (4,false),
.last 16 (4,false),
.cycle 11 3 false (1),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (0),
.last 15 (4,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.last 14 (4,false),
.cycle 12 3 true (2)
])
theorem kid02_part599_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part599) = true := by rfl

def kid02_part600 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.last 22 (5,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 5 false (0),
.cycle 18 1 false (-2),
.cycle 13 3 false (-1),
.last 20 (5,true),
.cycle 10 6 false (0),
.last 16 (5,true),
.cycle 11 5 false (0),
.last 18 (5,true),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.cycle 12 4 false (0),
.last 17 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.last 16 (5,true)
])
theorem kid02_part600_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part600) = true := by rfl

def kid02_part601 : Audit := .split 13 (5,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 19 (4,false),
.cycle 10 4 true (-1),
.last 18 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.last 20 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 11 26 true (-1),
.last 17 (4,false),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.cycle 17 1 false (-1),
.cycle 27 1 false (-1)
])
theorem kid02_part601_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part601) = true := by rfl

def kid02_part602 : Audit := .split 17 (4,false) (byMove [
.last 21 (5,true),
.cycle 1 21 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.cycle 20 1 false (0),
.cycle 15 3 false (1),
.cycle 1 19 true (-1),
.cycle 1 21 true (-1),
.last 18 (5,true),
.cycle 14 5 false (2),
.last 20 (5,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 21 (5,true),
.cycle 14 4 false (2),
.last 19 (5,true),
.cycle 1 19 true (-1),
.cycle 15 4 false (1),
.last 18 (5,true)
])
theorem kid02_part602_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part602) = true := by rfl

def kid02_part603 : Audit := .cycle 11 1 false (-1)
theorem kid02_part603_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part603) = true := by rfl

def kid02_part604 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 5 false (1),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.cycle 1 19 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 11 4 false (0),
.last 13 (5,true),
.cycle 5 7 false (3),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid02_part604_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part604) = true := by rfl

def kid02_part605 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 23 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.cycle 15 1 false (-1),
.cycle 11 3 false (-1),
.last 23 (5,true),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 11 4 false (-1),
.last 14 (5,true),
.cycle 5 8 false (3),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid02_part605_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part605) = true := by rfl

def kid02_part606 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.last 19 (4,false),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 18 (4,false),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 1 18 true (0)
])
theorem kid02_part606_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part606) = true := by rfl

def kid02_part607 : Audit := .split 14 (4,false) (byMove [
.last 18 (5,true),
.last 21 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 5 false (1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.last 19 (5,true),
.cycle 10 5 false (1),
.last 15 (5,true),
.cycle 11 5 false (1),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 18 (5,true),
.cycle 11 4 false (1),
.last 16 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.last 15 (5,true)
])
theorem kid02_part607_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part607) = true := by rfl

def kid02_part608 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 1 14 true (0),
.last 25 (4,false),
.last 16 (4,false),
.last 17 (4,false),
.cycle 11 3 false (1),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 17 true (0),
.last 16 (4,false),
.cycle 11 2 true (0),
.cycle 1 14 true (0),
.cycle 2 15 true (0),
.cycle 13 5 true (1)
])
theorem kid02_part608_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part608) = true := by rfl

def kid02_part609 : Audit := .cycle 1 12 true (0)
theorem kid02_part609_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part609) = true := by rfl

def kid02_part610 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 2 36 true (0),
.cycle 8 19 true (0),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.last 16 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 11 3 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid02_part610_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part610) = true := by rfl

def kid02_part611 : Audit := .split 11 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 17 (4,false),
.cycle 9 4 true (0),
.last 14 (4,false),
.cycle 1 12 true (0),
.last 21 (4,false),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.last 16 (4,false),
.last 14 (4,false),
.last 16 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 17 (4,false),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 1 12 true (0),
.last 18 (4,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.last 16 (4,false),
.cycle 12 3 true (2)
])
theorem kid02_part611_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part611) = true := by rfl

def kid02_part587 : Audit := .split 10 (4,true) (byMove [(kid02_part588),(kid02_part589),(kid02_part590),(kid02_part591),(kid02_part592),(kid02_part593),(kid02_part594),(kid02_part595),(kid02_part596),(kid02_part597),(kid02_part598),(kid02_part599),(kid02_part600),(kid02_part601),(kid02_part602),(kid02_part603),(kid02_part604),(kid02_part605),(kid02_part606),(kid02_part607),(kid02_part608),(kid02_part609),(kid02_part610),(kid02_part611)])

theorem kid02_part587_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part587) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid02_part588),(kid02_part589),(kid02_part590),(kid02_part591),(kid02_part592),(kid02_part593),(kid02_part594),(kid02_part595),(kid02_part596),(kid02_part597),(kid02_part598),(kid02_part599),(kid02_part600),(kid02_part601),(kid02_part602),(kid02_part603),(kid02_part604),(kid02_part605),(kid02_part606),(kid02_part607),(kid02_part608),(kid02_part609),(kid02_part610),(kid02_part611)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part588_checked

  · exact kid02_part594_checked

  · exact kid02_part600_checked

  · exact kid02_part606_checked

  · exact kid02_part589_checked

  · exact kid02_part595_checked

  · exact kid02_part601_checked

  · exact kid02_part607_checked

  · exact kid02_part590_checked

  · exact kid02_part596_checked

  · exact kid02_part602_checked

  · exact kid02_part608_checked

  · exact kid02_part591_checked

  · exact kid02_part597_checked

  · exact kid02_part603_checked

  · exact kid02_part609_checked

  · exact kid02_part592_checked

  · exact kid02_part598_checked

  · exact kid02_part604_checked

  · exact kid02_part610_checked

  · exact kid02_part593_checked

  · exact kid02_part599_checked

  · exact kid02_part605_checked

  · exact kid02_part611_checked

def kid02_part612 : Audit := .split 10 (5,true) (byMove [
.cycle 12 4 true (-1),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 1 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 10 5 false (1),
.last 15 (4,true),
.cycle 1 14 true (-1),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 1 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 1 12 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 22 1 false (2),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false)
]),
.cycle 13 1 false (3),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 16 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 9 10 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 10 5 false (1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 5 7 false (3),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 1 15 true (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 1 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 17 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 8 4 true (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (4,false),
.cycle 10 2 true (0),
.cycle 1 12 true (0),
.cycle 1 15 true (0),
.cycle 2 13 true (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false)
]),
.cycle 11 3 true (1)
])
theorem kid02_part612_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part612) = true := by rfl

def kid02_part613 : Audit := .cycle 1 10 true (1)
theorem kid02_part613_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part613) = true := by rfl

def kid02_part614 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 18 true (-2),
.cycle 15 3 false (1),
.cycle 11 4 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 15 (4,true),
.cycle 14 3 false (1),
.cycle 15 3 false (-1),
.cycle 11 4 false (1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 10 5 false (2),
.last 17 (4,true),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 9 5 false (2)
]),
.cycle 0 22 true (-2),
.cycle 1 13 true (0),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.last 14 (4,false),
.cycle 1 14 true (0),
.cycle 15 3 false (1),
.cycle 11 4 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 1 16 true (0),
.last 14 (4,false),
.cycle 1 14 true (0)
]),
.cycle 1 14 true (0),
.cycle 14 3 false (0),
.cycle 11 3 false (1),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 18 (4,true),
.cycle 1 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 15 3 false (1),
.cycle 16 1 false (0),
.cycle 14 3 false (0),
.cycle 1 15 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 15 3 false (-1),
.cycle 11 4 false (1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 10 5 false (2),
.cycle 14 3 false (0),
.cycle 11 3 false (1),
.cycle 1 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 3 false (0),
.cycle 1 13 true (0),
.cycle 13 3 false (1),
.cycle 11 2 true (0),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.cycle 16 1 false (0),
.cycle 14 3 false (0),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.last 14 (4,false),
.cycle 1 14 true (0),
.cycle 15 3 false (1),
.cycle 16 1 false (0),
.cycle 14 3 false (0),
.cycle 1 15 true (0),
.last 15 (4,false),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.last 14 (4,false),
.cycle 1 14 true (0)
]),
.cycle 1 14 true (0)
])
theorem kid02_part614_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part614) = true := by rfl

def kid02_part615 : Audit := .split 11 (5,true) (byMove [
.cycle 10 4 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 24 (4,false),
.last 19 (4,false),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 16 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 16 (4,false),
.last 17 (4,false),
.cycle 10 4 true (0),
.cycle 0 15 true (0),
.last 21 (4,false),
.last 13 (4,false),
.cycle 9 4 true (0)
]),
.cycle 0 36 true (-2),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 2 12 true (1),
.cycle 15 7 false (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 2 12 true (1)
]),
.cycle 2 12 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 10 18 true (-2),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 10 5 false (2),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 1 16 true (-1),
.last 19 (4,false),
.cycle 15 1 false (1),
.last 17 (4,false),
.cycle 1 14 true (0),
.last 15 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 16 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 16 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.cycle 1 14 true (0),
.last 15 (4,false),
.cycle 11 2 true (0)
]),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.cycle 13 5 false (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 21 1 false (-1),
.cycle 13 5 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 2 12 true (1),
.cycle 15 7 false (1),
.cycle 21 1 false (-1),
.cycle 13 5 false (1),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 2 12 true (1)
]),
.cycle 2 12 true (1)
])
theorem kid02_part615_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part615) = true := by rfl

def kid02_part616 : Audit := .cycle 0 11 true (0)
theorem kid02_part616_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part616) = true := by rfl

def kid02_part618 : Audit := .cycle 1 11 true (1)
theorem kid02_part618_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part618) = true := by rfl

def kid02_part619 : Audit := .cycle 17 1 false (-1)
theorem kid02_part619_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part619) = true := by rfl

def kid02_part620 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 13 true (0),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 1 13 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.last 15 (4,false)
])
theorem kid02_part620_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part620) = true := by rfl

def kid02_part621 : Audit := .cycle 0 12 true (0)
theorem kid02_part621_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part621) = true := by rfl

def kid02_part622 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 0 14 true (-1),
.cycle 11 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 13 2 true (-1),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.cycle 10 15 false (3),
.cycle 1 13 false (3),
.cycle 11 11 false (1),
.cycle 1 16 true (-1),
.cycle 13 1 true (-1),
.cycle 13 2 true (-1)
])
theorem kid02_part622_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part622) = true := by rfl

def kid02_part623 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid02_part623_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part623) = true := by rfl

def kid02_part624 : Audit := .cycle 0 11 true (0)
theorem kid02_part624_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part624) = true := by rfl

def kid02_part625 : Audit := .cycle 1 10 true (1)
theorem kid02_part625_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part625) = true := by rfl

def kid02_part626 : Audit := .cycle 0 23 true (0)
theorem kid02_part626_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part626) = true := by rfl

def kid02_part627 : Audit := .cycle 3 8 true (1)
theorem kid02_part627_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part627) = true := by rfl

def kid02_part628 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 17 1 false (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 20, 4, 1024, 8192, 16384, 8, 128, 4, 65536, 8192, 16384, 8, 128, 4, 65536, 262144],[128, 20, 16, 1, 16, 262144, 8192, 4, 262144, 1, 16, 262144, 8192, 262144, 262144, 1, 16, 262144, 262144],262144⟩,
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 25 1 false (5),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid02_part628_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part628) = true := by rfl

def kid02_part629 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 5 true (1),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (1),
.cycle 9 14 true (1),
.last 16 (5,true),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid02_part629_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part629) = true := by rfl

def kid02_part630 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 17 5 false (1),
.last 17 (4,false),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.last 17 (4,false)
])
theorem kid02_part630_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part630) = true := by rfl

def kid02_part631 : Audit := .cycle 17 1 false (-1)
theorem kid02_part631_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part631) = true := by rfl

def kid02_part632 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 15 3 false (1),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 1 14 true (0),
.cycle 1 16 true (0),
.last 16 (4,false),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 1 17 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 1 14 true (0),
.cycle 13 3 false (1),
.last 16 (4,false)
])
theorem kid02_part632_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part632) = true := by rfl

def kid02_part633 : Audit := .cycle 1 12 true (1)
theorem kid02_part633_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part633) = true := by rfl

def kid02_part634 : Audit := .split 13 (4,false) (byMove [
.last 17 (5,true),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 11 7 false (1),
.cycle 16 1 false (0),
.cycle 11 5 false (1),
.cycle 1 23 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.last 17 (5,true),
.cycle 11 6 false (1),
.last 15 (5,true),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.last 14 (5,true)
])
theorem kid02_part634_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part634) = true := by rfl

def kid02_part635 : Audit := .split 11 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 16 (4,false),
.last 14 (4,false),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.last 14 (4,false),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 11 18 true (-2),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 12 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 14 (4,false)
])
theorem kid02_part635_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part635) = true := by rfl

def kid02_part636 : Audit := .cycle 0 11 true (0)
theorem kid02_part636_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part636) = true := by rfl

def kid02_part637 : Audit := .cycle 1 10 true (1)
theorem kid02_part637_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part637) = true := by rfl

def kid02_part638 : Audit := .cycle 2 9 true (1)
theorem kid02_part638_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part638) = true := by rfl

def kid02_part639 : Audit := .cycle 1 13 true (1)
theorem kid02_part639_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part639) = true := by rfl

def kid02_part640 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 15 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid02_part640_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part640) = true := by rfl

def kid02_part641 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.last 16 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid02_part641_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part641) = true := by rfl

def kid02_part617 : Audit := .split 10 (4,true) (byMove [(kid02_part618),(kid02_part619),(kid02_part620),(kid02_part621),(kid02_part622),(kid02_part623),(kid02_part624),(kid02_part625),(kid02_part626),(kid02_part627),(kid02_part628),(kid02_part629),(kid02_part630),(kid02_part631),(kid02_part632),(kid02_part633),(kid02_part634),(kid02_part635),(kid02_part636),(kid02_part637),(kid02_part638),(kid02_part639),(kid02_part640),(kid02_part641)])

theorem kid02_part617_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part617) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid02_part618),(kid02_part619),(kid02_part620),(kid02_part621),(kid02_part622),(kid02_part623),(kid02_part624),(kid02_part625),(kid02_part626),(kid02_part627),(kid02_part628),(kid02_part629),(kid02_part630),(kid02_part631),(kid02_part632),(kid02_part633),(kid02_part634),(kid02_part635),(kid02_part636),(kid02_part637),(kid02_part638),(kid02_part639),(kid02_part640),(kid02_part641)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part618_checked

  · exact kid02_part624_checked

  · exact kid02_part630_checked

  · exact kid02_part636_checked

  · exact kid02_part619_checked

  · exact kid02_part625_checked

  · exact kid02_part631_checked

  · exact kid02_part637_checked

  · exact kid02_part620_checked

  · exact kid02_part626_checked

  · exact kid02_part632_checked

  · exact kid02_part638_checked

  · exact kid02_part621_checked

  · exact kid02_part627_checked

  · exact kid02_part633_checked

  · exact kid02_part639_checked

  · exact kid02_part622_checked

  · exact kid02_part628_checked

  · exact kid02_part634_checked

  · exact kid02_part640_checked

  · exact kid02_part623_checked

  · exact kid02_part629_checked

  · exact kid02_part635_checked

  · exact kid02_part641_checked

def kid02_part642 : Audit := .split 10 (5,true) (byMove [
.cycle 1 11 true (1),
.cycle 17 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 12 1 true (2),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 0 26 true (-2),
.cycle 1 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (2)
]),
.cycle 13 1 true (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 3 8 true (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (4,true),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3),
.cycle 16 5 false (0),
.cycle 17 1 false (-1),
.cycle 17 3 false (1),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 13 5 false (2),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 13 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.cycle 1 41 true (-2),
.cycle 19 1 false (-1),
.last 13 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.last 15 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 10 2 true (1)
]),
.cycle 11 3 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid02_part642_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part642) = true := by rfl

def kid02_part522 : Audit := .split 9 (5,false) (byMove [(kid02_part523),(kid02_part524),(kid02_part525),(kid02_part526),(kid02_part527),(kid02_part552),(kid02_part553),(kid02_part554),(kid02_part555),(kid02_part556),(kid02_part557),(kid02_part582),(kid02_part583),(kid02_part584),(kid02_part585),(kid02_part586),(kid02_part587),(kid02_part612),(kid02_part613),(kid02_part614),(kid02_part615),(kid02_part616),(kid02_part617),(kid02_part642)])

theorem kid02_part522_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (kid02_part522) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid02_part523),(kid02_part524),(kid02_part525),(kid02_part526),(kid02_part527),(kid02_part552),(kid02_part553),(kid02_part554),(kid02_part555),(kid02_part556),(kid02_part557),(kid02_part582),(kid02_part583),(kid02_part584),(kid02_part585),(kid02_part586),(kid02_part587),(kid02_part612),(kid02_part613),(kid02_part614),(kid02_part615),(kid02_part616),(kid02_part617),(kid02_part642)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part523_checked

  · exact kid02_part553_checked

  · exact kid02_part583_checked

  · exact kid02_part613_checked

  · exact kid02_part524_checked

  · exact kid02_part554_checked

  · exact kid02_part584_checked

  · exact kid02_part614_checked

  · exact kid02_part525_checked

  · exact kid02_part555_checked

  · exact kid02_part585_checked

  · exact kid02_part615_checked

  · exact kid02_part526_checked

  · exact kid02_part556_checked

  · exact kid02_part586_checked

  · exact kid02_part616_checked

  · exact kid02_part527_checked

  · exact kid02_part557_checked

  · exact kid02_part587_checked

  · exact kid02_part617_checked

  · exact kid02_part552_checked

  · exact kid02_part582_checked

  · exact kid02_part612_checked

  · exact kid02_part642_checked

def kid02_part643 : Audit := .cycle 0 9 true (0)
theorem kid02_part643_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,0⟩)) (kid02_part643) = true := by rfl

def kid02_part644 : Audit := .cycle 1 8 true (1)
theorem kid02_part644_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,1⟩)) (kid02_part644) = true := by rfl

def kid02_part645 : Audit := .cycle 2 7 true (1)
theorem kid02_part645_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,2⟩)) (kid02_part645) = true := by rfl

def kid02_part646 : Audit := .cycle 1 11 true (1)
theorem kid02_part646_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,3⟩)) (kid02_part646) = true := by rfl

def kid02_part648 : Audit := .cycle 1 10 true (1)
theorem kid02_part648_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part648) = true := by rfl

def kid02_part649 : Audit := .cycle 21 1 false (1)
theorem kid02_part649_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part649) = true := by rfl

def kid02_part650 : Audit := .cycle 8 2 true (2)
theorem kid02_part650_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part650) = true := by rfl

def kid02_part651 : Audit := .cycle 0 11 true (0)
theorem kid02_part651_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part651) = true := by rfl

def kid02_part652 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (5,true),
.cycle 1 13 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 15 1 false (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (5,true),
.cycle 1 24 true (0),
.cycle 18 1 false (2),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
]),
.cycle 17 5 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 17 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (5,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 9 4 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 10 3 true (2),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
])
theorem kid02_part652_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part652) = true := by rfl

def kid02_part654 : Audit := .cycle 0 11 true (0)
theorem kid02_part654_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part654) = true := by rfl

def kid02_part655 : Audit := .cycle 1 10 true (1)
theorem kid02_part655_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part655) = true := by rfl

def kid02_part656 : Audit := .cycle 21 1 false (1)
theorem kid02_part656_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part656) = true := by rfl

def kid02_part657 : Audit := .cycle 1 13 true (0)
theorem kid02_part657_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part657) = true := by rfl

def kid02_part658 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 15 false (3),
.cycle 11 12 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 14 1 true (-2),
.cycle 11 7 false (1),
.last 19 (4,true),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 28 (4,true),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 1 17 false (3),
.cycle 11 4 false (1),
.cycle 14 1 true (-2)
])
theorem kid02_part658_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part658) = true := by rfl

def kid02_part659 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 14 3 false (0),
.cycle 11 1 true (1)
])
theorem kid02_part659_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part659) = true := by rfl

def kid02_part660 : Audit := .cycle 0 11 true (0)
theorem kid02_part660_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part660) = true := by rfl

def kid02_part661 : Audit := .cycle 1 10 true (1)
theorem kid02_part661_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part661) = true := by rfl

def kid02_part662 : Audit := .cycle 1 24 true (0)
theorem kid02_part662_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part662) = true := by rfl

def kid02_part663 : Audit := .cycle 20 1 false (2)
theorem kid02_part663_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part663) = true := by rfl

def kid02_part664 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.cycle 21 7 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (1),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
])
theorem kid02_part664_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part664) = true := by rfl

def kid02_part665 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,true),
.cycle 1 24 true (0),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid02_part665_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part665) = true := by rfl

def kid02_part666 : Audit := .cycle 17 5 false (1)
theorem kid02_part666_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part666) = true := by rfl

def kid02_part667 : Audit := .cycle 25 1 false (-1)
theorem kid02_part667_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part667) = true := by rfl

def kid02_part668 : Audit := .cycle 0 13 true (0)
theorem kid02_part668_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part668) = true := by rfl

def kid02_part669 : Audit := .cycle 18 1 false (0)
theorem kid02_part669_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part669) = true := by rfl

def kid02_part670 : Audit := .split 14 (5,false) (byMove [
.cycle 16 30 true (-2),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 7 false (1),
.last 19 (4,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 12 4 true (-2),
.cycle 11 7 false (1),
.last 19 (4,true),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.last 19 (4,true),
.cycle 0 26 true (-2),
.cycle 11 9 false (1),
.cycle 11 4 false (1),
.last 17 (4,true)
])
theorem kid02_part670_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part670) = true := by rfl

def kid02_part671 : Audit := .split 11 (5,false) (byMove [
.last 23 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.last 19 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid02_part671_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part671) = true := by rfl

def kid02_part672 : Audit := .cycle 0 11 true (0)
theorem kid02_part672_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part672) = true := by rfl

def kid02_part673 : Audit := .cycle 1 10 true (1)
theorem kid02_part673_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part673) = true := by rfl

def kid02_part674 : Audit := .cycle 2 9 true (1)
theorem kid02_part674_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part674) = true := by rfl

def kid02_part675 : Audit := .cycle 1 13 true (1)
theorem kid02_part675_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part675) = true := by rfl

def kid02_part676 : Audit := .cycle 9 2 true (2)
theorem kid02_part676_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part676) = true := by rfl

def kid02_part677 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid02_part677_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part677) = true := by rfl

def kid02_part653 : Audit := .split 10 (5,true) (byMove [(kid02_part654),(kid02_part655),(kid02_part656),(kid02_part657),(kid02_part658),(kid02_part659),(kid02_part660),(kid02_part661),(kid02_part662),(kid02_part663),(kid02_part664),(kid02_part665),(kid02_part666),(kid02_part667),(kid02_part668),(kid02_part669),(kid02_part670),(kid02_part671),(kid02_part672),(kid02_part673),(kid02_part674),(kid02_part675),(kid02_part676),(kid02_part677)])

theorem kid02_part653_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part653) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid02_part654),(kid02_part655),(kid02_part656),(kid02_part657),(kid02_part658),(kid02_part659),(kid02_part660),(kid02_part661),(kid02_part662),(kid02_part663),(kid02_part664),(kid02_part665),(kid02_part666),(kid02_part667),(kid02_part668),(kid02_part669),(kid02_part670),(kid02_part671),(kid02_part672),(kid02_part673),(kid02_part674),(kid02_part675),(kid02_part676),(kid02_part677)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part654_checked

  · exact kid02_part660_checked

  · exact kid02_part666_checked

  · exact kid02_part672_checked

  · exact kid02_part655_checked

  · exact kid02_part661_checked

  · exact kid02_part667_checked

  · exact kid02_part673_checked

  · exact kid02_part656_checked

  · exact kid02_part662_checked

  · exact kid02_part668_checked

  · exact kid02_part674_checked

  · exact kid02_part657_checked

  · exact kid02_part663_checked

  · exact kid02_part669_checked

  · exact kid02_part675_checked

  · exact kid02_part658_checked

  · exact kid02_part664_checked

  · exact kid02_part670_checked

  · exact kid02_part676_checked

  · exact kid02_part659_checked

  · exact kid02_part665_checked

  · exact kid02_part671_checked

  · exact kid02_part677_checked

def kid02_part678 : Audit := .cycle 0 10 true (0)
theorem kid02_part678_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part678) = true := by rfl

def kid02_part679 : Audit := .cycle 1 9 true (1)
theorem kid02_part679_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part679) = true := by rfl

def kid02_part680 : Audit := .cycle 8 11 true (2)
theorem kid02_part680_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part680) = true := by rfl

def kid02_part681 : Audit := .cycle 3 7 true (1)
theorem kid02_part681_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part681) = true := by rfl

def kid02_part682 : Audit := .cycle 9 1 true (3)
theorem kid02_part682_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part682) = true := by rfl

def kid02_part683 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 42 (4,true),
.cycle 12 9 true (0),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.cycle 21 7 false (2),
.cycle 12 10 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 21 (5,true) (byMove [
.cycle 8 16 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 8 18 true (2),
.cycle 8 16 true (2),
.cycle 0 25 true (0),
.cycle 1 22 true (1),
.cycle 1 32 true (1),
.cycle 8 14 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 34, 16, 1, 64, 32, 64],64⟩,
.cycle 7 21 true (2),
.last 24 (4,true),
.cycle 1 24 true (1),
.cycle 4 25 true (1),
.cycle 20 2 true (4),
.last 24 (4,true),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 8 14 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 22 11 true (6)
]),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 3 18 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 8 23 true (2),
.cycle 11 9 true (2),
.last 33 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 8, 64],[2, 34, 16, 1, 64, 32, 64],64⟩,
.cycle 7 14 true (2),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.cycle 3 18 true (1)
]),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (2),
.cycle 11 9 true (2),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.last 18 (4,true),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 12 58 true (0),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 26 1 false (6),
.cycle 14 17 true (1),
.last 15 (4,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 13 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid02_part683_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part683) = true := by rfl

def kid02_part684 : Audit := .cycle 6 4 true (2)
theorem kid02_part684_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part684) = true := by rfl

def kid02_part685 : Audit := .cycle 21 1 false (1)
theorem kid02_part685_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part685) = true := by rfl

def kid02_part686 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 0 20 true (-2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 0 20 true (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 0 16 true (0),
.last 13 (5,false),
.cycle 21 7 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 12 true (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 0 16 true (0),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.cycle 13 10 true (-2),
.split 12 (5,true) (byMove [
.cycle 14 7 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 7 17 true (0),
.cycle 13 10 true (-2),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 21 7 false (1),
.cycle 29 1 false (-1),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 13 10 true (-2),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 18 (5,true),
.cycle 10 3 true (2),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
])
theorem kid02_part686_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part686) = true := by rfl

def kid02_part687 : Audit := .cycle 1 11 true (1)
theorem kid02_part687_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part687) = true := by rfl

def kid02_part688 : Audit := .split 10 (4,true) (byMove [
.cycle 12 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 7 13 true (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.last 18 (5,true),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 7 6 true (1),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 13 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (5,true),
.last 18 (5,true),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.last 13 (5,true)
]),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 8 3 true (2),
.cycle 0 12 true (0),
.cycle 21 1 false (5),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 42 (5,false),
.cycle 1 24 true (0),
.last 21 (5,false),
.last 12 (5,false),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
]),
.cycle 17 5 false (1),
.cycle 20 1 false (0),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 14 (5,true),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (5,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 8 3 true (2),
.cycle 0 12 true (0),
.cycle 9 3 true (2),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.last 17 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.last 14 (5,false),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
])
theorem kid02_part688_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part688) = true := by rfl

def kid02_part690 : Audit := .cycle 12 5 true (2)
theorem kid02_part690_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid02_part690) = true := by rfl

def kid02_part691 : Audit := .cycle 0 14 true (0)
theorem kid02_part691_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid02_part691) = true := by rfl

def kid02_part692 : Audit := .cycle 21 1 false (1)
theorem kid02_part692_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid02_part692) = true := by rfl

def kid02_part693 : Audit := .cycle 7 13 true (0)
theorem kid02_part693_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid02_part693) = true := by rfl

def kid02_part694 : Audit := .split 14 (5,false) (byMove [
.last 20 (4,true),
.cycle 27 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 11 7 false (1),
.last 17 (4,true),
.last 22 (4,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 11 6 false (1),
.last 18 (4,true),
.cycle 7 10 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid02_part694_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid02_part694) = true := by rfl

def kid02_part695 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 7 6 true (1),
.cycle 0 21 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 14 1 true (2),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (4,true),
.cycle 21 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 24 true (-1),
.cycle 1 19 false (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 14 3 false (0),
.cycle 17 1 true (-1)
])
theorem kid02_part695_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid02_part695) = true := by rfl

def kid02_part696 : Audit := .cycle 1 11 true (1)
theorem kid02_part696_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid02_part696) = true := by rfl

def kid02_part697 : Audit := .cycle 24 1 false (2)
theorem kid02_part697_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid02_part697) = true := by rfl

def kid02_part698 : Audit := .cycle 8 3 true (2)
theorem kid02_part698_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid02_part698) = true := by rfl

def kid02_part699 : Audit := .cycle 0 12 true (0)
theorem kid02_part699_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid02_part699) = true := by rfl

def kid02_part700 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 19 true (0),
.cycle 1 24 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid02_part700_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid02_part700) = true := by rfl

def kid02_part701 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 18 2 false (2),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.last 15 (4,true),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 2 false (5),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid02_part701_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid02_part701) = true := by rfl

def kid02_part702 : Audit := .cycle 17 5 false (1)
theorem kid02_part702_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid02_part702) = true := by rfl

def kid02_part703 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 20 1 false (0),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.last 18 (5,false),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 19 true (1),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 33 1 false (-1),
.cycle 20 1 false (0),
.cycle 12 2 true (2),
.cycle 1 15 true (1),
.last 18 (5,false),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 22 1 false (0),
.last 14 (5,false)
])
theorem kid02_part703_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid02_part703) = true := by rfl

def kid02_part704 : Audit := .cycle 1 13 true (1)
theorem kid02_part704_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid02_part704) = true := by rfl

def kid02_part705 : Audit := .cycle 18 1 false (0)
theorem kid02_part705_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid02_part705) = true := by rfl

def kid02_part706 : Audit := .split 14 (5,false) (byMove [
.last 18 (4,true),
.cycle 27 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 7 false (1),
.cycle 17 1 false (-1),
.last 16 (4,true),
.cycle 11 8 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 11 7 false (1),
.last 17 (4,true),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 11 6 false (1),
.last 16 (4,true),
.cycle 5 10 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid02_part706_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid02_part706) = true := by rfl

def kid02_part707 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid02_part707_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid02_part707) = true := by rfl

def kid02_part708 : Audit := .cycle 1 11 true (1)
theorem kid02_part708_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid02_part708) = true := by rfl

def kid02_part709 : Audit := .cycle 7 4 true (2)
theorem kid02_part709_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid02_part709) = true := by rfl

def kid02_part710 : Audit := .cycle 8 3 true (2)
theorem kid02_part710_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid02_part710) = true := by rfl

def kid02_part711 : Audit := .cycle 0 12 true (0)
theorem kid02_part711_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid02_part711) = true := by rfl

def kid02_part712 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 18 (5,false),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 11 2 true (2),
.cycle 1 13 true (1),
.last 18 (5,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid02_part712_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid02_part712) = true := by rfl

def kid02_part713 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 10 7 true (2),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid02_part713_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid02_part713) = true := by rfl

def kid02_part689 : Audit := .split 10 (5,true) (byMove [(kid02_part690),(kid02_part691),(kid02_part692),(kid02_part693),(kid02_part694),(kid02_part695),(kid02_part696),(kid02_part697),(kid02_part698),(kid02_part699),(kid02_part700),(kid02_part701),(kid02_part702),(kid02_part703),(kid02_part704),(kid02_part705),(kid02_part706),(kid02_part707),(kid02_part708),(kid02_part709),(kid02_part710),(kid02_part711),(kid02_part712),(kid02_part713)])

theorem kid02_part689_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part689) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid02_part690),(kid02_part691),(kid02_part692),(kid02_part693),(kid02_part694),(kid02_part695),(kid02_part696),(kid02_part697),(kid02_part698),(kid02_part699),(kid02_part700),(kid02_part701),(kid02_part702),(kid02_part703),(kid02_part704),(kid02_part705),(kid02_part706),(kid02_part707),(kid02_part708),(kid02_part709),(kid02_part710),(kid02_part711),(kid02_part712),(kid02_part713)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part690_checked

  · exact kid02_part696_checked

  · exact kid02_part702_checked

  · exact kid02_part708_checked

  · exact kid02_part691_checked

  · exact kid02_part697_checked

  · exact kid02_part703_checked

  · exact kid02_part709_checked

  · exact kid02_part692_checked

  · exact kid02_part698_checked

  · exact kid02_part704_checked

  · exact kid02_part710_checked

  · exact kid02_part693_checked

  · exact kid02_part699_checked

  · exact kid02_part705_checked

  · exact kid02_part711_checked

  · exact kid02_part694_checked

  · exact kid02_part700_checked

  · exact kid02_part706_checked

  · exact kid02_part712_checked

  · exact kid02_part695_checked

  · exact kid02_part701_checked

  · exact kid02_part707_checked

  · exact kid02_part713_checked

def kid02_part714 : Audit := .cycle 0 10 true (0)
theorem kid02_part714_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part714) = true := by rfl

def kid02_part715 : Audit := .cycle 1 9 true (1)
theorem kid02_part715_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part715) = true := by rfl

def kid02_part716 : Audit := .cycle 2 8 true (1)
theorem kid02_part716_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part716) = true := by rfl

def kid02_part717 : Audit := .cycle 1 12 true (1)
theorem kid02_part717_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part717) = true := by rfl

def kid02_part718 : Audit := .cycle 9 1 true (3)
theorem kid02_part718_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part718) = true := by rfl

def kid02_part720 : Audit := .cycle 1 11 true (1)
theorem kid02_part720_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part720) = true := by rfl

def kid02_part721 : Audit := .cycle 7 4 true (2)
theorem kid02_part721_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part721) = true := by rfl

def kid02_part722 : Audit := .cycle 8 3 true (2)
theorem kid02_part722_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part722) = true := by rfl

def kid02_part723 : Audit := .cycle 0 12 true (0)
theorem kid02_part723_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part723) = true := by rfl

def kid02_part724 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 9 4 true (3),
.cycle 6 6 true (2),
.last 21 (5,true),
.cycle 11 2 true (2),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
])
theorem kid02_part724_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part724) = true := by rfl

def kid02_part725 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 19 1 false (1),
.cycle 6 6 true (2),
.cycle 18 4 true (1),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
])
theorem kid02_part725_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part725) = true := by rfl

def kid02_part726 : Audit := .cycle 0 11 true (0)
theorem kid02_part726_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part726) = true := by rfl

def kid02_part727 : Audit := .cycle 1 10 true (1)
theorem kid02_part727_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part727) = true := by rfl

def kid02_part728 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 52 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.cycle 9 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 4, 64],[2, 34, 16, 1, 64, 32, 64],64⟩,
.cycle 6 15 true (2),
.cycle 17 4 true (4),
.last 22 (4,true),
.cycle 1 22 true (1),
.last 21 (4,true),
.last 25 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 12 true (3),
.cycle 10 11 true (3)
])
theorem kid02_part728_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part728) = true := by rfl

def kid02_part729 : Audit := .cycle 3 8 true (1)
theorem kid02_part729_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part729) = true := by rfl

def kid02_part730 : Audit := .cycle 9 2 true (3)
theorem kid02_part730_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part730) = true := by rfl

def kid02_part731 : Audit := .cycle 10 1 true (4)
theorem kid02_part731_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part731) = true := by rfl

def kid02_part732 : Audit := .cycle 6 5 true (2)
theorem kid02_part732_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part732) = true := by rfl

def kid02_part733 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 8 7 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.cycle 11 12 true (2),
.cycle 8 9 true (2),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 16 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (2),
.cycle 10 5 true (2)
])
theorem kid02_part733_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part733) = true := by rfl

def kid02_part734 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 19 5 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 16 (5,true),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
])
theorem kid02_part734_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part734) = true := by rfl

def kid02_part735 : Audit := .cycle 1 12 true (1)
theorem kid02_part735_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part735) = true := by rfl

def kid02_part736 : Audit := .split 11 (4,true) (byMove [
.cycle 8 6 true (2),
.cycle 25 1 false (1),
.last 14 (5,true),
.cycle 7 7 true (2),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true),
.last 16 (5,true),
.last 21 (5,true),
.cycle 11 2 true (2),
.cycle 5 7 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true)
])
theorem kid02_part736_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part736) = true := by rfl

def kid02_part737 : Audit := .split 11 (5,true) (byMove [
.cycle 8 6 true (2),
.cycle 25 1 false (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 33 1 false (7),
.cycle 6 11 true (2),
.cycle 18 4 true (1),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (3)
])
theorem kid02_part737_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part737) = true := by rfl

def kid02_part738 : Audit := .cycle 0 11 true (0)
theorem kid02_part738_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part738) = true := by rfl

def kid02_part739 : Audit := .cycle 1 10 true (1)
theorem kid02_part739_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part739) = true := by rfl

def kid02_part740 : Audit := .cycle 2 9 true (1)
theorem kid02_part740_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part740) = true := by rfl

def kid02_part741 : Audit := .cycle 1 13 true (1)
theorem kid02_part741_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part741) = true := by rfl

def kid02_part742 : Audit := .cycle 9 2 true (3)
theorem kid02_part742_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part742) = true := by rfl

def kid02_part743 : Audit := .cycle 10 1 true (4)
theorem kid02_part743_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part743) = true := by rfl

def kid02_part719 : Audit := .split 10 (5,false) (byMove [(kid02_part720),(kid02_part721),(kid02_part722),(kid02_part723),(kid02_part724),(kid02_part725),(kid02_part726),(kid02_part727),(kid02_part728),(kid02_part729),(kid02_part730),(kid02_part731),(kid02_part732),(kid02_part733),(kid02_part734),(kid02_part735),(kid02_part736),(kid02_part737),(kid02_part738),(kid02_part739),(kid02_part740),(kid02_part741),(kid02_part742),(kid02_part743)])

theorem kid02_part719_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part719) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid02_part720),(kid02_part721),(kid02_part722),(kid02_part723),(kid02_part724),(kid02_part725),(kid02_part726),(kid02_part727),(kid02_part728),(kid02_part729),(kid02_part730),(kid02_part731),(kid02_part732),(kid02_part733),(kid02_part734),(kid02_part735),(kid02_part736),(kid02_part737),(kid02_part738),(kid02_part739),(kid02_part740),(kid02_part741),(kid02_part742),(kid02_part743)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part720_checked

  · exact kid02_part726_checked

  · exact kid02_part732_checked

  · exact kid02_part738_checked

  · exact kid02_part721_checked

  · exact kid02_part727_checked

  · exact kid02_part733_checked

  · exact kid02_part739_checked

  · exact kid02_part722_checked

  · exact kid02_part728_checked

  · exact kid02_part734_checked

  · exact kid02_part740_checked

  · exact kid02_part723_checked

  · exact kid02_part729_checked

  · exact kid02_part735_checked

  · exact kid02_part741_checked

  · exact kid02_part724_checked

  · exact kid02_part730_checked

  · exact kid02_part736_checked

  · exact kid02_part742_checked

  · exact kid02_part725_checked

  · exact kid02_part731_checked

  · exact kid02_part737_checked

  · exact kid02_part743_checked

def kid02_part647 : Audit := .split 9 (4,false) (byMove [(kid02_part648),(kid02_part649),(kid02_part650),(kid02_part651),(kid02_part652),(kid02_part653),(kid02_part678),(kid02_part679),(kid02_part680),(kid02_part681),(kid02_part682),(kid02_part683),(kid02_part684),(kid02_part685),(kid02_part686),(kid02_part687),(kid02_part688),(kid02_part689),(kid02_part714),(kid02_part715),(kid02_part716),(kid02_part717),(kid02_part718),(kid02_part719)])

theorem kid02_part647_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (kid02_part647) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid02_part648),(kid02_part649),(kid02_part650),(kid02_part651),(kid02_part652),(kid02_part653),(kid02_part678),(kid02_part679),(kid02_part680),(kid02_part681),(kid02_part682),(kid02_part683),(kid02_part684),(kid02_part685),(kid02_part686),(kid02_part687),(kid02_part688),(kid02_part689),(kid02_part714),(kid02_part715),(kid02_part716),(kid02_part717),(kid02_part718),(kid02_part719)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part648_checked

  · exact kid02_part678_checked

  · exact kid02_part684_checked

  · exact kid02_part714_checked

  · exact kid02_part649_checked

  · exact kid02_part679_checked

  · exact kid02_part685_checked

  · exact kid02_part715_checked

  · exact kid02_part650_checked

  · exact kid02_part680_checked

  · exact kid02_part686_checked

  · exact kid02_part716_checked

  · exact kid02_part651_checked

  · exact kid02_part681_checked

  · exact kid02_part687_checked

  · exact kid02_part717_checked

  · exact kid02_part652_checked

  · exact kid02_part682_checked

  · exact kid02_part688_checked

  · exact kid02_part718_checked

  · exact kid02_part653_checked

  · exact kid02_part683_checked

  · exact kid02_part689_checked

  · exact kid02_part719_checked

def kid02_part745 : Audit := .cycle 1 10 true (1)
theorem kid02_part745_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid02_part745) = true := by rfl

def kid02_part746 : Audit := .cycle 21 1 false (1)
theorem kid02_part746_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid02_part746) = true := by rfl

def kid02_part747 : Audit := .cycle 8 2 true (2)
theorem kid02_part747_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid02_part747) = true := by rfl

def kid02_part748 : Audit := .cycle 0 11 true (0)
theorem kid02_part748_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid02_part748) = true := by rfl

def kid02_part750 : Audit := .cycle 0 11 true (0)
theorem kid02_part750_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part750) = true := by rfl

def kid02_part751 : Audit := .cycle 1 10 true (1)
theorem kid02_part751_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part751) = true := by rfl

def kid02_part752 : Audit := .cycle 21 1 false (1)
theorem kid02_part752_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part752) = true := by rfl

def kid02_part753 : Audit := .cycle 1 13 true (0)
theorem kid02_part753_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part753) = true := by rfl

def kid02_part754 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (5,true),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 14 3 false (0)
])
theorem kid02_part754_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part754) = true := by rfl

def kid02_part755 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 15 false (3),
.cycle 11 12 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 true (-2),
.cycle 13 2 true (-2),
.cycle 11 7 false (1),
.last 19 (5,true),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 28 (5,true),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 1 17 false (3),
.cycle 14 1 true (-2),
.cycle 11 4 false (1)
])
theorem kid02_part755_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part755) = true := by rfl

def kid02_part756 : Audit := .cycle 0 11 true (0)
theorem kid02_part756_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part756) = true := by rfl

def kid02_part757 : Audit := .cycle 1 10 true (1)
theorem kid02_part757_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part757) = true := by rfl

def kid02_part758 : Audit := .cycle 1 24 true (0)
theorem kid02_part758_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part758) = true := by rfl

def kid02_part759 : Audit := .cycle 20 1 false (2)
theorem kid02_part759_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part759) = true := by rfl

def kid02_part760 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid02_part760_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part760) = true := by rfl

def kid02_part761 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 21 7 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (2)
])
theorem kid02_part761_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part761) = true := by rfl

def kid02_part762 : Audit := .cycle 17 5 false (1)
theorem kid02_part762_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part762) = true := by rfl

def kid02_part763 : Audit := .cycle 25 1 false (-1)
theorem kid02_part763_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part763) = true := by rfl

def kid02_part764 : Audit := .cycle 0 13 true (0)
theorem kid02_part764_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part764) = true := by rfl

def kid02_part765 : Audit := .cycle 18 1 false (0)
theorem kid02_part765_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part765) = true := by rfl

def kid02_part766 : Audit := .split 11 (4,false) (byMove [
.last 23 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.last 19 (5,true),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid02_part766_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part766) = true := by rfl

def kid02_part767 : Audit := .split 14 (4,false) (byMove [
.cycle 16 30 true (-2),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 7 false (1),
.last 19 (5,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.cycle 11 7 false (1),
.last 19 (5,true),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 26 true (-2),
.cycle 11 9 false (1),
.last 17 (5,true),
.cycle 11 4 false (1)
])
theorem kid02_part767_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part767) = true := by rfl

def kid02_part768 : Audit := .cycle 0 11 true (0)
theorem kid02_part768_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part768) = true := by rfl

def kid02_part769 : Audit := .cycle 1 10 true (1)
theorem kid02_part769_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part769) = true := by rfl

def kid02_part770 : Audit := .cycle 2 9 true (1)
theorem kid02_part770_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part770) = true := by rfl

def kid02_part771 : Audit := .cycle 1 13 true (1)
theorem kid02_part771_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part771) = true := by rfl

def kid02_part772 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid02_part772_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part772) = true := by rfl

def kid02_part773 : Audit := .cycle 9 2 true (2)
theorem kid02_part773_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part773) = true := by rfl

def kid02_part749 : Audit := .split 10 (4,true) (byMove [(kid02_part750),(kid02_part751),(kid02_part752),(kid02_part753),(kid02_part754),(kid02_part755),(kid02_part756),(kid02_part757),(kid02_part758),(kid02_part759),(kid02_part760),(kid02_part761),(kid02_part762),(kid02_part763),(kid02_part764),(kid02_part765),(kid02_part766),(kid02_part767),(kid02_part768),(kid02_part769),(kid02_part770),(kid02_part771),(kid02_part772),(kid02_part773)])

theorem kid02_part749_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid02_part749) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid02_part750),(kid02_part751),(kid02_part752),(kid02_part753),(kid02_part754),(kid02_part755),(kid02_part756),(kid02_part757),(kid02_part758),(kid02_part759),(kid02_part760),(kid02_part761),(kid02_part762),(kid02_part763),(kid02_part764),(kid02_part765),(kid02_part766),(kid02_part767),(kid02_part768),(kid02_part769),(kid02_part770),(kid02_part771),(kid02_part772),(kid02_part773)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part750_checked

  · exact kid02_part756_checked

  · exact kid02_part762_checked

  · exact kid02_part768_checked

  · exact kid02_part751_checked

  · exact kid02_part757_checked

  · exact kid02_part763_checked

  · exact kid02_part769_checked

  · exact kid02_part752_checked

  · exact kid02_part758_checked

  · exact kid02_part764_checked

  · exact kid02_part770_checked

  · exact kid02_part753_checked

  · exact kid02_part759_checked

  · exact kid02_part765_checked

  · exact kid02_part771_checked

  · exact kid02_part754_checked

  · exact kid02_part760_checked

  · exact kid02_part766_checked

  · exact kid02_part772_checked

  · exact kid02_part755_checked

  · exact kid02_part761_checked

  · exact kid02_part767_checked

  · exact kid02_part773_checked

def kid02_part774 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 16 1 false (0),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.last 14 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (4,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 18 1 false (2),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 15 1 false (1),
.cycle 17 5 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 17 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 1 12 true (1),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (2),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 10 3 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid02_part774_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid02_part774) = true := by rfl

def kid02_part775 : Audit := .cycle 0 10 true (0)
theorem kid02_part775_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid02_part775) = true := by rfl

def kid02_part776 : Audit := .cycle 1 9 true (1)
theorem kid02_part776_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid02_part776) = true := by rfl

def kid02_part777 : Audit := .cycle 8 11 true (2)
theorem kid02_part777_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid02_part777) = true := by rfl

def kid02_part778 : Audit := .cycle 3 7 true (1)
theorem kid02_part778_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid02_part778) = true := by rfl

def kid02_part779 : Audit := .split 10 (4,false) (byMove [
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
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 42 (5,true),
.cycle 12 9 true (0),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 21 7 false (2),
.cycle 12 10 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 21 (4,true) (byMove [
.cycle 8 16 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 8 18 true (2),
.cycle 0 25 true (0),
.cycle 8 16 true (2),
.cycle 1 22 true (1),
.cycle 1 32 true (1),
.cycle 8 14 true (2),
.cycle 0 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 16, 64],[2, 18, 32, 1, 16, 64, 64],64⟩,
.last 22 (5,true),
.cycle 7 21 true (2),
.last 24 (5,true),
.cycle 1 24 true (1),
.cycle 4 25 true (1),
.last 24 (5,true),
.cycle 20 2 true (4),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 8 14 true (2),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.last 22 (5,true)
]),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 3 18 true (1),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 8 23 true (2),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 16, 64],[2, 18, 32, 1, 16, 64, 64],64⟩,
.last 33 (5,true),
.cycle 7 14 true (2),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 0 22 true (0),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 3 18 true (1),
.cycle 9 11 true (2)
]),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.last 18 (5,true),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 6 7 true (2),
.cycle 12 58 true (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 26 1 false (6),
.last 13 (5,true),
.cycle 14 17 true (1),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 13 3 true (3),
.last 13 (5,true)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (2),
.cycle 11 9 true (2),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid02_part779_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid02_part779) = true := by rfl

def kid02_part780 : Audit := .cycle 9 1 true (3)
theorem kid02_part780_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid02_part780) = true := by rfl

def kid02_part781 : Audit := .cycle 6 4 true (2)
theorem kid02_part781_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid02_part781) = true := by rfl

def kid02_part782 : Audit := .cycle 21 1 false (1)
theorem kid02_part782_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid02_part782) = true := by rfl

def kid02_part783 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 0 20 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 21 7 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 12 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 9 4 true (2)
]),
.cycle 0 20 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
]),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 14 7 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 7 17 true (0),
.last 13 (4,false),
.cycle 13 10 true (-2),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 21 7 false (1),
.cycle 29 1 false (-1),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 13 10 true (-2),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 11 2 true (2)
]),
.cycle 13 10 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 18 (4,true),
.cycle 10 3 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
]),
.cycle 9 3 true (2)
])
theorem kid02_part783_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid02_part783) = true := by rfl

def kid02_part784 : Audit := .cycle 1 11 true (1)
theorem kid02_part784_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid02_part784) = true := by rfl

def kid02_part786 : Audit := .cycle 12 5 true (2)
theorem kid02_part786_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid02_part786) = true := by rfl

def kid02_part787 : Audit := .cycle 0 14 true (0)
theorem kid02_part787_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid02_part787) = true := by rfl

def kid02_part788 : Audit := .cycle 21 1 false (1)
theorem kid02_part788_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid02_part788) = true := by rfl

def kid02_part789 : Audit := .cycle 7 13 true (0)
theorem kid02_part789_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid02_part789) = true := by rfl

def kid02_part790 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 0 21 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.last 14 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (5,true),
.cycle 21 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 24 true (-1),
.cycle 1 19 false (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.cycle 14 3 false (0)
])
theorem kid02_part790_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid02_part790) = true := by rfl

def kid02_part791 : Audit := .split 14 (4,false) (byMove [
.last 20 (5,true),
.cycle 27 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 11 7 false (1),
.last 17 (5,true),
.last 22 (5,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.cycle 11 6 false (1),
.last 18 (5,true),
.cycle 7 10 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid02_part791_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid02_part791) = true := by rfl

def kid02_part792 : Audit := .cycle 1 11 true (1)
theorem kid02_part792_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid02_part792) = true := by rfl

def kid02_part793 : Audit := .cycle 24 1 false (2)
theorem kid02_part793_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid02_part793) = true := by rfl

def kid02_part794 : Audit := .cycle 8 3 true (2)
theorem kid02_part794_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid02_part794) = true := by rfl

def kid02_part795 : Audit := .cycle 0 12 true (0)
theorem kid02_part795_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid02_part795) = true := by rfl

def kid02_part796 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 17 1 false (1),
.cycle 18 2 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 12 1 true (4),
.last 15 (5,true),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (5),
.cycle 21 2 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid02_part796_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid02_part796) = true := by rfl

def kid02_part797 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 19 true (0),
.cycle 1 24 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid02_part797_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid02_part797) = true := by rfl

def kid02_part798 : Audit := .cycle 17 5 false (1)
theorem kid02_part798_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid02_part798) = true := by rfl

def kid02_part799 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 20 1 false (0),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.cycle 25 1 false (-1),
.last 18 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 19 true (1),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 33 1 false (-1),
.cycle 20 1 false (0),
.cycle 12 2 true (2),
.cycle 1 15 true (1),
.cycle 25 1 false (-1),
.last 18 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 22 1 false (0)
])
theorem kid02_part799_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid02_part799) = true := by rfl

def kid02_part800 : Audit := .cycle 1 13 true (1)
theorem kid02_part800_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid02_part800) = true := by rfl

def kid02_part801 : Audit := .cycle 18 1 false (0)
theorem kid02_part801_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid02_part801) = true := by rfl

def kid02_part802 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 13 (5,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid02_part802_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid02_part802) = true := by rfl

def kid02_part803 : Audit := .split 14 (4,false) (byMove [
.last 18 (5,true),
.cycle 27 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 7 false (1),
.cycle 17 1 false (-1),
.last 16 (5,true),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 11 7 false (1),
.last 17 (5,true),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.cycle 11 6 false (1),
.last 16 (5,true),
.cycle 5 10 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid02_part803_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid02_part803) = true := by rfl

def kid02_part804 : Audit := .cycle 1 11 true (1)
theorem kid02_part804_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid02_part804) = true := by rfl

def kid02_part805 : Audit := .cycle 7 4 true (2)
theorem kid02_part805_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid02_part805) = true := by rfl

def kid02_part806 : Audit := .cycle 8 3 true (2)
theorem kid02_part806_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid02_part806) = true := by rfl

def kid02_part807 : Audit := .cycle 0 12 true (0)
theorem kid02_part807_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid02_part807) = true := by rfl

def kid02_part808 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 15 (5,true),
.cycle 6 7 true (2),
.cycle 10 7 true (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid02_part808_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid02_part808) = true := by rfl

def kid02_part809 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (2),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.cycle 11 2 true (2),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid02_part809_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid02_part809) = true := by rfl

def kid02_part785 : Audit := .split 10 (4,true) (byMove [(kid02_part786),(kid02_part787),(kid02_part788),(kid02_part789),(kid02_part790),(kid02_part791),(kid02_part792),(kid02_part793),(kid02_part794),(kid02_part795),(kid02_part796),(kid02_part797),(kid02_part798),(kid02_part799),(kid02_part800),(kid02_part801),(kid02_part802),(kid02_part803),(kid02_part804),(kid02_part805),(kid02_part806),(kid02_part807),(kid02_part808),(kid02_part809)])

theorem kid02_part785_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid02_part785) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid02_part786),(kid02_part787),(kid02_part788),(kid02_part789),(kid02_part790),(kid02_part791),(kid02_part792),(kid02_part793),(kid02_part794),(kid02_part795),(kid02_part796),(kid02_part797),(kid02_part798),(kid02_part799),(kid02_part800),(kid02_part801),(kid02_part802),(kid02_part803),(kid02_part804),(kid02_part805),(kid02_part806),(kid02_part807),(kid02_part808),(kid02_part809)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part786_checked

  · exact kid02_part792_checked

  · exact kid02_part798_checked

  · exact kid02_part804_checked

  · exact kid02_part787_checked

  · exact kid02_part793_checked

  · exact kid02_part799_checked

  · exact kid02_part805_checked

  · exact kid02_part788_checked

  · exact kid02_part794_checked

  · exact kid02_part800_checked

  · exact kid02_part806_checked

  · exact kid02_part789_checked

  · exact kid02_part795_checked

  · exact kid02_part801_checked

  · exact kid02_part807_checked

  · exact kid02_part790_checked

  · exact kid02_part796_checked

  · exact kid02_part802_checked

  · exact kid02_part808_checked

  · exact kid02_part791_checked

  · exact kid02_part797_checked

  · exact kid02_part803_checked

  · exact kid02_part809_checked

def kid02_part810 : Audit := .split 10 (5,true) (byMove [
.cycle 12 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 7 13 true (0),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.last 18 (4,true),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 7 6 true (1),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (4,true),
.cycle 16 1 false (0),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (4,true),
.last 18 (4,true),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 17 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 8 3 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 42 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.last 21 (4,false),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 21 1 false (5),
.cycle 17 5 false (1),
.cycle 20 1 false (0),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 6 6 true (1),
.cycle 25 1 false (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 14 1 false (0),
.last 14 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 17 (4,true),
.last 16 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 8 3 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 15 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 17 (4,false),
.cycle 6 6 true (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 9 3 true (2)
])
theorem kid02_part810_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid02_part810) = true := by rfl

def kid02_part811 : Audit := .cycle 0 10 true (0)
theorem kid02_part811_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid02_part811) = true := by rfl

def kid02_part812 : Audit := .cycle 1 9 true (1)
theorem kid02_part812_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid02_part812) = true := by rfl

def kid02_part813 : Audit := .cycle 2 8 true (1)
theorem kid02_part813_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid02_part813) = true := by rfl

def kid02_part814 : Audit := .cycle 1 12 true (1)
theorem kid02_part814_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid02_part814) = true := by rfl

def kid02_part816 : Audit := .cycle 1 11 true (1)
theorem kid02_part816_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid02_part816) = true := by rfl

def kid02_part817 : Audit := .cycle 7 4 true (2)
theorem kid02_part817_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid02_part817) = true := by rfl

def kid02_part818 : Audit := .cycle 8 3 true (2)
theorem kid02_part818_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid02_part818) = true := by rfl

def kid02_part819 : Audit := .cycle 0 12 true (0)
theorem kid02_part819_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid02_part819) = true := by rfl

def kid02_part820 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.cycle 18 4 true (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid02_part820_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid02_part820) = true := by rfl

def kid02_part821 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 9 4 true (3),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.last 21 (4,true),
.cycle 11 2 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid02_part821_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid02_part821) = true := by rfl

def kid02_part822 : Audit := .cycle 0 11 true (0)
theorem kid02_part822_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid02_part822) = true := by rfl

def kid02_part823 : Audit := .cycle 1 10 true (1)
theorem kid02_part823_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid02_part823) = true := by rfl

def kid02_part824 : Audit := .split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 16, 64],[2, 18, 32, 1, 16, 64, 64],64⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.cycle 17 4 true (4),
.last 22 (5,true),
.cycle 1 22 true (1),
.last 25 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 11 true (3),
.cycle 9 12 true (3)
])
theorem kid02_part824_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid02_part824) = true := by rfl

def kid02_part825 : Audit := .cycle 3 8 true (1)
theorem kid02_part825_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid02_part825) = true := by rfl

def kid02_part826 : Audit := .cycle 10 1 true (4)
theorem kid02_part826_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid02_part826) = true := by rfl

def kid02_part827 : Audit := .cycle 9 2 true (3)
theorem kid02_part827_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid02_part827) = true := by rfl

def kid02_part828 : Audit := .cycle 6 5 true (2)
theorem kid02_part828_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid02_part828) = true := by rfl

def kid02_part829 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 8 7 true (2),
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.cycle 8 9 true (2),
.cycle 11 12 true (2),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 20 1 false (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 10 5 true (2),
.cycle 9 6 true (2)
])
theorem kid02_part829_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid02_part829) = true := by rfl

def kid02_part830 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 8 5 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 0 16 true (0),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.last 16 (4,true),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3)
])
theorem kid02_part830_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid02_part830) = true := by rfl

def kid02_part831 : Audit := .cycle 1 12 true (1)
theorem kid02_part831_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid02_part831) = true := by rfl

def kid02_part832 : Audit := .split 11 (4,true) (byMove [
.cycle 8 6 true (2),
.cycle 25 1 false (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.last 12 (5,true),
.cycle 6 11 true (2),
.cycle 18 4 true (1),
.last 13 (5,true),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.last 12 (5,true)
])
theorem kid02_part832_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid02_part832) = true := by rfl

def kid02_part833 : Audit := .split 11 (5,true) (byMove [
.cycle 8 6 true (2),
.cycle 25 1 false (1),
.last 14 (4,true),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3),
.last 16 (4,true),
.last 21 (4,true),
.cycle 11 2 true (2),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3)
])
theorem kid02_part833_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid02_part833) = true := by rfl

def kid02_part834 : Audit := .cycle 0 11 true (0)
theorem kid02_part834_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid02_part834) = true := by rfl

def kid02_part835 : Audit := .cycle 1 10 true (1)
theorem kid02_part835_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid02_part835) = true := by rfl

def kid02_part836 : Audit := .cycle 2 9 true (1)
theorem kid02_part836_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid02_part836) = true := by rfl

def kid02_part837 : Audit := .cycle 1 13 true (1)
theorem kid02_part837_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid02_part837) = true := by rfl

def kid02_part838 : Audit := .cycle 10 1 true (4)
theorem kid02_part838_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid02_part838) = true := by rfl

def kid02_part839 : Audit := .cycle 9 2 true (3)
theorem kid02_part839_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid02_part839) = true := by rfl

def kid02_part815 : Audit := .split 10 (4,false) (byMove [(kid02_part816),(kid02_part817),(kid02_part818),(kid02_part819),(kid02_part820),(kid02_part821),(kid02_part822),(kid02_part823),(kid02_part824),(kid02_part825),(kid02_part826),(kid02_part827),(kid02_part828),(kid02_part829),(kid02_part830),(kid02_part831),(kid02_part832),(kid02_part833),(kid02_part834),(kid02_part835),(kid02_part836),(kid02_part837),(kid02_part838),(kid02_part839)])

theorem kid02_part815_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid02_part815) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid02_part816),(kid02_part817),(kid02_part818),(kid02_part819),(kid02_part820),(kid02_part821),(kid02_part822),(kid02_part823),(kid02_part824),(kid02_part825),(kid02_part826),(kid02_part827),(kid02_part828),(kid02_part829),(kid02_part830),(kid02_part831),(kid02_part832),(kid02_part833),(kid02_part834),(kid02_part835),(kid02_part836),(kid02_part837),(kid02_part838),(kid02_part839)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part816_checked

  · exact kid02_part822_checked

  · exact kid02_part828_checked

  · exact kid02_part834_checked

  · exact kid02_part817_checked

  · exact kid02_part823_checked

  · exact kid02_part829_checked

  · exact kid02_part835_checked

  · exact kid02_part818_checked

  · exact kid02_part824_checked

  · exact kid02_part830_checked

  · exact kid02_part836_checked

  · exact kid02_part819_checked

  · exact kid02_part825_checked

  · exact kid02_part831_checked

  · exact kid02_part837_checked

  · exact kid02_part820_checked

  · exact kid02_part826_checked

  · exact kid02_part832_checked

  · exact kid02_part838_checked

  · exact kid02_part821_checked

  · exact kid02_part827_checked

  · exact kid02_part833_checked

  · exact kid02_part839_checked

def kid02_part840 : Audit := .cycle 9 1 true (3)
theorem kid02_part840_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid02_part840) = true := by rfl

def kid02_part744 : Audit := .split 9 (5,false) (byMove [(kid02_part745),(kid02_part746),(kid02_part747),(kid02_part748),(kid02_part749),(kid02_part774),(kid02_part775),(kid02_part776),(kid02_part777),(kid02_part778),(kid02_part779),(kid02_part780),(kid02_part781),(kid02_part782),(kid02_part783),(kid02_part784),(kid02_part785),(kid02_part810),(kid02_part811),(kid02_part812),(kid02_part813),(kid02_part814),(kid02_part815),(kid02_part840)])

theorem kid02_part744_checked : zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (kid02_part744) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid02_part745),(kid02_part746),(kid02_part747),(kid02_part748),(kid02_part749),(kid02_part774),(kid02_part775),(kid02_part776),(kid02_part777),(kid02_part778),(kid02_part779),(kid02_part780),(kid02_part781),(kid02_part782),(kid02_part783),(kid02_part784),(kid02_part785),(kid02_part810),(kid02_part811),(kid02_part812),(kid02_part813),(kid02_part814),(kid02_part815),(kid02_part840)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part745_checked

  · exact kid02_part775_checked

  · exact kid02_part781_checked

  · exact kid02_part811_checked

  · exact kid02_part746_checked

  · exact kid02_part776_checked

  · exact kid02_part782_checked

  · exact kid02_part812_checked

  · exact kid02_part747_checked

  · exact kid02_part777_checked

  · exact kid02_part783_checked

  · exact kid02_part813_checked

  · exact kid02_part748_checked

  · exact kid02_part778_checked

  · exact kid02_part784_checked

  · exact kid02_part814_checked

  · exact kid02_part749_checked

  · exact kid02_part779_checked

  · exact kid02_part785_checked

  · exact kid02_part815_checked

  · exact kid02_part774_checked

  · exact kid02_part780_checked

  · exact kid02_part810_checked

  · exact kid02_part840_checked

def kid02 : Audit := .split 8 (2,true) (byMove [(kid02_part1),(kid02_part2),(kid02_part3),(kid02_part4),(kid02_part5),(kid02_part102),(kid02_part199),(kid02_part200),(kid02_part201),(kid02_part202),(kid02_part203),(kid02_part300),(kid02_part397),(kid02_part398),(kid02_part399),(kid02_part400),(kid02_part401),(kid02_part522),(kid02_part643),(kid02_part644),(kid02_part645),(kid02_part646),(kid02_part647),(kid02_part744)])

theorem check02 : zipCheck 175 (child39 ⟨false,false,2⟩) (kid02) = true := by

  change (zipQueryOK 175 (child39 ⟨false,false,2⟩) 8 (2,true) && allMoves (fun mv => zipCheck 175 (refine (child39 ⟨false,false,2⟩) (2,true) (some mv)) (byMove [(kid02_part1),(kid02_part2),(kid02_part3),(kid02_part4),(kid02_part5),(kid02_part102),(kid02_part199),(kid02_part200),(kid02_part201),(kid02_part202),(kid02_part203),(kid02_part300),(kid02_part397),(kid02_part398),(kid02_part399),(kid02_part400),(kid02_part401),(kid02_part522),(kid02_part643),(kid02_part644),(kid02_part645),(kid02_part646),(kid02_part647),(kid02_part744)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid02_part1_checked

  · exact kid02_part199_checked

  · exact kid02_part397_checked

  · exact kid02_part643_checked

  · exact kid02_part2_checked

  · exact kid02_part200_checked

  · exact kid02_part398_checked

  · exact kid02_part644_checked

  · exact kid02_part3_checked

  · exact kid02_part201_checked

  · exact kid02_part399_checked

  · exact kid02_part645_checked

  · exact kid02_part4_checked

  · exact kid02_part202_checked

  · exact kid02_part400_checked

  · exact kid02_part646_checked

  · exact kid02_part5_checked

  · exact kid02_part203_checked

  · exact kid02_part401_checked

  · exact kid02_part647_checked

  · exact kid02_part102_checked

  · exact kid02_part300_checked

  · exact kid02_part522_checked

  · exact kid02_part744_checked

end BB6.Agent11Raw39
