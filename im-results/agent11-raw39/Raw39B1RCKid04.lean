import Raw39B1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid04_part1 : Audit := .cycle 0 9 true (0)
theorem kid04_part1_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,0⟩)) (kid04_part1) = true := by rfl

def kid04_part2 : Audit := .cycle 1 8 true (1)
theorem kid04_part2_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,1⟩)) (kid04_part2) = true := by rfl

def kid04_part3 : Audit := .cycle 17 1 false (1)
theorem kid04_part3_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,2⟩)) (kid04_part3) = true := by rfl

def kid04_part4 : Audit := .cycle 19 1 false (1)
theorem kid04_part4_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,3⟩)) (kid04_part4) = true := by rfl

def kid04_part6 : Audit := .cycle 0 19 false (3)
theorem kid04_part6_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part6) = true := by rfl

def kid04_part7 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 false (3),
.cycle 11 9 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 9 false (0),
.split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 12 9 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 9 false (-1),
.cycle 11 1 false (-1),
.cycle 0 12 true (-1),
.cycle 12 9 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 9 false (1),
.cycle 11 1 true (-1),
.last 14 (5,true),
.cycle 13 9 false (-1),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 1 40 false (3),
.cycle 11 1 false (-1),
.last 23 (5,true),
.cycle 1 11 false (3),
.cycle 12 9 false (1),
.cycle 15 9 false (2),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
]),
.cycle 0 11 true (0),
.cycle 11 9 false (3),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 9 false (2),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 12 9 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 9 false (1),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 12 9 false (4),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 9 false (3),
.cycle 11 1 true (1),
.cycle 10 3 true (0),
.cycle 13 9 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 0 16 true (-1),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 12 9 false (3),
.cycle 15 9 false (4),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
]),
.cycle 13 9 false (0),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 0 15 true (-2),
.split 11 (5,false) (byMove [
.cycle 16 9 false (-2),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 9 false (-1),
.cycle 11 1 false (-1),
.cycle 13 9 false (2),
.cycle 10 2 true (-1),
.cycle 13 9 false (0),
.cycle 0 13 true (-1),
.cycle 12 9 false (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 13 9 false (-1),
.cycle 15 9 false (2),
.cycle 12 1 false (-2),
.cycle 1 33 false (3),
.cycle 11 1 false (-1),
.cycle 2 11 false (3),
.last 13 (5,true),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.cycle 13 9 false (-1),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 11 9 false (2),
.cycle 14 9 false (3),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 13 9 false (2),
.cycle 10 2 true (0),
.cycle 13 9 false (0),
.cycle 0 13 true (0),
.cycle 12 9 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 20 true (0),
.cycle 14 9 false (2),
.cycle 12 9 false (2),
.cycle 1 12 true (0),
.cycle 11 1 true (1),
.cycle 12 9 false (1),
.last 13 (5,true),
.cycle 13 9 false (0),
.cycle 14 9 false (3),
.cycle 12 9 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 22 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid04_part7_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part7) = true := by rfl

def kid04_part8 : Audit := .cycle 13 1 false (-1)
theorem kid04_part8_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part8) = true := by rfl

def kid04_part9 : Audit := .cycle 0 11 true (0)
theorem kid04_part9_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part9) = true := by rfl

def kid04_part10 : Audit := .cycle 11 1 false (-1)
theorem kid04_part10_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part10) = true := by rfl

def kid04_part12 : Audit := .cycle 0 11 false (3)
theorem kid04_part12_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part12) = true := by rfl

def kid04_part13 : Audit := .split 20 (5,false) (byMove [
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
.last 22 (1,true),
.cycle 17 5 false (1),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 32 (1,true),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 12 12 true (-2),
.cycle 9 12 false (1),
.cycle 20 1 true (-2)
])
theorem kid04_part13_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part13) = true := by rfl

def kid04_part14 : Audit := .cycle 12 1 false (0)
theorem kid04_part14_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part14) = true := by rfl

def kid04_part15 : Audit := .cycle 11 1 false (-1)
theorem kid04_part15_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part15) = true := by rfl

def kid04_part16 : Audit := .split 12 (5,false) (byMove [
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
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 14 false (2),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 11 12 true (-2),
.cycle 9 4 false (1),
.cycle 12 1 true (-2)
])
theorem kid04_part16_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part16) = true := by rfl

def kid04_part17 : Audit := .split 11 (5,false) (byMove [
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
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 10 13 false (3),
.cycle 1 11 false (3),
.cycle 11 9 false (1),
.cycle 11 12 true (-1),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
])
theorem kid04_part17_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part17) = true := by rfl

def kid04_part18 : Audit := .cycle 0 11 true (0)
theorem kid04_part18_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part18) = true := by rfl

def kid04_part19 : Audit := .split 20 (5,false) (byMove [
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
.last 22 (1,true),
.cycle 17 5 false (3),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 12 9 false (3),
.cycle 12 12 true (0),
.cycle 9 12 true (0),
.cycle 20 1 true (0)
])
theorem kid04_part19_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part19) = true := by rfl

def kid04_part20 : Audit := .cycle 12 1 false (2)
theorem kid04_part20_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part20) = true := by rfl

def kid04_part21 : Audit := .cycle 11 1 false (1)
theorem kid04_part21_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part21) = true := by rfl

def kid04_part22 : Audit := .split 12 (5,false) (byMove [
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
.last 14 (1,true),
.cycle 11 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 11 9 false (2),
.cycle 11 12 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (0)
])
theorem kid04_part22_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part22) = true := by rfl

def kid04_part23 : Audit := .split 11 (5,false) (byMove [
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
.last 13 (1,true),
.cycle 11 5 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 11 9 false (3),
.cycle 11 12 true (1),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid04_part23_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part23) = true := by rfl

def kid04_part24 : Audit := .split 12 (1,true) (byMove [
.last 22 (5,false),
.last 23 (5,false),
.last 15 (5,false),
.cycle 0 14 true (-1),
.last 15 (5,false),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.last 22 (5,false),
.last 22 (5,false),
.last 20 (5,false),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 15 (5,false),
.cycle 10 3 false (0),
.last 29 (5,false),
.last 27 (5,false),
.cycle 2 11 false (3),
.last 24 (5,false),
.last 19 (5,false),
.last 13 (5,false)
])
theorem kid04_part24_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part24) = true := by rfl

def kid04_part25 : Audit := .split 15 (5,false) (byMove [
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
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 0 18 false (3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 27 (1,true),
.cycle 1 15 false (3),
.cycle 12 9 false (0),
.cycle 12 12 true (-3),
.cycle 9 7 false (1),
.cycle 15 1 true (-3)
])
theorem kid04_part25_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part25) = true := by rfl

def kid04_part26 : Audit := .cycle 0 13 true (-1)
theorem kid04_part26_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part26) = true := by rfl

def kid04_part27 : Audit := .cycle 11 1 false (-1)
theorem kid04_part27_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part27) = true := by rfl

def kid04_part28 : Audit := .split 12 (5,false) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M30.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M30.never m hm),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 14 (1,true),
.cycle 14 10 true (-3),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.last 14 (1,true),
.cycle 11 5 false (-1),
.last 16 (1,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 14 (1,true),
.cycle 1 18 false (3),
.cycle 0 15 true (-2),
.cycle 13 12 true (-3),
.cycle 9 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 0, 64],64⟩
])
theorem kid04_part28_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part28) = true := by rfl

def kid04_part29 : Audit := .split 11 (5,false) (byMove [
.cycle 0 19 false (3),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 22 true (-1),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (-1),
.cycle 13 2 true (-2),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 0 26 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 2 11 false (3),
.last 12 (1,true),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.cycle 9 7 false (1),
.cycle 10 3 false (0)
])
theorem kid04_part29_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part29) = true := by rfl

def kid04_part30 : Audit := .cycle 0 11 true (0)
theorem kid04_part30_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part30) = true := by rfl

def kid04_part31 : Audit := .cycle 1 10 true (0)
theorem kid04_part31_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part31) = true := by rfl

def kid04_part32 : Audit := .split 19 (5,false) (byMove [
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
.last 21 (1,true),
.cycle 16 5 false (2),
.cycle 0 22 true (-2),
.cycle 20 1 false (-2),
.cycle 18 2 false (0),
.cycle 19 1 false (-1),
.cycle 2 29 false (3),
.cycle 1 19 false (3),
.cycle 11 9 false (2),
.cycle 11 12 true (-1),
.cycle 9 11 false (2),
.cycle 19 1 true (-1)
])
theorem kid04_part32_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part32) = true := by rfl

def kid04_part33 : Audit := .split 22 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 14 10 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 0 23 true (0),
.cycle 14 10 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 21 2 true (0),
.cycle 22 1 true (0),
.last 24 (1,true),
.cycle 19 5 false (3),
.cycle 0 25 true (-1),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 14 9 false (3),
.cycle 11 12 true (0),
.cycle 9 14 true (0),
.cycle 22 1 true (0)
])
theorem kid04_part33_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part33) = true := by rfl

def kid04_part34 : Audit := .cycle 9 2 true (0)
theorem kid04_part34_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part34) = true := by rfl

def kid04_part35 : Audit := .split 11 (5,false) (byMove [
.cycle 0 22 false (3),
.last 12 (1,true),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 13 2 false (-1),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.last 18 (1,true),
.last 12 (1,true),
.cycle 0 26 false (3),
.cycle 23 1 false (-1),
.cycle 13 2 false (-1),
.cycle 10 3 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 11 12 true (1),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid04_part35_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part35) = true := by rfl

def kid04_part11 : Audit := .split 10 (5,true) (byMove [(kid04_part12),(kid04_part13),(kid04_part14),(kid04_part15),(kid04_part16),(kid04_part17),(kid04_part18),(kid04_part19),(kid04_part20),(kid04_part21),(kid04_part22),(kid04_part23),(kid04_part24),(kid04_part25),(kid04_part26),(kid04_part27),(kid04_part28),(kid04_part29),(kid04_part30),(kid04_part31),(kid04_part32),(kid04_part33),(kid04_part34),(kid04_part35)])

theorem kid04_part11_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part11) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part12),(kid04_part13),(kid04_part14),(kid04_part15),(kid04_part16),(kid04_part17),(kid04_part18),(kid04_part19),(kid04_part20),(kid04_part21),(kid04_part22),(kid04_part23),(kid04_part24),(kid04_part25),(kid04_part26),(kid04_part27),(kid04_part28),(kid04_part29),(kid04_part30),(kid04_part31),(kid04_part32),(kid04_part33),(kid04_part34),(kid04_part35)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part12_checked

  · exact kid04_part18_checked

  · exact kid04_part24_checked

  · exact kid04_part30_checked

  · exact kid04_part13_checked

  · exact kid04_part19_checked

  · exact kid04_part25_checked

  · exact kid04_part31_checked

  · exact kid04_part14_checked

  · exact kid04_part20_checked

  · exact kid04_part26_checked

  · exact kid04_part32_checked

  · exact kid04_part15_checked

  · exact kid04_part21_checked

  · exact kid04_part27_checked

  · exact kid04_part33_checked

  · exact kid04_part16_checked

  · exact kid04_part22_checked

  · exact kid04_part28_checked

  · exact kid04_part34_checked

  · exact kid04_part17_checked

  · exact kid04_part23_checked

  · exact kid04_part29_checked

  · exact kid04_part35_checked

def kid04_part36 : Audit := .cycle 0 10 true (0)
theorem kid04_part36_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part36) = true := by rfl

def kid04_part37 : Audit := .cycle 1 9 true (1)
theorem kid04_part37_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part37) = true := by rfl

def kid04_part38 : Audit := .cycle 20 1 false (2)
theorem kid04_part38_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part38) = true := by rfl

def kid04_part39 : Audit := .cycle 17 1 false (1)
theorem kid04_part39_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part39) = true := by rfl

def kid04_part40 : Audit := .cycle 9 1 true (1)
theorem kid04_part40_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part40) = true := by rfl

def kid04_part41 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
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
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 9 4 true (0),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 9 2 true (1),
.cycle 10 1 true (2),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 15 5 false (0),
.cycle 0 14 true (0),
.cycle 14 5 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 9 4 true (1),
.cycle 10 3 true (1),
.cycle 16 7 false (0),
.cycle 13 8 false (1),
.cycle 15 5 false (0),
.cycle 2 13 true (1),
.cycle 14 5 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (1),
.cycle 17 9 false (1)
]),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 9 4 true (1),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 9 4 true (1),
.cycle 10 3 true (1),
.last 14 (1,true),
.cycle 16 7 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩
]),
.split 12 (5,true) (byMove [
.cycle 19 1 false (-1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (1),
.cycle 23 1 false (3),
.cycle 15 1 false (1),
.cycle 15 1 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.cycle 16 1 false (0),
.cycle 13 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2)
])
theorem kid04_part41_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part41) = true := by rfl

def kid04_part42 : Audit := .split 15 (1,true) (byMove [
.cycle 10 11 false (1),
.cycle 10 12 false (1),
.cycle 13 4 false (-1),
.cycle 0 17 false (3),
.cycle 12 4 false (0),
.split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.last 17 (5,false),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 12 18 false (2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.last 17 (5,false)
]),
.cycle 6 20 false (3),
.cycle 10 11 true (-2),
.cycle 10 11 false (1),
.cycle 10 9 false (1),
.cycle 13 3 true (-2),
.split 16 (5,false) (byMove [
.cycle 12 18 false (2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 10 12 true (-2),
.cycle 10 27 true (-3),
.cycle 10 11 false (1),
.cycle 13 4 true (-2),
.cycle 16 1 true (0),
.cycle 14 3 true (-2),
.cycle 12 8 false (0),
.cycle 0 19 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.last 18 (5,true),
.cycle 8 22 false (4),
.cycle 6 20 false (3),
.cycle 10 11 true (-2),
.cycle 10 14 true (-2),
.cycle 6 12 false (3),
.cycle 16 1 true (0)
]),
.cycle 10 6 false (1),
.cycle 11 7 false (1),
.cycle 13 4 false (-1),
.cycle 10 12 true (-2),
.cycle 12 4 false (0),
.split 16 (5,true) (byMove [
.cycle 12 9 false (0),
.last 38 (5,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 10 12 true (-2),
.last 18 (5,false),
.cycle 13 5 false (-1),
.cycle 0 18 true (-2),
.cycle 12 5 false (0),
.last 18 (5,false),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 14 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 2 16 false (3),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 6 22 false (3),
.cycle 12 6 false (0),
.last 18 (5,false)
]),
.cycle 12 18 false (3),
.cycle 12 16 false (2),
.cycle 2 14 false (3),
.cycle 10 13 true (-2),
.cycle 12 8 false (0),
.split 16 (5,false) (byMove [
.cycle 2 16 false (3),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 6 22 false (3),
.cycle 12 6 false (0),
.last 17 (5,true),
.cycle 12 22 false (4),
.cycle 10 12 true (-2),
.cycle 3 16 false (3),
.cycle 3 14 false (3),
.cycle 13 4 true (-2),
.cycle 16 1 true (0),
.cycle 12 8 false (0),
.last 18 (5,true),
.cycle 11 6 false (1),
.cycle 10 13 true (-2),
.cycle 12 6 false (0),
.last 17 (5,true),
.cycle 12 20 false (4),
.cycle 12 18 false (3),
.cycle 12 16 false (2),
.cycle 10 14 true (-2),
.cycle 12 10 false (1),
.cycle 16 1 true (0)
])
])
theorem kid04_part42_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part42) = true := by rfl

def kid04_part43 : Audit := .split 10 (1,true) (byMove [
.cycle 15 4 false (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 4 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 14 (5,true),
.cycle 12 4 false (1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 13 (5,true),
.last 14 (5,true),
.cycle 12 4 false (-1),
.last 16 (5,true),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 14 (5,true),
.cycle 15 4 false (-1),
.cycle 0 14 true (-1),
.cycle 15 4 false (1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 17 4 false (3),
.cycle 18 4 false (4),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 11 4 false (1),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 18 4 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 18 4 false (4),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 4 false (2),
.last 12 (5,false),
.last 14 (5,false),
.cycle 12 4 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 17 4 false (3),
.cycle 20 4 false (4),
.cycle 9 3 true (0),
.last 12 (5,false)
]),
.cycle 14 4 false (0),
.cycle 11 4 false (0),
.cycle 19 4 false (3),
.cycle 11 1 false (-1),
.cycle 11 4 false (-1),
.split 11 (5,false) (byMove [
.cycle 16 4 false (-2),
.cycle 7 18 false (3),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 13 4 false (-1),
.cycle 19 4 false (3),
.cycle 12 4 false (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 15 4 false (-1),
.last 13 (5,true),
.cycle 12 4 false (0),
.cycle 25 4 false (-1),
.cycle 13 4 false (-1),
.last 12 (5,true)
]),
.cycle 2 10 true (0),
.cycle 1 11 true (0),
.cycle 11 4 false (1),
.cycle 0 12 true (0),
.cycle 12 4 false (0),
.split 11 (5,true) (byMove [
.cycle 18 4 false (2),
.last 13 (5,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 24 4 false (0),
.cycle 18 4 false (2),
.cycle 16 4 false (2),
.cycle 16 4 false (0),
.last 12 (5,false),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.cycle 13 4 false (-1),
.cycle 19 4 false (3),
.cycle 12 4 false (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 26 4 false (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
])
theorem kid04_part43_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part43) = true := by rfl

def kid04_part44 : Audit := .split 15 (1,true) (byMove [
.cycle 0 27 true (-2),
.cycle 0 28 true (-2),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.cycle 0 20 true (-2),
.split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 0 28 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 20 true (-2),
.last 17 (5,false),
.cycle 0 17 true (-2),
.cycle 0 28 true (-2),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 0 20 true (-2),
.last 17 (5,false),
.cycle 14 3 false (1),
.cycle 0 23 false (3),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 0 31 true (-2),
.last 17 (5,false),
.cycle 0 40 true (-2),
.cycle 1 16 true (-2),
.cycle 0 27 true (-2),
.cycle 0 30 true (-2),
.cycle 9 8 true (-2),
.last 17 (5,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 1, 15, 1, 15, 64, 64],96⟩,
.cycle 0 27 true (-2),
.cycle 0 35 true (-2),
.cycle 0 25 true (-2),
.cycle 0 19 true (-2),
.split 16 (5,false) (byMove [
.cycle 0 40 true (-2),
.cycle 1 16 true (-2),
.cycle 0 27 true (-2),
.cycle 0 30 true (-2),
.cycle 9 8 true (-2),
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 0 28 true (-2),
.cycle 0 41 true (-2),
.cycle 0 35 true (-2),
.cycle 0 20 true (-2),
.cycle 16 1 true (2),
.cycle 14 3 true (0),
.cycle 0 24 true (-2),
.cycle 0 19 true (-2),
.cycle 0 25 true (-2),
.last 24 (5,true),
.last 18 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 426369, 164225, 64, 128, 256, 32768, 260, 164225, 64, 2, 4, 8, 33153, 1, 1, 262144],[256, 32, 33153, 1, 33153, 262144, 256, 131072, 33153, 4096, 33153, 262144, 4, 32, 33153, 1, 33153, 262144, 262144],287244⟩,
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 426403, 164259, 128, 128, 256, 32768, 260, 164259, 128, 2, 4, 8, 33154, 1, 2, 262144],[256, 32, 33154, 1, 33154, 262144, 256, 131072, 33154, 4096, 33154, 262144, 4, 32, 33154, 1, 33154, 262144, 262144],287244⟩,
.cycle 0 27 true (-2),
.cycle 0 30 true (-2),
.cycle 8 20 true (-2),
.cycle 16 1 true (2)
]),
.cycle 0 22 true (-2),
.cycle 0 31 false (3),
.cycle 10 6 true (-2),
.cycle 0 28 true (-2),
.cycle 11 6 true (-2),
.split 16 (5,true) (byMove [
.cycle 0 25 false (3),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 6 true (-2),
.last 17 (5,false),
.cycle 0 28 true (-2),
.last 18 (5,false),
.cycle 0 21 true (-2),
.cycle 0 18 true (-2),
.cycle 0 21 true (-2),
.last 18 (5,false),
.cycle 14 3 false (1),
.cycle 0 31 false (3),
.cycle 0 30 true (-2),
.cycle 17 1 false (-1),
.cycle 0 26 true (-2),
.last 17 (5,false),
.cycle 2 16 true (-2),
.cycle 15 2 true (0),
.cycle 0 22 true (-2),
.far true 1 ⟨0,[0, 0],[28, 28, 8, 8, 4, 64, 64],[28, 32, 16, 12, 16, 28, 64],96⟩,
.cycle 0 22 true (-2),
.last 18 (5,false)
]),
.cycle 0 36 true (-2),
.cycle 0 38 true (-2),
.cycle 2 14 true (-2),
.cycle 0 29 true (-2),
.cycle 0 30 true (-2),
.split 16 (5,false) (byMove [
.cycle 2 16 true (-2),
.cycle 15 2 true (1),
.cycle 0 22 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 297347, 35203, 295298, 128, 256, 32768, 260, 35203, 130, 2, 4, 8, 33154, 1, 32776, 262144],[256, 2048, 33154, 1, 33154, 262144, 256, 2048, 33154, 4096, 33154, 262144, 4, 32, 33154, 1, 33154, 262144, 262144],418348⟩,
.cycle 0 22 true (-2),
.last 17 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 297345, 1, 1, 128, 256, 32768, 256, 35201, 4096, 128, 256, 8, 33152, 1, 1, 262144],[256, 2048, 128, 1, 128, 262144, 256, 2048, 33152, 4096, 33152, 262144, 256, 2048, 37248, 1, 37248, 262144, 262144],278540⟩,
.cycle 0 28 true (-2),
.cycle 0 35 true (-2),
.cycle 3 14 true (-2),
.cycle 0 20 true (-2),
.cycle 16 1 true (2),
.cycle 0 24 true (-2),
.last 18 (5,true),
.cycle 0 30 true (-2),
.cycle 0 29 true (-2),
.cycle 0 30 true (-2),
.last 17 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 297409, 35265, 64, 128, 256, 32768, 260, 35265, 64, 2, 4, 8, 33216, 1, 1, 262144],[256, 2048, 33216, 1, 33216, 262144, 256, 2048, 33216, 4096, 33216, 262144, 4, 32, 33216, 1, 33216, 262144, 262144],287244⟩,
.cycle 0 36 true (-2),
.cycle 0 38 true (-2),
.cycle 0 30 true (-2),
.cycle 0 28 true (-2),
.cycle 16 1 true (2)
])
])
theorem kid04_part44_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part44) = true := by rfl

def kid04_part45 : Audit := .cycle 20 1 false (0)
theorem kid04_part45_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part45) = true := by rfl

def kid04_part46 : Audit := .cycle 11 1 false (-1)
theorem kid04_part46_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part46) = true := by rfl

def kid04_part48 : Audit := .split 17 (5,false) (byMove [
.cycle 11 7 false (1),
.cycle 8 28 false (2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 15 10 true (-3),
.last 18 (1,true),
.cycle 16 3 false (-2),
.cycle 0 19 false (3),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.last 19 (1,true),
.cycle 15 5 false (-1),
.cycle 15 12 true (-4),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 2 17 false (3),
.last 18 (1,true),
.cycle 15 4 false (-1),
.cycle 14 20 false (2),
.cycle 14 4 false (0),
.cycle 15 11 false (-1)
])
theorem kid04_part48_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part48) = true := by rfl

def kid04_part49 : Audit := .cycle 0 14 true (-1)
theorem kid04_part49_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part49) = true := by rfl

def kid04_part50 : Audit := .cycle 12 1 false (0)
theorem kid04_part50_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part50) = true := by rfl

def kid04_part51 : Audit := .cycle 11 1 false (-1)
theorem kid04_part51_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part51) = true := by rfl

def kid04_part52 : Audit := .split 12 (5,false) (byMove [
.cycle 11 7 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-2),
.last 13 (1,true),
.cycle 11 3 false (-1),
.last 15 (1,true),
.cycle 11 3 false (-1),
.cycle 10 3 false (0),
.last 14 (1,true),
.cycle 11 5 false (-1),
.far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 2, 4, 4, 4, 4, 6, 2, 4],[65536, 2048, 2097152, 512, 2048, 256, 4398046511104, 16, 274877906944, 2097152, 8388608, 1048576, 268435472, 65536, 134217728, 8589934592, 34359738368, 4294967296, 4398046511104, 268435456, 0, 134217728, 536870912, 67108864, 5258047719424, 5258047719424, 5222882607104, 134217728, 536870912, 67108864, 4398046511104, 268435456, 4398046511104, 549755813888, 2199023255552, 274877906944, 4398046511104, 268435456, 274877906944, 134217728, 536870912, 67108864, 4398046511104],[2048, 4398046511104, 16, 34359738368, 16, 16, 16, 4398046511104, 65536, 1048576, 65536, 65536, 65536, 4398046511104, 268435456, 4398046511104, 268435456, 268435456, 268435456, 4398046511104, 65536, 2048, 65536, 65536, 5258047719424, 4398046511104, 268435456, 5257779218432, 268435456, 268435456, 268435456, 4398046511104, 268435456, 34359738368, 268435456, 268435456, 268435456, 4398046511104, 65536, 536870912, 65536, 65536, 4398046511104],7928372139072⟩,
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-2),
.last 13 (1,true),
.cycle 11 4 false (-1),
.last 15 (1,true),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid04_part52_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part52) = true := by rfl

def kid04_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.last 32 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 13 (1,true),
.last 17 (1,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 3 false (0),
.cycle 14 1 true (0),
.last 13 (1,true),
.cycle 11 5 false (-1),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 9 3 false (1),
.cycle 16 1 true (-2)
])
theorem kid04_part53_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part53) = true := by rfl

def kid04_part54 : Audit := .split 20 (5,false) (byMove [
.cycle 18 7 false (2),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 11 10 true (0),
.last 21 (1,true),
.cycle 19 3 false (1),
.cycle 0 22 true (0),
.cycle 18 3 false (2),
.cycle 0 22 true (0),
.last 22 (1,true),
.cycle 17 5 false (3),
.cycle 11 12 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 2 20 true (0),
.last 21 (1,true),
.cycle 17 4 false (3),
.cycle 0 22 true (0),
.cycle 18 4 false (2),
.cycle 0 22 true (0)
])
theorem kid04_part54_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part54) = true := by rfl

def kid04_part55 : Audit := .split 11 (1,true) (byMove [
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
.last 18 (5,false),
.last 16 (5,false),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.last 20 (5,false),
.last 23 (5,false),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid04_part55_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part55) = true := by rfl

def kid04_part56 : Audit := .split 13 (5,false) (byMove [
.cycle 12 7 false (0),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 12 10 true (-1),
.last 14 (1,true),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 12 3 false (0),
.cycle 16 1 false (2),
.last 15 (1,true),
.cycle 12 5 false (0),
.cycle 12 12 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 2 13 false (3),
.last 14 (1,true),
.cycle 12 4 false (0),
.cycle 0 15 true (-1),
.cycle 12 4 false (0),
.cycle 12 11 false (2)
])
theorem kid04_part56_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part56) = true := by rfl

def kid04_part57 : Audit := .cycle 0 12 true (0)
theorem kid04_part57_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part57) = true := by rfl

def kid04_part58 : Audit := .split 13 (5,false) (byMove [
.cycle 11 7 false (1),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 10 true (-1),
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.cycle 12 3 true (-1),
.last 15 (1,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 2 13 false (3),
.last 14 (1,true),
.cycle 11 4 false (1),
.cycle 0 15 true (-1),
.cycle 11 4 false (1),
.cycle 12 3 true (-1)
])
theorem kid04_part58_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part58) = true := by rfl

def kid04_part59 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 0 13 true (0),
.last 23 (1,true),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 13 3 false (3),
.cycle 12 1 true (2),
.last 14 (1,true),
.cycle 12 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (4),
.cycle 0 26 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (2)
])
theorem kid04_part59_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part59) = true := by rfl

def kid04_part60 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (-1),
.last 23 (5,false),
.last 15 (5,false),
.cycle 0 17 true (-1),
.last 15 (5,false),
.cycle 10 3 false (0),
.last 22 (5,false),
.last 23 (5,false),
.cycle 9 5 false (1),
.cycle 0 14 true (-1),
.cycle 8 5 false (2),
.last 16 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.cycle 10 3 false (0),
.last 27 (5,false),
.last 29 (5,false),
.last 17 (5,false),
.cycle 0 14 true (-1),
.last 17 (5,false),
.last 19 (5,false)
])
theorem kid04_part60_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part60) = true := by rfl

def kid04_part61 : Audit := .split 15 (5,false) (byMove [
.cycle 13 7 false (-1),
.last 26 (1,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 10 true (-3),
.last 16 (1,true),
.cycle 14 3 false (-2),
.cycle 0 25 false (3),
.cycle 13 3 false (-1),
.cycle 10 6 false (0),
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 12 12 true (-4),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 2 15 false (3),
.last 16 (1,true),
.cycle 12 4 false (0),
.cycle 8 13 false (2),
.cycle 13 4 false (-1),
.last 17 (1,true)
])
theorem kid04_part61_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part61) = true := by rfl

def kid04_part62 : Audit := .split 22 (5,false) (byMove [
.cycle 20 7 false (2),
.cycle 0 26 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 13 10 true (0),
.last 23 (1,true),
.cycle 21 3 false (1),
.cycle 0 24 true (-1),
.cycle 20 3 false (2),
.cycle 0 26 true (-1),
.last 24 (1,true),
.cycle 19 5 false (3),
.cycle 11 12 true (-1),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 2 22 true (-1),
.last 23 (1,true),
.cycle 19 4 false (3),
.cycle 0 24 true (-1),
.cycle 20 4 false (2),
.cycle 21 4 false (1)
])
theorem kid04_part62_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part62) = true := by rfl

def kid04_part63 : Audit := .cycle 11 1 false (-1)
theorem kid04_part63_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part63) = true := by rfl

def kid04_part64 : Audit := .split 12 (5,false) (byMove [
.cycle 11 7 false (-1),
.last 21 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 13 10 true (-3),
.last 13 (1,true),
.cycle 11 3 false (-1),
.cycle 0 20 true (-2),
.cycle 11 3 false (-1),
.cycle 10 3 false (0),
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 14 12 true (-4),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 2 18 false (3),
.last 13 (1,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid04_part64_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part64) = true := by rfl

def kid04_part65 : Audit := .split 11 (5,false) (byMove [
.cycle 11 7 false (0),
.cycle 0 28 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 12 10 true (-2),
.last 12 (1,true),
.cycle 11 3 false (0),
.cycle 0 24 true (-1),
.cycle 11 3 false (0),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 13 12 true (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 2 17 false (3),
.last 12 (1,true),
.cycle 11 4 false (0),
.cycle 0 24 true (-1),
.cycle 11 4 false (0),
.cycle 10 3 false (0)
])
theorem kid04_part65_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part65) = true := by rfl

def kid04_part66 : Audit := .cycle 2 10 true (0)
theorem kid04_part66_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part66) = true := by rfl

def kid04_part67 : Audit := .split 11 (1,true) (byMove [
.last 21 (5,false),
.last 22 (5,false),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 1 12 true (0),
.cycle 0 12 true (0),
.last 21 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.last 22 (5,false),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.last 23 (5,false),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid04_part67_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part67) = true := by rfl

def kid04_part68 : Audit := .split 14 (5,false) (byMove [
.cycle 12 7 false (0),
.last 33 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 10 true (-2),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 16 true (-2),
.cycle 12 3 false (0),
.cycle 11 10 true (-2),
.last 16 (1,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 2 14 false (3),
.last 15 (1,true),
.cycle 11 4 false (1),
.cycle 7 20 false (3),
.cycle 12 4 false (0),
.cycle 2 14 false (3)
])
theorem kid04_part68_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part68) = true := by rfl

def kid04_part69 : Audit := .cycle 0 12 true (0)
theorem kid04_part69_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part69) = true := by rfl

def kid04_part70 : Audit := .split 14 (5,false) (byMove [
.cycle 11 7 false (1),
.last 33 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 10 true (-2),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 16 true (-2),
.cycle 12 3 false (0),
.cycle 9 7 false (1),
.last 16 (1,true),
.cycle 12 5 false (0),
.cycle 12 12 true (-3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 2 14 false (3),
.last 15 (1,true),
.cycle 12 4 false (0),
.cycle 8 20 false (3),
.cycle 11 4 false (1),
.cycle 11 8 false (1)
])
theorem kid04_part70_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part70) = true := by rfl

def kid04_part71 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 15 2 false (-1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.last 23 (1,true),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 8 7 true (0),
.cycle 12 1 true (2),
.last 20 (1,true),
.last 13 (1,true),
.cycle 13 12 true (-3),
.cycle 30 1 false (-2),
.cycle 15 2 false (-1),
.cycle 10 3 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 26 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (2)
])
theorem kid04_part71_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part71) = true := by rfl

def kid04_part47 : Audit := .split 10 (5,true) (byMove [(kid04_part48),(kid04_part49),(kid04_part50),(kid04_part51),(kid04_part52),(kid04_part53),(kid04_part54),(kid04_part55),(kid04_part56),(kid04_part57),(kid04_part58),(kid04_part59),(kid04_part60),(kid04_part61),(kid04_part62),(kid04_part63),(kid04_part64),(kid04_part65),(kid04_part66),(kid04_part67),(kid04_part68),(kid04_part69),(kid04_part70),(kid04_part71)])

theorem kid04_part47_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part47) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part48),(kid04_part49),(kid04_part50),(kid04_part51),(kid04_part52),(kid04_part53),(kid04_part54),(kid04_part55),(kid04_part56),(kid04_part57),(kid04_part58),(kid04_part59),(kid04_part60),(kid04_part61),(kid04_part62),(kid04_part63),(kid04_part64),(kid04_part65),(kid04_part66),(kid04_part67),(kid04_part68),(kid04_part69),(kid04_part70),(kid04_part71)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part48_checked

  · exact kid04_part54_checked

  · exact kid04_part60_checked

  · exact kid04_part66_checked

  · exact kid04_part49_checked

  · exact kid04_part55_checked

  · exact kid04_part61_checked

  · exact kid04_part67_checked

  · exact kid04_part50_checked

  · exact kid04_part56_checked

  · exact kid04_part62_checked

  · exact kid04_part68_checked

  · exact kid04_part51_checked

  · exact kid04_part57_checked

  · exact kid04_part63_checked

  · exact kid04_part69_checked

  · exact kid04_part52_checked

  · exact kid04_part58_checked

  · exact kid04_part64_checked

  · exact kid04_part70_checked

  · exact kid04_part53_checked

  · exact kid04_part59_checked

  · exact kid04_part65_checked

  · exact kid04_part71_checked

def kid04_part72 : Audit := .cycle 0 10 true (0)
theorem kid04_part72_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part72) = true := by rfl

def kid04_part73 : Audit := .cycle 1 9 true (1)
theorem kid04_part73_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part73) = true := by rfl

def kid04_part74 : Audit := .cycle 2 8 true (1)
theorem kid04_part74_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part74) = true := by rfl

def kid04_part75 : Audit := .cycle 2 11 true (1)
theorem kid04_part75_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part75) = true := by rfl

def kid04_part76 : Audit := .cycle 9 1 true (1)
theorem kid04_part76_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part76) = true := by rfl

def kid04_part77 : Audit := .split 10 (5,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 1 12 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.cycle 11 8 true (-2),
.cycle 24 1 false (0),
.last 17 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
]),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 12 3 false (0),
.split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 15 1 false (1),
.last 19 (1,true),
.last 12 (1,true),
.last 19 (1,true),
.cycle 24 1 false (0),
.cycle 11 6 false (1),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 3 8 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2),
.cycle 14 5 false (0),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 13 3 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.cycle 0 29 true (-2),
.cycle 19 1 false (-1),
.last 17 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 5 false (1),
.last 12 (5,true)
]),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.cycle 12 3 false (0),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 17 1 false (-1),
.last 14 (1,true),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 20 1 false (4),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 29 true (-2),
.cycle 19 1 false (-1),
.cycle 11 6 false (1),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 5 false (1),
.cycle 10 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2)
])
theorem kid04_part77_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part77) = true := by rfl

def kid04_part5 : Audit := .split 9 (4,false) (byMove [(kid04_part6),(kid04_part7),(kid04_part8),(kid04_part9),(kid04_part10),(kid04_part11),(kid04_part36),(kid04_part37),(kid04_part38),(kid04_part39),(kid04_part40),(kid04_part41),(kid04_part42),(kid04_part43),(kid04_part44),(kid04_part45),(kid04_part46),(kid04_part47),(kid04_part72),(kid04_part73),(kid04_part74),(kid04_part75),(kid04_part76),(kid04_part77)])

theorem kid04_part5_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (kid04_part5) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid04_part6),(kid04_part7),(kid04_part8),(kid04_part9),(kid04_part10),(kid04_part11),(kid04_part36),(kid04_part37),(kid04_part38),(kid04_part39),(kid04_part40),(kid04_part41),(kid04_part42),(kid04_part43),(kid04_part44),(kid04_part45),(kid04_part46),(kid04_part47),(kid04_part72),(kid04_part73),(kid04_part74),(kid04_part75),(kid04_part76),(kid04_part77)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part6_checked

  · exact kid04_part36_checked

  · exact kid04_part42_checked

  · exact kid04_part72_checked

  · exact kid04_part7_checked

  · exact kid04_part37_checked

  · exact kid04_part43_checked

  · exact kid04_part73_checked

  · exact kid04_part8_checked

  · exact kid04_part38_checked

  · exact kid04_part44_checked

  · exact kid04_part74_checked

  · exact kid04_part9_checked

  · exact kid04_part39_checked

  · exact kid04_part45_checked

  · exact kid04_part75_checked

  · exact kid04_part10_checked

  · exact kid04_part40_checked

  · exact kid04_part46_checked

  · exact kid04_part76_checked

  · exact kid04_part11_checked

  · exact kid04_part41_checked

  · exact kid04_part47_checked

  · exact kid04_part77_checked

def kid04_part79 : Audit := .cycle 0 19 false (3)
theorem kid04_part79_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part79) = true := by rfl

def kid04_part80 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 false (3),
.cycle 11 9 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 12 9 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 9 false (-1),
.cycle 0 12 true (-1),
.cycle 12 9 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 12 9 false (1),
.cycle 14 9 false (-2),
.cycle 13 9 false (-1),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 39 (5,true),
.cycle 23 9 false (-1),
.cycle 1 11 false (3),
.cycle 12 9 false (1),
.cycle 15 9 false (2),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
]),
.cycle 11 9 false (0),
.cycle 0 11 true (0),
.cycle 11 9 false (3),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 12 9 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 9 false (1),
.cycle 0 12 true (0),
.cycle 12 9 false (4),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 12 9 false (3),
.cycle 10 3 true (0),
.cycle 13 9 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 16 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 12 9 false (3),
.cycle 15 9 false (4),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 11 9 false (2),
.cycle 13 9 false (0),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 9 false (-1),
.cycle 13 9 false (2),
.cycle 10 2 true (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (-1),
.cycle 12 9 false (0),
.last 12 (5,true),
.cycle 14 9 false (-2),
.cycle 13 9 false (-1),
.cycle 15 9 false (2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 1 33 false (3),
.cycle 2 11 false (3),
.cycle 13 9 false (-1),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 15 true (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 11 9 false (2),
.cycle 14 9 false (3),
.split 11 (4,false) (byMove [
.cycle 13 9 false (2),
.cycle 10 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 12 9 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 20 true (0),
.cycle 14 9 false (2),
.cycle 12 9 false (2),
.cycle 11 1 true (1),
.cycle 1 12 true (0),
.cycle 12 9 false (1),
.last 14 (5,true),
.cycle 19 9 false (1),
.cycle 14 9 false (3),
.cycle 12 9 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 22 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid04_part80_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part80) = true := by rfl

def kid04_part81 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 12 true (-1),
.cycle 22 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 14 1 false (0),
.split 13 (1,true) (byMove [
.cycle 24 1 false (-2),
.cycle 25 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 15 false (3),
.cycle 17 1 false (-3),
.last 14 (5,true),
.cycle 31 1 false (-3),
.cycle 32 1 false (-2),
.cycle 24 1 false (-2),
.cycle 22 1 false (-2),
.cycle 11 3 true (-2),
.cycle 24 1 false (-2),
.cycle 19 1 false (-3),
.cycle 20 1 false (-4),
.cycle 10 4 false (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (-3),
.last 14 (5,true),
.last 26 (5,true),
.cycle 27 1 false (-3),
.cycle 2 12 false (3),
.cycle 34 1 false (-2),
.last 18 (5,true),
.cycle 19 1 false (-3)
]),
.cycle 17 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 26 1 false (-2),
.cycle 1 11 false (3),
.cycle 21 1 false (-1),
.cycle 24 1 false (0),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
])
theorem kid04_part81_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part81) = true := by rfl

def kid04_part82 : Audit := .cycle 0 11 true (0)
theorem kid04_part82_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part82) = true := by rfl

def kid04_part83 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 10 10 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 13 false (3),
.cycle 10 10 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 true (-2),
.cycle 11 2 true (-2),
.split 14 (1,true) (byMove [
.cycle 10 12 false (0),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.cycle 0 16 false (3),
.cycle 10 5 false (0),
.last 15 (5,true),
.cycle 8 17 false (2),
.cycle 10 17 false (1),
.cycle 10 12 false (0),
.cycle 10 10 false (0),
.cycle 12 3 true (-3),
.cycle 10 9 false (0),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.cycle 10 13 false (0),
.cycle 10 5 false (0),
.last 15 (5,true),
.last 26 (5,true),
.last 25 (5,true),
.cycle 2 13 false (3),
.cycle 10 19 false (1),
.last 19 (5,true),
.last 17 (5,true)
]),
.cycle 10 5 false (0),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.split 24 (5,true) (byMove [
.cycle 0 25 false (3),
.cycle 10 22 false (2),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.cycle 12 13 false (2),
.cycle 11 14 false (2),
.cycle 0 25 false (3),
.cycle 10 22 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 12 13 true (-2),
.cycle 11 14 true (-2),
.last 26 (1,true),
.cycle 10 17 false (2),
.cycle 0 27 false (3),
.cycle 25 1 false (-3),
.cycle 2 25 false (3),
.last 28 (1,true),
.cycle 13 12 true (-2),
.cycle 1 24 false (3),
.cycle 10 21 false (2),
.cycle 10 24 true (-2),
.cycle 12 13 true (-2),
.cycle 9 16 false (2)
]),
.cycle 1 12 false (3),
.cycle 10 9 false (0),
.cycle 10 12 true (-2),
.cycle 12 1 true (-2),
.cycle 9 4 false (1)
])
theorem kid04_part83_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part83) = true := by rfl

def kid04_part84 : Audit := .split 10 (5,true) (byMove [
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
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 24 1 false (-2),
.cycle 1 11 false (3),
.cycle 19 1 false (-1),
.cycle 22 1 false (0),
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
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 22 1 false (2),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 11 1 false (1),
.split 12 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 22 1 false (-2),
.last 14 (4,false),
.cycle 0 14 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 9 13 false (3),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.last 13 (4,false),
.cycle 9 5 false (1),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (4,false),
.cycle 22 1 false (0),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 10 17 false (4),
.cycle 26 1 false (-2),
.cycle 2 11 false (3),
.cycle 9 15 false (3),
.last 13 (4,false),
.cycle 18 1 false (-2)
]),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 10 6 false (0),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 20 1 false (0),
.last 12 (1,true),
.cycle 15 1 false (1),
.cycle 0 13 true (-1),
.cycle 13 1 false (-1),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 22 1 false (0),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 2 11 false (3),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2)
]),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 21 1 false (1),
.split 11 (4,false) (byMove [
.cycle 20 1 false (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 9 12 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 11 1 true (1),
.cycle 9 4 true (0),
.cycle 15 1 false (-1),
.last 12 (1,true),
.last 17 (1,true),
.cycle 21 1 false (1),
.cycle 13 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 9 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid04_part84_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part84) = true := by rfl

def kid04_part85 : Audit := .cycle 0 10 true (0)
theorem kid04_part85_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part85) = true := by rfl

def kid04_part86 : Audit := .cycle 1 9 true (1)
theorem kid04_part86_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part86) = true := by rfl

def kid04_part87 : Audit := .cycle 20 1 false (2)
theorem kid04_part87_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part87) = true := by rfl

def kid04_part88 : Audit := .cycle 17 1 false (1)
theorem kid04_part88_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part88) = true := by rfl

def kid04_part89 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 14 1 false (0),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (1),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 16 4 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 10 3 true (1),
.cycle 9 4 true (1),
.last 16 (5,true),
.cycle 13 8 false (1),
.cycle 16 4 false (0),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 17 (5,true),
.cycle 9 4 true (1)
]),
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
.last 16 (1,true),
.cycle 15 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 16 5 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 23 5 false (3),
.last 16 (1,true),
.cycle 9 6 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 14 1 false (0),
.cycle 8 4 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid04_part89_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part89) = true := by rfl

def kid04_part90 : Audit := .cycle 9 1 true (1)
theorem kid04_part90_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part90) = true := by rfl

def kid04_part92 : Audit := .cycle 10 11 false (1)
theorem kid04_part92_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part92) = true := by rfl

def kid04_part93 : Audit := .cycle 10 12 false (1)
theorem kid04_part93_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part93) = true := by rfl

def kid04_part94 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 true (-3),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 31 (5,true),
.cycle 1 17 false (3),
.cycle 10 12 false (1),
.cycle 10 15 false (1),
.cycle 17 1 true (-3),
.cycle 9 9 false (1)
])
theorem kid04_part94_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part94) = true := by rfl

def kid04_part95 : Audit := .cycle 0 17 false (3)
theorem kid04_part95_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part95) = true := by rfl

def kid04_part96 : Audit := .cycle 12 4 false (0)
theorem kid04_part96_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part96) = true := by rfl

def kid04_part97 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 16 14 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.last 17 (4,false),
.cycle 9 8 false (1)
])
theorem kid04_part97_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part97) = true := by rfl

def kid04_part98 : Audit := .cycle 6 20 false (3)
theorem kid04_part98_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part98) = true := by rfl

def kid04_part99 : Audit := .cycle 10 11 true (-2)
theorem kid04_part99_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part99) = true := by rfl

def kid04_part100 : Audit := .cycle 10 11 false (1)
theorem kid04_part100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part100) = true := by rfl

def kid04_part101 : Audit := .cycle 10 9 false (1)
theorem kid04_part101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part101) = true := by rfl

def kid04_part102 : Audit := .split 16 (4,false) (byMove [
.last 30 (5,true),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 12 6 false (0),
.cycle 9 8 false (1),
.cycle 0 17 true (-2),
.cycle 10 12 true (-2),
.cycle 10 27 true (-3),
.cycle 10 11 false (1),
.cycle 16 1 true (0),
.cycle 13 4 true (-2),
.cycle 14 3 true (-2),
.last 20 (5,true),
.cycle 0 19 true (-2),
.cycle 10 9 false (1),
.cycle 12 6 false (0),
.cycle 9 8 false (1),
.last 30 (5,true),
.cycle 6 20 false (3),
.cycle 10 11 true (-2),
.cycle 10 14 true (-2),
.cycle 16 1 true (0),
.cycle 6 12 false (3)
])
theorem kid04_part102_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part102) = true := by rfl

def kid04_part103 : Audit := .cycle 13 3 true (-2)
theorem kid04_part103_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part103) = true := by rfl

def kid04_part104 : Audit := .cycle 10 6 false (1)
theorem kid04_part104_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part104) = true := by rfl

def kid04_part105 : Audit := .cycle 11 7 false (1)
theorem kid04_part105_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part105) = true := by rfl

def kid04_part106 : Audit := .split 17 (4,false) (byMove [
.last 40 (5,true),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.cycle 0 20 true (-3),
.cycle 18 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 11 9 false (1),
.last 21 (5,true),
.last 49 (5,true),
.cycle 10 10 false (1),
.last 20 (5,true),
.cycle 9 9 false (1)
])
theorem kid04_part106_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part106) = true := by rfl

def kid04_part107 : Audit := .cycle 10 12 true (-2)
theorem kid04_part107_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part107) = true := by rfl

def kid04_part108 : Audit := .cycle 12 4 false (0)
theorem kid04_part108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part108) = true := by rfl

def kid04_part109 : Audit := .split 16 (5,true) (byMove [
.cycle 0 22 false (3),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 1, 64],[35, 32, 16, 35, 32, 2, 64],80⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 10 12 true (-2),
.cycle 13 5 false (-1),
.last 18 (4,false),
.cycle 0 18 true (-2),
.cycle 12 5 false (0),
.cycle 13 5 true (-2),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 14 true (-3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 2 16 false (3),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 6 22 false (3),
.last 19 (4,false),
.cycle 9 14 false (1)
])
theorem kid04_part109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part109) = true := by rfl

def kid04_part110 : Audit := .split 29 (5,true) (byMove [
.cycle 10 25 false (3),
.cycle 10 40 false (3),
.last 31 (4,false),
.cycle 0 31 false (3),
.cycle 12 18 false (3),
.cycle 13 18 false (3),
.cycle 6 34 false (3),
.cycle 10 25 true (-2),
.cycle 3 45 false (3),
.cycle 10 23 false (3),
.last 30 (4,false),
.cycle 13 17 true (-2),
.cycle 10 20 false (3),
.cycle 2 30 false (3),
.last 31 (4,false),
.cycle 10 26 true (-2),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[32, 4096, 35184372088832, 32768, 281474976710656, 4096, 283709186247744, 283709186247744, 283709320465984, 134217728, 281474976710656, 16777216, 2199023255552, 32, 2199023255552, 35184372088832, 281474976710656, 4398046511104, 34359738368, 536872960, 34359738368, 134217728, 281474976710656, 16777216, 283709186247744, 283709186247744, 283709320465984, 512, 281474976710656, 64, 268436480, 4194304, 512, 2097152, 281474976710656, 262144, 65536, 4194304, 134217728, 2097152, 281474976710656, 262144, 65536, 536870912, 262144, 134217728, 281474976710656, 16777216, 281474976710656],[4096, 65536, 16, 4096, 32, 65536, 283709186247744, 283709186247744, 1024, 283709186247744, 2048, 268435456, 32, 32, 1099511627776, 2199023255552, 2199023255552, 70368744177664, 536872960, 34359738368, 17179869184, 281474976710656, 34359738368, 268435456, 283709186247744, 283709186247744, 268435456, 283709186247744, 536870912, 1024, 4194304, 4194304, 1024, 262144, 2048, 4194304, 4194304, 4194304, 268435456, 262144, 536870912, 4194304, 536870912, 65536, 268435456, 4096, 536870912, 268435456, 281474976710656],507102355983824⟩,
.cycle 26 8 false (1),
.cycle 16 14 true (-1),
.cycle 1 42 false (3),
.cycle 2 28 false (3),
.cycle 10 27 true (-2),
.last 30 (4,false),
.cycle 9 26 false (3)
])
theorem kid04_part110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part110) = true := by rfl

def kid04_part111 : Audit := .split 28 (5,true) (byMove [
.cycle 0 29 false (3),
.cycle 10 24 false (2),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.last 29 (4,false),
.cycle 13 16 false (2),
.cycle 0 29 false (3),
.cycle 10 24 true (-2),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.last 29 (4,false),
.cycle 13 16 true (-2),
.cycle 14 15 false (2),
.cycle 11 19 false (2),
.cycle 0 31 false (3),
.cycle 29 1 false (-3),
.last 29 (4,false),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 33, 16, 33, 32, 32, 64],80⟩,
.cycle 16 14 true (-2),
.cycle 1 28 false (3),
.cycle 10 23 false (2),
.cycle 10 26 true (-2),
.last 29 (4,false),
.cycle 9 20 false (2)
])
theorem kid04_part111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part111) = true := by rfl

def kid04_part112 : Audit := .cycle 2 14 false (3)
theorem kid04_part112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part112) = true := by rfl

def kid04_part113 : Audit := .cycle 10 13 true (-2)
theorem kid04_part113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part113) = true := by rfl

def kid04_part114 : Audit := .split 16 (4,false) (byMove [
.cycle 2 16 false (3),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 6 22 false (3),
.last 18 (5,true),
.last 17 (5,true),
.last 34 (5,true),
.cycle 10 12 true (-2),
.cycle 3 16 false (3),
.cycle 3 14 false (3),
.cycle 16 1 true (0),
.cycle 13 4 true (-2),
.last 20 (5,true),
.last 19 (5,true),
.cycle 11 6 false (1),
.cycle 10 13 true (-2),
.last 18 (5,true),
.last 17 (5,true),
.last 30 (5,true),
.last 29 (5,true),
.last 28 (5,true),
.cycle 10 14 true (-2),
.cycle 16 1 true (0),
.last 21 (5,true)
])
theorem kid04_part114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part114) = true := by rfl

def kid04_part115 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 false (3),
.cycle 10 16 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 13 8 false (0),
.cycle 0 21 false (3),
.cycle 10 16 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 13 8 true (-2),
.cycle 14 7 false (0),
.cycle 11 11 false (1),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 20 6 false (-2),
.cycle 16 14 true (-2),
.cycle 1 20 false (3),
.cycle 10 15 false (1),
.cycle 10 18 true (-2),
.last 21 (4,false),
.cycle 9 12 false (1)
])
theorem kid04_part115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part115) = true := by rfl

def kid04_part91 : Audit := .split 15 (1,true) (byMove [(kid04_part92),(kid04_part93),(kid04_part94),(kid04_part95),(kid04_part96),(kid04_part97),(kid04_part98),(kid04_part99),(kid04_part100),(kid04_part101),(kid04_part102),(kid04_part103),(kid04_part104),(kid04_part105),(kid04_part106),(kid04_part107),(kid04_part108),(kid04_part109),(kid04_part110),(kid04_part111),(kid04_part112),(kid04_part113),(kid04_part114),(kid04_part115)])

theorem kid04_part91_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part91) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part92),(kid04_part93),(kid04_part94),(kid04_part95),(kid04_part96),(kid04_part97),(kid04_part98),(kid04_part99),(kid04_part100),(kid04_part101),(kid04_part102),(kid04_part103),(kid04_part104),(kid04_part105),(kid04_part106),(kid04_part107),(kid04_part108),(kid04_part109),(kid04_part110),(kid04_part111),(kid04_part112),(kid04_part113),(kid04_part114),(kid04_part115)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part92_checked

  · exact kid04_part98_checked

  · exact kid04_part104_checked

  · exact kid04_part110_checked

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

def kid04_part117 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 false (3),
.cycle 22 4 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 4 false (-2),
.cycle 0 16 true (-1),
.cycle 22 4 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 16 4 false (0),
.cycle 24 4 false (0),
.cycle 16 4 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 4 false (-2),
.cycle 0 30 true (-1),
.cycle 1 15 false (3),
.cycle 21 4 false (1),
.cycle 24 4 false (2),
.last 16 (4,false),
.cycle 9 7 false (1)
])
theorem kid04_part117_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part117) = true := by rfl

def kid04_part118 : Audit := .cycle 0 14 true (-1)
theorem kid04_part118_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part118) = true := by rfl

def kid04_part119 : Audit := .cycle 12 1 false (0)
theorem kid04_part119_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part119) = true := by rfl

def kid04_part120 : Audit := .cycle 11 1 false (-1)
theorem kid04_part120_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part120) = true := by rfl

def kid04_part121 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 14 4 false (0),
.cycle 12 4 false (1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 13 4 false (1),
.cycle 12 4 false (0),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 16 4 false (0),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 15 (5,true),
.last 15 (5,true),
.cycle 0 14 true (-1),
.cycle 15 4 false (1),
.last 14 (5,true),
.cycle 9 3 false (1)
])
theorem kid04_part121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part121) = true := by rfl

def kid04_part122 : Audit := .cycle 11 4 false (-1)
theorem kid04_part122_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part122) = true := by rfl

def kid04_part123 : Audit := .cycle 17 4 false (3)
theorem kid04_part123_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part123) = true := by rfl

def kid04_part124 : Audit := .cycle 18 4 false (4)
theorem kid04_part124_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part124) = true := by rfl

def kid04_part125 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 true (0),
.cycle 13 4 false (1),
.cycle 21 4 false (1),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 21 4 false (3),
.cycle 12 1 true (0),
.cycle 9 4 true (0)
])
theorem kid04_part125_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part125) = true := by rfl

def kid04_part126 : Audit := .cycle 0 12 true (0)
theorem kid04_part126_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part126) = true := by rfl

def kid04_part127 : Audit := .cycle 11 4 false (1)
theorem kid04_part127_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part127) = true := by rfl

def kid04_part128 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 18 4 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 18 4 false (4),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 12 (4,false),
.cycle 12 4 false (2),
.cycle 11 7 false (2),
.cycle 12 4 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 17 4 false (3),
.cycle 20 4 false (4),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid04_part128_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part128) = true := by rfl

def kid04_part129 : Audit := .cycle 14 4 false (0)
theorem kid04_part129_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part129) = true := by rfl

def kid04_part130 : Audit := .cycle 11 4 false (0)
theorem kid04_part130_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part130) = true := by rfl

def kid04_part131 : Audit := .cycle 19 4 false (3)
theorem kid04_part131_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part131) = true := by rfl

def kid04_part132 : Audit := .cycle 11 1 false (-1)
theorem kid04_part132_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part132) = true := by rfl

def kid04_part133 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 7 18 false (3),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 0 16 true (-1),
.cycle 19 4 false (3),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 15 (5,true),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.last 25 (5,true),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid04_part133_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part133) = true := by rfl

def kid04_part134 : Audit := .cycle 11 4 false (-1)
theorem kid04_part134_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part134) = true := by rfl

def kid04_part135 : Audit := .cycle 2 10 true (0)
theorem kid04_part135_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part135) = true := by rfl

def kid04_part136 : Audit := .cycle 1 11 true (0)
theorem kid04_part136_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part136) = true := by rfl

def kid04_part137 : Audit := .cycle 11 4 false (1)
theorem kid04_part137_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part137) = true := by rfl

def kid04_part138 : Audit := .cycle 0 12 true (0)
theorem kid04_part138_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part138) = true := by rfl

def kid04_part139 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 4 false (1),
.last 15 (4,false),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 21 4 false (3),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid04_part139_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part139) = true := by rfl

def kid04_part140 : Audit := .split 11 (5,true) (byMove [
.cycle 18 4 false (2),
.cycle 9 4 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 12 true (0),
.cycle 31 4 false (3),
.cycle 18 4 false (2),
.cycle 16 4 false (2),
.last 12 (4,false),
.cycle 17 4 false (1),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.last 13 (4,false),
.cycle 19 4 false (3),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 35 4 false (3),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid04_part140_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part140) = true := by rfl

def kid04_part116 : Audit := .split 10 (1,true) (byMove [(kid04_part117),(kid04_part118),(kid04_part119),(kid04_part120),(kid04_part121),(kid04_part122),(kid04_part123),(kid04_part124),(kid04_part125),(kid04_part126),(kid04_part127),(kid04_part128),(kid04_part129),(kid04_part130),(kid04_part131),(kid04_part132),(kid04_part133),(kid04_part134),(kid04_part135),(kid04_part136),(kid04_part137),(kid04_part138),(kid04_part139),(kid04_part140)])

theorem kid04_part116_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part116) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part117),(kid04_part118),(kid04_part119),(kid04_part120),(kid04_part121),(kid04_part122),(kid04_part123),(kid04_part124),(kid04_part125),(kid04_part126),(kid04_part127),(kid04_part128),(kid04_part129),(kid04_part130),(kid04_part131),(kid04_part132),(kid04_part133),(kid04_part134),(kid04_part135),(kid04_part136),(kid04_part137),(kid04_part138),(kid04_part139),(kid04_part140)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part117_checked

  · exact kid04_part123_checked

  · exact kid04_part129_checked

  · exact kid04_part135_checked

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

def kid04_part142 : Audit := .cycle 0 16 true (-2)
theorem kid04_part142_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part142) = true := by rfl

def kid04_part143 : Audit := .split 27 (5,true) (byMove [
.cycle 0 28 false (3),
.cycle 0 39 false (3),
.cycle 29 1 false (-1),
.cycle 28 1 false (-2),
.cycle 0 40 false (3),
.cycle 0 31 false (3),
.cycle 0 28 true (-3),
.cycle 0 39 true (-3),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 0 40 true (-3),
.cycle 0 31 true (-3),
.last 29 (1,true),
.cycle 0 34 false (3),
.cycle 0 30 true (-3),
.cycle 28 1 false (-2),
.cycle 1 43 false (3),
.cycle 0 42 true (-3),
.cycle 18 20 true (-3),
.cycle 1 27 false (3),
.cycle 0 38 true (-3),
.cycle 0 41 true (-3),
.last 29 (1,true),
.cycle 9 19 false (1)
])
theorem kid04_part143_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part143) = true := by rfl

def kid04_part144 : Audit := .cycle 13 1 false (-1)
theorem kid04_part144_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part144) = true := by rfl

def kid04_part145 : Audit := .cycle 12 1 false (-2)
theorem kid04_part145_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part145) = true := by rfl

def kid04_part146 : Audit := .cycle 11 1 false (-1)
theorem kid04_part146_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part146) = true := by rfl

def kid04_part147 : Audit := .split 19 (5,true) (byMove [
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
.cycle 0 34 true (-3),
.cycle 12 20 true (-3),
.cycle 1 19 false (3),
.cycle 0 30 true (-3),
.cycle 0 33 true (-3),
.cycle 19 2 true (-1),
.cycle 9 11 false (1)
])
theorem kid04_part147_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part147) = true := by rfl

def kid04_part148 : Audit := .split 13 (1,true) (byMove [
.cycle 0 25 true (-1),
.cycle 0 26 true (-2),
.cycle 0 16 true (-1),
.cycle 0 15 true (-1),
.cycle 0 18 true (-2),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 0 25 true (-1),
.last 29 (5,true),
.cycle 0 23 true (-1),
.cycle 0 15 true (-1),
.cycle 0 17 true (-1),
.cycle 0 20 true (-2),
.last 25 (5,true),
.cycle 10 4 true (-1),
.cycle 0 26 true (-1),
.cycle 12 6 true (-2),
.last 14 (5,true),
.last 26 (5,true),
.last 32 (5,true),
.cycle 2 12 true (-1),
.cycle 0 27 true (-1),
.cycle 0 15 true (-1),
.last 24 (5,true)
])
theorem kid04_part148_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part148) = true := by rfl

def kid04_part149 : Audit := .cycle 0 18 true (-2)
theorem kid04_part149_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part149) = true := by rfl

def kid04_part150 : Audit := .cycle 0 14 true (-1)
theorem kid04_part150_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part150) = true := by rfl

def kid04_part151 : Audit := .cycle 12 1 false (0)
theorem kid04_part151_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part151) = true := by rfl

def kid04_part152 : Audit := .cycle 0 17 true (-1)
theorem kid04_part152_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part152) = true := by rfl

def kid04_part153 : Audit := .cycle 0 26 true (-1)
theorem kid04_part153_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part153) = true := by rfl

def kid04_part154 : Audit := .split 13 (1,true) (byMove [
.last 29 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M44.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M44.never m hm),
.cycle 10 4 false (0),
.last 19 (5,true),
.last 37 (5,true),
.last 14 (5,true),
.last 76 (5,true),
.cycle 7 8 false (3),
.cycle 0 16 true (-2),
.last 27 (5,true),
.last 28 (5,true),
.cycle 0 28 true (-2),
.last 41 (5,true),
.last 25 (5,true),
.cycle 10 4 false (0),
.cycle 0 18 true (-2),
.cycle 12 6 true (-4),
.last 14 (5,true),
.last 28 (5,true),
.last 17 (5,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.last 18 (5,true),
.last 24 (5,true)
])
theorem kid04_part154_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part154) = true := by rfl

def kid04_part155 : Audit := .split 37 (5,true) (byMove [
.last 88 (1,true),
.last 38 (1,true),
.cycle 0 46 false (5),
.cycle 3 63 false (5),
.proven (BB6.Agent11Raw39B1RCPumps.M45.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M45.never m hm),
.proven (BB6.Agent11Raw39B1RCPumps.M46.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M46.never m hm),
.cycle 18 20 true (-2),
.cycle 0 65 true (-4),
.cycle 55 1 false (1),
.cycle 50 26 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M47.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M47.never m hm),
.cycle 0 49 true (-4),
.proven (BB6.Agent11Raw39B1RCPumps.M48.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M48.never m hm),
.last 38 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M49.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M49.never m hm),
.cycle 13 32 true (-4),
.last 43 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M50.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M50.never m hm),
.cycle 18 20 true (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M51.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M51.never m hm),
.proven (BB6.Agent11Raw39B1RCPumps.M52.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M52.never m hm),
.cycle 0 69 true (-4),
.last 39 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M53.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M53.never m hm)
])
theorem kid04_part155_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part155) = true := by rfl

def kid04_part156 : Audit := .split 15 (1,true) (byMove [
.cycle 0 27 true (-2),
.cycle 0 28 true (-2),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.cycle 0 20 true (-2),
.last 16 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 1, 1, 8192, 16384, 8, 256, 1, 1, 33554432, 67108864, 2097152, 256, 1073741824, 1073741824, 8192, 16384, 8, 16384, 1, 1, 33554432, 67108864, 134217728, 1327513993, 1327513993, 1327513993, 1073741824],[256, 1, 128, 1, 128, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 1073741824, 1, 1073741824, 1073741824, 67108864, 16777216, 1327513993, 16777216, 1327513993, 1073741824, 1073741824],2132259662⟩,
.cycle 0 27 true (-2),
.last 31 (5,true),
.cycle 0 25 true (-2),
.cycle 0 19 true (-2),
.cycle 0 19 true (-2),
.cycle 0 22 true (-2),
.last 27 (5,true),
.cycle 10 6 true (-2),
.cycle 0 28 true (-2),
.cycle 12 6 true (-2),
.last 16 (5,true),
.last 28 (5,true),
.last 34 (5,true),
.cycle 2 14 true (-2),
.cycle 0 29 true (-2),
.last 26 (5,true),
.last 26 (5,true)
])
theorem kid04_part156_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part156) = true := by rfl

def kid04_part157 : Audit := .cycle 12 1 false (-2)
theorem kid04_part157_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part157) = true := by rfl

def kid04_part158 : Audit := .cycle 11 1 false (-1)
theorem kid04_part158_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part158) = true := by rfl

def kid04_part159 : Audit := .far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 2, 4, 4, 4, 4, 6, 2, 4],[65536, 256, 2097152, 512, 2048, 256, 4398046511104, 32, 274877906944, 2097152, 8388608, 1048576, 4398046511104, 65536, 134217728, 8589934592, 34359738368, 4294967296, 4398046511104, 536870912, 274877906944, 134217728, 536870912, 67108864, 5258046668800, 5258046668800, 5222881558528, 134217728, 536870912, 67108864, 4398046511104, 536870912, 4398046511104, 549755813888, 2199023255552, 274877906944, 4398046511104, 536870912, 274877906944, 134217728, 536870912, 67108864, 4398046511104],[256, 4398046511104, 16, 34359738368, 32, 4398046511104, 32, 4398046511104, 65536, 274877906944, 131072, 4398046511104, 65536, 4398046511104, 268435456, 4398046511104, 536870912, 4398046511104, 536870912, 4398046511104, 65536, 256, 131072, 4398046511104, 5258046668800, 4398046511104, 268435456, 5257778167808, 536870912, 4398046511104, 536870912, 4398046511104, 268435456, 34359738368, 536870912, 4398046511104, 536870912, 4398046511104, 65536, 67108864, 131072, 4398046511104, 4398046511104],7928372139072⟩
theorem kid04_part159_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part159) = true := by rfl

def kid04_part160 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 false (3),
.cycle 0 27 false (3),
.cycle 0 19 false (3),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 0 25 true (-1),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.last 37 (5,true),
.cycle 0 17 true (-1),
.last 17 (5,true),
.last 26 (5,true),
.last 23 (5,true),
.cycle 0 26 true (-1),
.last 15 (5,true),
.last 14 (5,true),
.last 26 (5,true),
.last 25 (5,true),
.last 31 (5,true),
.cycle 0 27 true (-1),
.last 27 (5,true),
.last 17 (5,true)
])
theorem kid04_part160_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part160) = true := by rfl

def kid04_part161 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 false (3),
.cycle 0 27 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 1 16 false (3),
.cycle 0 19 false (3),
.cycle 0 16 true (-1),
.cycle 0 27 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 1 16 true (-1),
.cycle 0 19 true (-1),
.last 17 (1,true),
.cycle 0 22 false (3),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 17 (1,true),
.cycle 0 30 true (-3),
.cycle 12 20 true (-3),
.cycle 1 15 false (3),
.cycle 0 26 true (-2),
.cycle 0 29 true (-1),
.cycle 12 20 true (-3),
.cycle 9 7 false (1)
])
theorem kid04_part161_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part161) = true := by rfl

def kid04_part162 : Audit := .cycle 0 14 true (-1)
theorem kid04_part162_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part162) = true := by rfl

def kid04_part163 : Audit := .cycle 0 20 true (-2)
theorem kid04_part163_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part163) = true := by rfl

def kid04_part164 : Audit := .split 14 (5,true) (byMove [
.cycle 0 26 true (-2),
.last 15 (1,true),
.cycle 16 1 true (-2),
.cycle 0 16 true (-1),
.cycle 0 19 false (3),
.cycle 0 19 false (3),
.cycle 0 15 true (-1),
.cycle 0 26 true (-1),
.cycle 32 1 false (2),
.cycle 0 24 true (-2),
.cycle 15 1 true (1),
.cycle 0 18 true (-1),
.cycle 0 21 false (3),
.last 15 (1,true),
.cycle 10 5 false (1),
.cycle 0 27 true (-1),
.last 20 (1,true),
.cycle 0 25 false (3),
.cycle 13 18 true (-1),
.cycle 1 33 false (3),
.cycle 2 13 false (3),
.cycle 0 28 true (-1),
.cycle 15 1 true (1),
.cycle 9 17 false (1)
])
theorem kid04_part164_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part164) = true := by rfl

def kid04_part165 : Audit := .cycle 9 3 false (1)
theorem kid04_part165_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part165) = true := by rfl

def kid04_part141 : Audit := .split 11 (4,false) (byMove [(kid04_part142),(kid04_part143),(kid04_part144),(kid04_part145),(kid04_part146),(kid04_part147),(kid04_part148),(kid04_part149),(kid04_part150),(kid04_part151),(kid04_part152),(kid04_part153),(kid04_part154),(kid04_part155),(kid04_part156),(kid04_part157),(kid04_part158),(kid04_part159),(kid04_part160),(kid04_part161),(kid04_part162),(kid04_part163),(kid04_part164),(kid04_part165)])

theorem kid04_part141_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part141) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some mv)) (byMove [(kid04_part142),(kid04_part143),(kid04_part144),(kid04_part145),(kid04_part146),(kid04_part147),(kid04_part148),(kid04_part149),(kid04_part150),(kid04_part151),(kid04_part152),(kid04_part153),(kid04_part154),(kid04_part155),(kid04_part156),(kid04_part157),(kid04_part158),(kid04_part159),(kid04_part160),(kid04_part161),(kid04_part162),(kid04_part163),(kid04_part164),(kid04_part165)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part142_checked

  · exact kid04_part148_checked

  · exact kid04_part154_checked

  · exact kid04_part160_checked

  · exact kid04_part143_checked

  · exact kid04_part149_checked

  · exact kid04_part155_checked

  · exact kid04_part161_checked

  · exact kid04_part144_checked

  · exact kid04_part150_checked

  · exact kid04_part156_checked

  · exact kid04_part162_checked

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

def kid04_part166 : Audit := .cycle 20 1 false (0)
theorem kid04_part166_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part166) = true := by rfl

def kid04_part168 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 false (3),
.cycle 10 15 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 0 19 false (3),
.cycle 11 7 false (-1),
.last 39 (1,true),
.cycle 10 15 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 19 false (3),
.cycle 11 7 false (-1),
.last 19 (1,true),
.cycle 10 10 false (0),
.last 41 (1,true),
.cycle 18 1 false (-4),
.cycle 12 6 false (-1),
.cycle 11 7 false (-1),
.last 39 (1,true),
.cycle 1 17 false (3),
.cycle 10 14 false (0),
.cycle 10 17 false (0),
.cycle 10 16 false (0),
.cycle 9 9 false (1)
])
theorem kid04_part168_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part168) = true := by rfl

def kid04_part169 : Audit := .split 17 (1,true) (byMove [
.last 62 (5,true),
.last 47 (5,true),
.cycle 1 19 false (3),
.cycle 0 19 true (-3),
.proven (BB6.Agent11Raw39B1RCPumps.M56.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M56.never m hm),
.last 18 (5,true),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[2199023255552, 65536, 35184372088832, 32768, 2, 65536, 281512326990976, 281512326990976, 281512461209216, 134217728, 128, 268435456, 34359738368, 32, 2147483648, 35184372088832, 137438953472, 70368744177664, 34359738368, 536872960, 2147483648, 134217728, 2147483648, 268435456, 283711350246528, 281512326990976, 281649900162688, 512, 33554432, 1024, 281474976710656, 4194304, 512, 2097152, 128, 4194304, 281474976710656, 4194304, 134217728, 2097152, 33554432, 4194304, 4194304, 536870912, 4194304, 134217728, 33554432, 268435456, 281474976710656],[65536, 4194304, 16, 4194304, 32, 281474976710656, 281512326990976, 281512326990976, 1024, 281512326990976, 2048, 281474976710656, 32, 137438953472, 1099511627776, 137438953472, 2199023255552, 281474976710656, 536872960, 2147483648, 17179869184, 2147483648, 34359738368, 281474976710656, 281512326990976, 281512326990976, 268435456, 281512326990976, 536870912, 281474976710656, 4194304, 4194304, 1024, 4194304, 2048, 281474976710656, 4194304, 4194304, 268435456, 4194304, 536870912, 281474976710656, 536870912, 65536, 268435456, 65536, 536870912, 281474976710656, 281474976710656],502564718775744⟩,
.cycle 7 45 false (4),
.last 35 (5,true),
.last 58 (5,true),
.cycle 12 20 true (-3),
.cycle 146 50 true (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M58.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M58.never m hm),
.cycle 7 13 false (3),
.cycle 1 19 false (3),
.cycle 100 1 false (-6),
.cycle 12 10 false (1),
.last 18 (5,true),
.last 29 (5,true),
.last 28 (5,true),
.cycle 14 16 true (-3),
.cycle 4 51 false (4),
.cycle 17 2 true (1),
.last 20 (5,true)
])
theorem kid04_part169_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part169) = true := by rfl

def kid04_part170 : Audit := .cycle 14 1 false (-2)
theorem kid04_part170_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part170) = true := by rfl

def kid04_part171 : Audit := .cycle 13 1 false (-3)
theorem kid04_part171_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part171) = true := by rfl

def kid04_part172 : Audit := .cycle 12 1 false (-2)
theorem kid04_part172_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part172) = true := by rfl

def kid04_part173 : Audit := .cycle 11 2 false (-1)
theorem kid04_part173_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part173) = true := by rfl

def kid04_part174 : Audit := .cycle 0 16 true (-2)
theorem kid04_part174_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part174) = true := by rfl

def kid04_part175 : Audit := .split 13 (1,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 11 3 false (-1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 2, 1, 8192, 16384, 8, 256, 2, 1, 33554432, 67108864, 2097152, 256, 524288, 1073741824, 8192, 16384, 8, 16384, 2, 1, 33554432, 67108864, 134217728, 1140867072, 33554432, 1090519040, 1073741824],[256, 1, 256, 1, 128, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 16777216, 1140850688, 16777216, 1107296256, 1073741824, 1073741824],2136389470⟩,
.cycle 15 11 true (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (0),
.cycle 14 12 true (0),
.last 17 (5,true),
.cycle 10 8 false (0),
.cycle 10 6 false (0),
.cycle 0 28 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 true (-2),
.cycle 11 3 false (-1),
.last 27 (5,true),
.last 17 (5,true),
.cycle 0 16 true (-2),
.cycle 14 13 true (-2),
.cycle 14 12 true (0),
.cycle 9 5 false (1)
])
theorem kid04_part175_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part175) = true := by rfl

def kid04_part176 : Audit := .cycle 16 1 false (0)
theorem kid04_part176_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part176) = true := by rfl

def kid04_part177 : Audit := .split 15 (1,true) (byMove [
.cycle 0 27 true (-2),
.cycle 0 28 true (-2),
.cycle 18 1 false (0),
.cycle 0 17 true (-2),
.cycle 0 20 true (-2),
.last 16 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 8, 1, 8192, 16384, 8, 256, 8, 1, 33554432, 67108864, 2097152, 256, 2097152, 1073741824, 8192, 16384, 8, 16384, 8, 1, 33554432, 67108864, 134217728, 1140867072, 134217728, 1090519040, 1073741824],[256, 1, 1073758208, 1, 128, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 16777216, 1140867072, 16777216, 1107296256, 1073741824, 1073741824],2136389470⟩,
.cycle 0 27 true (-2),
.last 31 (5,true),
.cycle 0 25 true (-2),
.last 31 (5,true),
.cycle 0 19 true (-2),
.cycle 0 22 true (-2),
.last 27 (5,true),
.cycle 18 1 false (0),
.cycle 0 28 true (-2),
.cycle 10 6 true (-2),
.last 16 (5,true),
.last 27 (5,true),
.last 26 (5,true),
.cycle 2 14 true (-2),
.cycle 0 29 true (-2),
.cycle 3 14 true (-2),
.last 18 (5,true)
])
theorem kid04_part177_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part177) = true := by rfl

def kid04_part178 : Audit := .cycle 10 3 false (0)
theorem kid04_part178_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part178) = true := by rfl

def kid04_part179 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 4 true (-2),
.cycle 11 3 false (-1),
.last 15 (1,true),
.cycle 15 11 true (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (0),
.cycle 14 4 true (0),
.cycle 17 3 true (1),
.last 15 (1,true),
.cycle 10 6 false (0),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 12 2 true (-2),
.cycle 11 3 false (-1),
.last 15 (1,true),
.cycle 1 17 false (3),
.cycle 0 16 true (-2),
.cycle 14 13 true (-2),
.cycle 14 4 true (0),
.cycle 9 5 false (1)
])
theorem kid04_part179_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part179) = true := by rfl

def kid04_part180 : Audit := .split 14 (1,true) (byMove [
.last 51 (5,true),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.last 23 (5,true),
.cycle 10 5 false (0),
.last 15 (5,true),
.last 47 (5,true),
.last 65 (5,true),
.cycle 10 9 false (0),
.last 45 (5,true),
.cycle 8 7 false (2),
.last 15 (5,true),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.cycle 10 8 false (0),
.cycle 10 5 false (0),
.last 15 (5,true),
.last 34 (5,true),
.last 19 (5,true),
.last 17 (5,true),
.last 35 (5,true),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid04_part180_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part180) = true := by rfl

def kid04_part181 : Audit := .cycle 10 5 false (0)
theorem kid04_part181_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part181) = true := by rfl

def kid04_part182 : Audit := .split 36 (1,true) (byMove [
.cycle 42 12 true (0),
.cycle 39 12 true (-4),
.last 45 (5,true),
.last 45 (5,true),
.cycle 37 12 true (-4),
.last 37 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 1, 256, 524288, 1048576, 32768, 256, 4096, 4097, 128, 256, 8, 1048576, 1, 256, 2147483648, 4294967296, 134217728, 256, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 1048576, 1073741824, 68719476736, 2147483648, 4294967296, 8589934592, 84825604096, 84825604096, 84825604096, 68719476736],[256, 1, 128, 1, 32768, 68719476736, 1048576, 4096, 1048576, 4096, 68719476736, 68719476736, 256, 1, 128, 1, 128, 68719476736, 4294967296, 16777216, 68719476736, 16777216, 68719476736, 68719476736, 4294967296, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 4294967296, 1073741824, 84825604096, 1073741824, 84825604096, 68719476736, 68719476736],137301344332⟩,
.cycle 51 12 true (0),
.cycle 47 12 true (-3),
.cycle 40 12 true (0),
.last 51 (5,true),
.last 37 (5,true),
.cycle 37 12 true (-4),
.cycle 39 12 true (-5),
.cycle 31 6 true (-3),
.cycle 37 12 true (-3),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 1, 256, 524288, 1048576, 32768, 256, 1, 1, 128, 256, 8, 1048576, 1, 256, 2147483648, 4294967296, 134217728, 256, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 1048576, 1073741824, 68719476736, 2147483648, 4294967296, 8589934592, 84825604096, 84825604096, 84825604096, 68719476736],[256, 256, 128, 1, 32768, 68719476736, 1048576, 1, 1048576, 4096, 68719476736, 68719476736, 256, 256, 128, 1, 128, 68719476736, 4294967296, 68719476736, 68719476736, 16777216, 68719476736, 68719476736, 4294967296, 68719476736, 68719476736, 1073741824, 68719476736, 68719476736, 4294967296, 84825604096, 84825604096, 1073741824, 84825604096, 68719476736, 68719476736],137301344332⟩,
.last 37 (5,true),
.last 55 (5,true),
.last 41 (5,true),
.last 39 (5,true),
.cycle 54 12 true (-4),
.last 38 (5,true),
.last 37 (5,true)
])
theorem kid04_part182_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part182) = true := by rfl

def kid04_part183 : Audit := .cycle 13 1 false (-3)
theorem kid04_part183_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part183) = true := by rfl

def kid04_part184 : Audit := .cycle 12 1 false (-2)
theorem kid04_part184_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part184) = true := by rfl

def kid04_part185 : Audit := .cycle 11 2 false (-1)
theorem kid04_part185_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part185) = true := by rfl

def kid04_part186 : Audit := .cycle 0 16 true (-2)
theorem kid04_part186_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part186) = true := by rfl

def kid04_part187 : Audit := .split 13 (1,true) (byMove [
.cycle 10 11 false (0),
.cycle 10 12 false (0),
.cycle 1 15 false (3),
.last 19 (5,true),
.cycle 10 4 false (0),
.last 14 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 4096, 524288, 1048576, 32768, 67109120, 524288, 4096, 128, 256, 134217728, 68787634176, 128, 1073741824, 33554432, 67108864, 8589934592, 256, 33554432, 68719476736, 33554432, 67108864, 134217728, 68787634176, 33554432, 68736258048, 33554432, 67108864, 134217728, 1048576, 33554432, 16777216, 68719476736],[256, 1, 1048576, 1, 128, 68719476736, 1048576, 4096, 1048576, 4096, 68719476736, 68719476736, 256, 16777216, 67108864, 16777216, 128, 68719476736, 67108864, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 16777216, 68787634176, 16777216, 68753031296, 68719476736, 67108864, 16777216, 67108864, 16777216, 68719476736, 68719476736, 68719476736],128847898434⟩,
.cycle 7 8 false (3),
.cycle 0 16 true (-2),
.cycle 10 9 false (0),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 65536, 524288, 1048576, 32768, 67109120, 524288, 65536, 128, 256, 134217728, 68787634176, 128, 17179869184, 33554432, 67108864, 8589934592, 256, 33554432, 68719476736, 33554432, 67108864, 134217728, 68787634176, 33554432, 68987977728, 33554432, 67108864, 134217728, 1048576, 33554432, 268435456, 68719476736],[256, 16, 1048576, 1, 128, 68719476736, 1048576, 65536, 1048576, 4096, 68719476736, 68719476736, 256, 268435456, 67108864, 16777216, 128, 68719476736, 67108864, 17179869184, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 268435456, 68787634176, 16777216, 68753031296, 68719476736, 67108864, 268435456, 67108864, 16777216, 68719476736, 68719476736, 68719476736],128847898434⟩,
.last 17 (5,true),
.cycle 10 6 false (0),
.cycle 10 7 false (0),
.last 19 (5,true),
.cycle 0 18 true (-2),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 27 (5,true),
.last 17 (5,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.last 27 (5,true),
.last 16 (5,true)
])
theorem kid04_part187_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part187) = true := by rfl

def kid04_part188 : Audit := .cycle 10 4 false (0)
theorem kid04_part188_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part188) = true := by rfl

def kid04_part189 : Audit := .split 15 (1,true) (byMove [
.last 40 (5,true),
.cycle 1 16 false (3),
.last 44 (5,true),
.cycle 0 17 true (-2),
.cycle 8 8 false (2),
.last 16 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 512, 4096, 524288, 1048576, 32768, 67109120, 2097152, 4096, 128, 256, 134217728, 68787634432, 512, 1073741824, 33554432, 67108864, 8589934592, 256, 134217728, 68719476736, 33554432, 67108864, 134217728, 68787634432, 134217728, 68736258048, 33554432, 67108864, 134217728, 1048576, 134217728, 16777216, 68719476736],[256, 1, 67109120, 1, 128, 68719476736, 1048576, 4096, 1048576, 4096, 68719476736, 68719476736, 256, 16777216, 256, 16777216, 128, 68719476736, 67108864, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 16777216, 68787634432, 16777216, 68753031296, 68719476736, 67108864, 16777216, 68787634432, 16777216, 68719476736, 68719476736, 68719476736],128847963986⟩,
.last 40 (5,true),
.last 31 (5,true),
.last 38 (5,true),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[2199023255552, 65536, 35184372088832, 32768, 34359738368, 65536, 281509873321984, 283709169208320, 283709303426560, 134217728, 283709169208320, 268435456, 34359738368, 32, 34359738368, 35184372088832, 34359738368, 70368744177664, 34359738368, 536872960, 34359738368, 134217728, 34359738368, 268435456, 281509873321984, 283709169208320, 283709303426560, 512, 283709169208320, 1024, 281474976710656, 281474976710656, 512, 2097152, 283709169208320, 4194304, 281474976710656, 281474976710656, 134217728, 2097152, 65536, 4194304, 2199023255552, 536870912, 4194304, 134217728, 281474976710656, 268435456, 281474976710656],[65536, 4194304, 16, 4194304, 32, 281474976710656, 283709169208320, 283709169208320, 1024, 283709169208320, 2048, 281474976710656, 32, 65536, 1099511627776, 34359738368, 2199023255552, 281474976710656, 536872960, 268436480, 17179869184, 281474976710656, 34359738368, 281474976710656, 283709169208320, 283709169208320, 268435456, 283709169208320, 536870912, 281474976710656, 281474976710656, 4194304, 1024, 4194304, 2048, 281474976710656, 281474976710656, 4194304, 268435456, 4194304, 536870912, 281474976710656, 536870912, 4194304, 268435456, 65536, 536870912, 281474976710656, 281474976710656],501604793585088⟩,
.last 32 (5,true),
.cycle 6 10 false (3),
.last 20 (5,true),
.cycle 4 14 false (3),
.last 131 (5,true),
.cycle 8 8 false (2),
.last 16 (5,true),
.last 27 (5,true),
.last 26 (5,true),
.last 61 (5,true),
.last 42 (5,true),
.last 43 (5,true),
.last 18 (5,true)
])
theorem kid04_part189_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part189) = true := by rfl

def kid04_part190 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 10 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 28 1 true (-6),
.cycle 11 4 false (-1),
.cycle 0 20 true (-2),
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 true (1),
.cycle 11 4 true (-2),
.last 16 (1,true),
.cycle 10 7 false (0),
.cycle 0 24 true (-3),
.cycle 15 1 false (-3),
.cycle 12 3 false (-1),
.cycle 11 4 false (-1),
.last 33 (1,true),
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 0 20 true (-2),
.cycle 19 1 true (1),
.cycle 9 6 false (1)
])
theorem kid04_part190_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part190) = true := by rfl

def kid04_part191 : Audit := .split 13 (5,true) (byMove [
.cycle 10 11 false (0),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 20 1 false (-2),
.cycle 10 4 false (0),
.cycle 11 4 false (-1),
.last 15 (1,true),
.cycle 7 8 false (3),
.cycle 0 16 true (-2),
.cycle 10 9 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 17 3 true (1),
.cycle 10 6 false (0),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 0 18 true (-2),
.cycle 10 4 false (0),
.cycle 11 4 false (-1),
.last 15 (1,true),
.cycle 1 32 false (3),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.cycle 13 6 true (-1),
.cycle 9 8 false (1)
])
theorem kid04_part191_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part191) = true := by rfl

def kid04_part167 : Audit := .split 12 (4,false) (byMove [(kid04_part168),(kid04_part169),(kid04_part170),(kid04_part171),(kid04_part172),(kid04_part173),(kid04_part174),(kid04_part175),(kid04_part176),(kid04_part177),(kid04_part178),(kid04_part179),(kid04_part180),(kid04_part181),(kid04_part182),(kid04_part183),(kid04_part184),(kid04_part185),(kid04_part186),(kid04_part187),(kid04_part188),(kid04_part189),(kid04_part190),(kid04_part191)])

theorem kid04_part167_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part167) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 12 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid04_part168),(kid04_part169),(kid04_part170),(kid04_part171),(kid04_part172),(kid04_part173),(kid04_part174),(kid04_part175),(kid04_part176),(kid04_part177),(kid04_part178),(kid04_part179),(kid04_part180),(kid04_part181),(kid04_part182),(kid04_part183),(kid04_part184),(kid04_part185),(kid04_part186),(kid04_part187),(kid04_part188),(kid04_part189),(kid04_part190),(kid04_part191)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part168_checked

  · exact kid04_part174_checked

  · exact kid04_part180_checked

  · exact kid04_part186_checked

  · exact kid04_part169_checked

  · exact kid04_part175_checked

  · exact kid04_part181_checked

  · exact kid04_part187_checked

  · exact kid04_part170_checked

  · exact kid04_part176_checked

  · exact kid04_part182_checked

  · exact kid04_part188_checked

  · exact kid04_part171_checked

  · exact kid04_part177_checked

  · exact kid04_part183_checked

  · exact kid04_part189_checked

  · exact kid04_part172_checked

  · exact kid04_part178_checked

  · exact kid04_part184_checked

  · exact kid04_part190_checked

  · exact kid04_part173_checked

  · exact kid04_part179_checked

  · exact kid04_part185_checked

  · exact kid04_part191_checked

def kid04_part193 : Audit := .cycle 0 16 false (3)
theorem kid04_part193_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part193) = true := by rfl

def kid04_part194 : Audit := .cycle 0 14 true (-1)
theorem kid04_part194_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part194) = true := by rfl

def kid04_part195 : Audit := .cycle 12 1 false (0)
theorem kid04_part195_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part195) = true := by rfl

def kid04_part196 : Audit := .cycle 11 1 false (-1)
theorem kid04_part196_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part196) = true := by rfl

def kid04_part197 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 12 1 false (0),
.last 13 (1,true),
.cycle 15 1 false (-3),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 13 (1,true),
.cycle 1 16 false (3),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 9 3 false (1)
])
theorem kid04_part197_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part197) = true := by rfl

def kid04_part198 : Audit := .cycle 11 1 false (-1)
theorem kid04_part198_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part198) = true := by rfl

def kid04_part199 : Audit := .cycle 19 1 false (1)
theorem kid04_part199_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part199) = true := by rfl

def kid04_part200 : Audit := .split 11 (1,true) (byMove [
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
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 22 1 false (2),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid04_part200_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part200) = true := by rfl

def kid04_part201 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 21 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 true (0),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 23 1 false (1),
.cycle 12 1 true (0),
.cycle 9 4 true (0)
])
theorem kid04_part201_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part201) = true := by rfl

def kid04_part202 : Audit := .cycle 0 12 true (0)
theorem kid04_part202_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part202) = true := by rfl

def kid04_part203 : Audit := .cycle 12 1 false (0)
theorem kid04_part203_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part203) = true := by rfl

def kid04_part204 : Audit := .cycle 12 1 false (2)
theorem kid04_part204_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part204) = true := by rfl

def kid04_part205 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (-1),
.cycle 22 1 false (-2),
.last 14 (4,false),
.cycle 0 17 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 6 20 false (3),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 32, 64],[33, 33, 16, 33, 32, 1, 64],80⟩,
.last 14 (4,false),
.cycle 0 14 true (-1),
.cycle 8 5 false (2),
.cycle 22 1 false (-2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 26 1 false (-2),
.cycle 0 33 true (-2),
.cycle 2 16 false (3),
.cycle 0 14 true (-1),
.cycle 18 1 false (-2),
.cycle 25 1 false (-3)
])
theorem kid04_part205_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part205) = true := by rfl

def kid04_part206 : Audit := .cycle 14 1 false (-2)
theorem kid04_part206_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part206) = true := by rfl

def kid04_part207 : Audit := .cycle 21 1 false (1)
theorem kid04_part207_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part207) = true := by rfl

def kid04_part208 : Audit := .cycle 11 1 false (-1)
theorem kid04_part208_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part208) = true := by rfl

def kid04_part209 : Audit := .split 11 (4,false) (byMove [
.cycle 10 6 false (0),
.cycle 24 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.last 12 (1,true),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.cycle 13 1 false (-1),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 2 16 false (3),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 5 20 false (3),
.cycle 10 3 false (0),
.cycle 14 1 false (-2)
])
theorem kid04_part209_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part209) = true := by rfl

def kid04_part210 : Audit := .cycle 11 1 false (-1)
theorem kid04_part210_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part210) = true := by rfl

def kid04_part211 : Audit := .cycle 2 10 true (0)
theorem kid04_part211_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part211) = true := by rfl

def kid04_part212 : Audit := .split 11 (1,true) (byMove [
.cycle 20 1 false (0),
.cycle 21 1 false (-1),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 1 12 true (0),
.cycle 0 12 true (0),
.far true 1 ⟨0,[0, 0],[0, 32, 40, 8, 64, 32, 64],[32, 32, 16, 32, 32, 0, 64],80⟩,
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 12 (4,false),
.cycle 1 16 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 13 (4,false),
.cycle 21 1 false (1),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 27 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid04_part212_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part212) = true := by rfl

def kid04_part213 : Audit := .cycle 13 1 false (-1)
theorem kid04_part213_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part213) = true := by rfl

def kid04_part214 : Audit := .cycle 0 12 true (0)
theorem kid04_part214_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part214) = true := by rfl

def kid04_part215 : Audit := .split 13 (4,false) (byMove [
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.last 28 (1,true),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 13 1 true (1),
.cycle 12 8 true (0),
.cycle 17 1 false (-1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 23 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 31 true (0),
.cycle 13 1 true (1),
.cycle 9 5 true (0)
])
theorem kid04_part215_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part215) = true := by rfl

def kid04_part216 : Audit := .cycle 9 3 true (0)
theorem kid04_part216_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part216) = true := by rfl

def kid04_part192 : Audit := .split 10 (5,true) (byMove [(kid04_part193),(kid04_part194),(kid04_part195),(kid04_part196),(kid04_part197),(kid04_part198),(kid04_part199),(kid04_part200),(kid04_part201),(kid04_part202),(kid04_part203),(kid04_part204),(kid04_part205),(kid04_part206),(kid04_part207),(kid04_part208),(kid04_part209),(kid04_part210),(kid04_part211),(kid04_part212),(kid04_part213),(kid04_part214),(kid04_part215),(kid04_part216)])

theorem kid04_part192_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part192) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part193),(kid04_part194),(kid04_part195),(kid04_part196),(kid04_part197),(kid04_part198),(kid04_part199),(kid04_part200),(kid04_part201),(kid04_part202),(kid04_part203),(kid04_part204),(kid04_part205),(kid04_part206),(kid04_part207),(kid04_part208),(kid04_part209),(kid04_part210),(kid04_part211),(kid04_part212),(kid04_part213),(kid04_part214),(kid04_part215),(kid04_part216)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part193_checked

  · exact kid04_part199_checked

  · exact kid04_part205_checked

  · exact kid04_part211_checked

  · exact kid04_part194_checked

  · exact kid04_part200_checked

  · exact kid04_part206_checked

  · exact kid04_part212_checked

  · exact kid04_part195_checked

  · exact kid04_part201_checked

  · exact kid04_part207_checked

  · exact kid04_part213_checked

  · exact kid04_part196_checked

  · exact kid04_part202_checked

  · exact kid04_part208_checked

  · exact kid04_part214_checked

  · exact kid04_part197_checked

  · exact kid04_part203_checked

  · exact kid04_part209_checked

  · exact kid04_part215_checked

  · exact kid04_part198_checked

  · exact kid04_part204_checked

  · exact kid04_part210_checked

  · exact kid04_part216_checked

def kid04_part217 : Audit := .cycle 0 10 true (0)
theorem kid04_part217_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part217) = true := by rfl

def kid04_part218 : Audit := .cycle 1 9 true (1)
theorem kid04_part218_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part218) = true := by rfl

def kid04_part219 : Audit := .cycle 2 8 true (1)
theorem kid04_part219_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part219) = true := by rfl

def kid04_part220 : Audit := .cycle 2 11 true (1)
theorem kid04_part220_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part220) = true := by rfl

def kid04_part222 : Audit := .cycle 2 10 true (1)
theorem kid04_part222_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part222) = true := by rfl

def kid04_part223 : Audit := .split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 26 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 12 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 9 3 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 31 (5,true),
.cycle 24 1 false (0),
.cycle 14 12 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
])
theorem kid04_part223_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part223) = true := by rfl

def kid04_part224 : Audit := .cycle 18 1 false (-2)
theorem kid04_part224_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part224) = true := by rfl

def kid04_part225 : Audit := .cycle 0 12 true (0)
theorem kid04_part225_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part225) = true := by rfl

def kid04_part226 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 13 true (0),
.cycle 20 3 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 3 false (2),
.last 14 (1,true),
.cycle 15 3 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 22 3 false (2),
.cycle 13 3 false (1),
.cycle 9 4 true (0)
])
theorem kid04_part226_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part226) = true := by rfl

def kid04_part227 : Audit := .split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 4 true (1),
.cycle 9 3 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 26 true (-3),
.cycle 24 1 false (0),
.cycle 13 4 false (0),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
])
theorem kid04_part227_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part227) = true := by rfl

def kid04_part228 : Audit := .cycle 0 11 true (0)
theorem kid04_part228_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part228) = true := by rfl

def kid04_part229 : Audit := .cycle 1 10 true (1)
theorem kid04_part229_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part229) = true := by rfl

def kid04_part230 : Audit := .cycle 0 23 true (0)
theorem kid04_part230_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part230) = true := by rfl

def kid04_part231 : Audit := .cycle 3 8 true (1)
theorem kid04_part231_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part231) = true := by rfl

def kid04_part232 : Audit := .cycle 10 1 true (2)
theorem kid04_part232_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part232) = true := by rfl

def kid04_part233 : Audit := .cycle 9 2 true (1)
theorem kid04_part233_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part233) = true := by rfl

def kid04_part234 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 17 (1,true),
.cycle 15 5 false (0),
.cycle 0 15 true (0),
.cycle 20 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 17 (1,true),
.cycle 15 5 false (2),
.last 16 (1,true),
.cycle 16 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 17 (1,true),
.cycle 13 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 22 5 false (3),
.cycle 15 5 false (1),
.cycle 9 6 true (0)
])
theorem kid04_part234_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part234) = true := by rfl

def kid04_part235 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.cycle 21 1 false (-3),
.cycle 0 16 true (0),
.cycle 12 7 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.cycle 36 13 true (0),
.cycle 19 1 false (-1),
.cycle 12 7 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid04_part235_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part235) = true := by rfl

def kid04_part236 : Audit := .split 20 (1,true) (byMove [
.cycle 11 16 true (-3),
.cycle 11 17 false (1),
.proven (BB6.Agent11Raw39B1RCPumps.M70.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M70.never m hm),
.last 26 (5,true),
.cycle 12 9 false (0),
.last 21 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 385, 1, 1024, 8192, 16384, 8, 384, 1, 65536, 524288, 1048576, 512, 256, 1, 4194304, 524288, 1048576, 2097152, 18628608, 17039360, 4194304, 16777216],[256, 1, 128, 1, 1, 16777216, 16384, 1, 128, 1, 17039360, 16777216, 1048576, 64, 17301504, 64, 16777216, 16777216, 1048576, 262144, 17301504, 262144, 17039360, 16777216, 16777216],33435712⟩,
.cycle 7 15 false (3),
.cycle 0 23 true (-3),
.cycle 11 14 true (-3),
.cycle 41 29 true (0),
.last 23 (5,true),
.cycle 11 11 false (1),
.cycle 11 12 false (1),
.cycle 15 6 true (-3),
.cycle 50 17 true (2),
.cycle 12 9 false (0),
.last 21 (5,true),
.last 36 (5,true),
.last 24 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1327513985, 1, 1024, 8192, 16384, 8, 256, 16385, 65536, 33554432, 67108864, 2097152, 256, 16385, 268435456, 8192, 16384, 8, 2097280, 1, 65536, 33554432, 67108864, 134217728, 1325416448, 1157627904, 268435456, 1073741824],[256, 256, 2097280, 1, 16385, 1073741824, 16384, 16384, 2097280, 1, 1073741824, 1073741824, 67108864, 67108864, 1241513984, 262144, 1073741824, 1073741824, 16384, 16384, 2097280, 1, 1157627904, 1073741824, 67108864, 67108864, 1241513984, 16777216, 1157627904, 1073741824, 1073741824],2132194126⟩,
.cycle 4 17 false (3),
.cycle 10 11 false (2),
.last 23 (5,true)
])
theorem kid04_part236_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part236) = true := by rfl

def kid04_part237 : Audit := .cycle 2 11 true (1)
theorem kid04_part237_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part237) = true := by rfl

def kid04_part238 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 14 (1,true),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 16 3 false (3),
.last 14 (1,true),
.cycle 15 3 false (-1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.last 14 (1,true),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.cycle 13 3 false (1),
.cycle 9 7 true (0)
])
theorem kid04_part238_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part238) = true := by rfl

def kid04_part239 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 18 1 false (-2),
.last 14 (1,true),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 9 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 33 true (-3),
.cycle 19 1 false (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 5 false (2),
.cycle 0 13 true (0),
.cycle 10 4 true (1),
.cycle 9 4 true (1)
])
theorem kid04_part239_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part239) = true := by rfl

def kid04_part240 : Audit := .cycle 0 11 true (0)
theorem kid04_part240_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part240) = true := by rfl

def kid04_part241 : Audit := .cycle 1 10 true (1)
theorem kid04_part241_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part241) = true := by rfl

def kid04_part242 : Audit := .cycle 2 9 true (1)
theorem kid04_part242_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part242) = true := by rfl

def kid04_part243 : Audit := .cycle 2 12 true (1)
theorem kid04_part243_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part243) = true := by rfl

def kid04_part244 : Audit := .cycle 10 1 true (2)
theorem kid04_part244_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part244) = true := by rfl

def kid04_part245 : Audit := .cycle 9 2 true (1)
theorem kid04_part245_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part245) = true := by rfl

def kid04_part221 : Audit := .split 10 (4,false) (byMove [(kid04_part222),(kid04_part223),(kid04_part224),(kid04_part225),(kid04_part226),(kid04_part227),(kid04_part228),(kid04_part229),(kid04_part230),(kid04_part231),(kid04_part232),(kid04_part233),(kid04_part234),(kid04_part235),(kid04_part236),(kid04_part237),(kid04_part238),(kid04_part239),(kid04_part240),(kid04_part241),(kid04_part242),(kid04_part243),(kid04_part244),(kid04_part245)])

theorem kid04_part221_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part221) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid04_part222),(kid04_part223),(kid04_part224),(kid04_part225),(kid04_part226),(kid04_part227),(kid04_part228),(kid04_part229),(kid04_part230),(kid04_part231),(kid04_part232),(kid04_part233),(kid04_part234),(kid04_part235),(kid04_part236),(kid04_part237),(kid04_part238),(kid04_part239),(kid04_part240),(kid04_part241),(kid04_part242),(kid04_part243),(kid04_part244),(kid04_part245)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part222_checked

  · exact kid04_part228_checked

  · exact kid04_part234_checked

  · exact kid04_part240_checked

  · exact kid04_part223_checked

  · exact kid04_part229_checked

  · exact kid04_part235_checked

  · exact kid04_part241_checked

  · exact kid04_part224_checked

  · exact kid04_part230_checked

  · exact kid04_part236_checked

  · exact kid04_part242_checked

  · exact kid04_part225_checked

  · exact kid04_part231_checked

  · exact kid04_part237_checked

  · exact kid04_part243_checked

  · exact kid04_part226_checked

  · exact kid04_part232_checked

  · exact kid04_part238_checked

  · exact kid04_part244_checked

  · exact kid04_part227_checked

  · exact kid04_part233_checked

  · exact kid04_part239_checked

  · exact kid04_part245_checked

def kid04_part246 : Audit := .cycle 9 1 true (1)
theorem kid04_part246_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part246) = true := by rfl

def kid04_part78 : Audit := .split 9 (5,false) (byMove [(kid04_part79),(kid04_part80),(kid04_part81),(kid04_part82),(kid04_part83),(kid04_part84),(kid04_part85),(kid04_part86),(kid04_part87),(kid04_part88),(kid04_part89),(kid04_part90),(kid04_part91),(kid04_part116),(kid04_part141),(kid04_part166),(kid04_part167),(kid04_part192),(kid04_part217),(kid04_part218),(kid04_part219),(kid04_part220),(kid04_part221),(kid04_part246)])

theorem kid04_part78_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (kid04_part78) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part79),(kid04_part80),(kid04_part81),(kid04_part82),(kid04_part83),(kid04_part84),(kid04_part85),(kid04_part86),(kid04_part87),(kid04_part88),(kid04_part89),(kid04_part90),(kid04_part91),(kid04_part116),(kid04_part141),(kid04_part166),(kid04_part167),(kid04_part192),(kid04_part217),(kid04_part218),(kid04_part219),(kid04_part220),(kid04_part221),(kid04_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part79_checked

  · exact kid04_part85_checked

  · exact kid04_part91_checked

  · exact kid04_part217_checked

  · exact kid04_part80_checked

  · exact kid04_part86_checked

  · exact kid04_part116_checked

  · exact kid04_part218_checked

  · exact kid04_part81_checked

  · exact kid04_part87_checked

  · exact kid04_part141_checked

  · exact kid04_part219_checked

  · exact kid04_part82_checked

  · exact kid04_part88_checked

  · exact kid04_part166_checked

  · exact kid04_part220_checked

  · exact kid04_part83_checked

  · exact kid04_part89_checked

  · exact kid04_part167_checked

  · exact kid04_part221_checked

  · exact kid04_part84_checked

  · exact kid04_part90_checked

  · exact kid04_part192_checked

  · exact kid04_part246_checked

def kid04_part247 : Audit := .cycle 0 9 true (0)
theorem kid04_part247_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,0⟩)) (kid04_part247) = true := by rfl

def kid04_part248 : Audit := .cycle 1 8 true (1)
theorem kid04_part248_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,1⟩)) (kid04_part248) = true := by rfl

def kid04_part249 : Audit := .cycle 29 1 false (7)
theorem kid04_part249_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,2⟩)) (kid04_part249) = true := by rfl

def kid04_part250 : Audit := .cycle 16 1 false (2)
theorem kid04_part250_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,3⟩)) (kid04_part250) = true := by rfl

def kid04_part252 : Audit := .cycle 0 10 true (0)
theorem kid04_part252_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part252) = true := by rfl

def kid04_part253 : Audit := .cycle 1 9 true (1)
theorem kid04_part253_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part253) = true := by rfl

def kid04_part254 : Audit := .cycle 20 1 false (2)
theorem kid04_part254_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part254) = true := by rfl

def kid04_part255 : Audit := .cycle 17 1 false (1)
theorem kid04_part255_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part255) = true := by rfl

def kid04_part256 : Audit := .cycle 13 1 false (1)
theorem kid04_part256_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part256) = true := by rfl

def kid04_part258 : Audit := .cycle 0 11 true (0)
theorem kid04_part258_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part258) = true := by rfl

def kid04_part259 : Audit := .cycle 1 10 true (1)
theorem kid04_part259_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part259) = true := by rfl

def kid04_part260 : Audit := .cycle 21 1 false (1)
theorem kid04_part260_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part260) = true := by rfl

def kid04_part261 : Audit := .cycle 23 1 false (1)
theorem kid04_part261_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part261) = true := by rfl

def kid04_part262 : Audit := .split 12 (5,true) (byMove [
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
.last 14 (1,true),
.cycle 16 2 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 2 false (2),
.cycle 23 2 false (3),
.cycle 11 2 true (0),
.cycle 15 2 false (1)
])
theorem kid04_part262_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part262) = true := by rfl

def kid04_part263 : Audit := .split 12 (5,true) (byMove [
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
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 12 2 true (0),
.cycle 11 2 true (0)
])
theorem kid04_part263_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part263) = true := by rfl

def kid04_part264 : Audit := .cycle 0 11 true (0)
theorem kid04_part264_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part264) = true := by rfl

def kid04_part265 : Audit := .cycle 1 10 true (1)
theorem kid04_part265_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part265) = true := by rfl

def kid04_part266 : Audit := .cycle 35 1 false (7)
theorem kid04_part266_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part266) = true := by rfl

def kid04_part267 : Audit := .cycle 20 1 false (2)
theorem kid04_part267_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part267) = true := by rfl

def kid04_part268 : Audit := .cycle 9 2 true (2)
theorem kid04_part268_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part268) = true := by rfl

def kid04_part269 : Audit := .cycle 10 1 true (2)
theorem kid04_part269_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part269) = true := by rfl

def kid04_part270 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 15 5 false (1),
.cycle 0 14 true (0),
.cycle 18 5 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 18 9 false (2),
.cycle 10 3 true (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 15 5 false (1),
.cycle 2 13 true (1),
.cycle 8 6 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 18 13 false (2)
])
theorem kid04_part270_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part270) = true := by rfl

def kid04_part271 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 23 5 false (3),
.cycle 24 5 false (4),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.last 17 (5,true),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 25 5 false (3),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 13 4 true (0),
.last 17 (5,true)
])
theorem kid04_part271_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part271) = true := by rfl

def kid04_part272 : Audit := .cycle 0 13 true (0)
theorem kid04_part272_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part272) = true := by rfl

def kid04_part273 : Audit := .cycle 18 1 false (0)
theorem kid04_part273_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part273) = true := by rfl

def kid04_part274 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 16 2 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 14 (1,true),
.cycle 16 2 false (0),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 20 2 false (2),
.cycle 0 15 true (0),
.cycle 18 2 false (2),
.cycle 11 2 true (0),
.cycle 17 2 false (3)
])
theorem kid04_part274_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part274) = true := by rfl

def kid04_part275 : Audit := .split 12 (5,true) (byMove [
.cycle 11 7 false (1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 23 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 2 18 true (0),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.cycle 8 6 true (0),
.cycle 13 3 true (1)
])
theorem kid04_part275_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part275) = true := by rfl

def kid04_part276 : Audit := .cycle 0 11 true (0)
theorem kid04_part276_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part276) = true := by rfl

def kid04_part277 : Audit := .cycle 1 10 true (1)
theorem kid04_part277_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part277) = true := by rfl

def kid04_part278 : Audit := .cycle 2 9 true (1)
theorem kid04_part278_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part278) = true := by rfl

def kid04_part279 : Audit := .cycle 2 12 true (1)
theorem kid04_part279_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part279) = true := by rfl

def kid04_part280 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 13 4 false (1),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 0, 16, 64],[4, 64, 0, 1, 16, 16, 64],64⟩,
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.cycle 10 3 true (2)
])
theorem kid04_part280_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part280) = true := by rfl

def kid04_part281 : Audit := .cycle 10 1 true (2)
theorem kid04_part281_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part281) = true := by rfl

def kid04_part257 : Audit := .split 10 (5,false) (byMove [(kid04_part258),(kid04_part259),(kid04_part260),(kid04_part261),(kid04_part262),(kid04_part263),(kid04_part264),(kid04_part265),(kid04_part266),(kid04_part267),(kid04_part268),(kid04_part269),(kid04_part270),(kid04_part271),(kid04_part272),(kid04_part273),(kid04_part274),(kid04_part275),(kid04_part276),(kid04_part277),(kid04_part278),(kid04_part279),(kid04_part280),(kid04_part281)])

theorem kid04_part257_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part257) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part258),(kid04_part259),(kid04_part260),(kid04_part261),(kid04_part262),(kid04_part263),(kid04_part264),(kid04_part265),(kid04_part266),(kid04_part267),(kid04_part268),(kid04_part269),(kid04_part270),(kid04_part271),(kid04_part272),(kid04_part273),(kid04_part274),(kid04_part275),(kid04_part276),(kid04_part277),(kid04_part278),(kid04_part279),(kid04_part280),(kid04_part281)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part258_checked

  · exact kid04_part264_checked

  · exact kid04_part270_checked

  · exact kid04_part276_checked

  · exact kid04_part259_checked

  · exact kid04_part265_checked

  · exact kid04_part271_checked

  · exact kid04_part277_checked

  · exact kid04_part260_checked

  · exact kid04_part266_checked

  · exact kid04_part272_checked

  · exact kid04_part278_checked

  · exact kid04_part261_checked

  · exact kid04_part267_checked

  · exact kid04_part273_checked

  · exact kid04_part279_checked

  · exact kid04_part262_checked

  · exact kid04_part268_checked

  · exact kid04_part274_checked

  · exact kid04_part280_checked

  · exact kid04_part263_checked

  · exact kid04_part269_checked

  · exact kid04_part275_checked

  · exact kid04_part281_checked

def kid04_part282 : Audit := .cycle 0 10 true (0)
theorem kid04_part282_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part282) = true := by rfl

def kid04_part283 : Audit := .cycle 1 9 true (1)
theorem kid04_part283_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part283) = true := by rfl

def kid04_part284 : Audit := .cycle 35 1 false (9)
theorem kid04_part284_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part284) = true := by rfl

def kid04_part285 : Audit := .cycle 29 1 false (7)
theorem kid04_part285_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part285) = true := by rfl

def kid04_part286 : Audit := .cycle 9 1 true (3)
theorem kid04_part286_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part286) = true := by rfl

def kid04_part288 : Audit := .cycle 0 11 true (0)
theorem kid04_part288_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part288) = true := by rfl

def kid04_part289 : Audit := .cycle 1 10 true (1)
theorem kid04_part289_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part289) = true := by rfl

def kid04_part290 : Audit := .split 21 (5,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (7),
.last 22 (1,true),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.last 23 (1,true),
.cycle 33 1 false (5),
.cycle 35 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 24 1 false (2),
.cycle 2 21 true (0),
.last 22 (1,true),
.cycle 27 1 false (5),
.cycle 0 23 true (0),
.cycle 47 1 false (9),
.cycle 29 1 false (5)
])
theorem kid04_part290_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part290) = true := by rfl

def kid04_part291 : Audit := .split 19 (5,true) (byMove [
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
.last 21 (1,true),
.cycle 25 1 false (3),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 32 1 false (6),
.cycle 34 1 false (6),
.cycle 0 22 true (0)
])
theorem kid04_part291_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part291) = true := by rfl

def kid04_part292 : Audit := .cycle 9 2 true (3)
theorem kid04_part292_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part292) = true := by rfl

def kid04_part293 : Audit := .split 14 (5,true) (byMove [
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
.last 16 (1,true),
.cycle 19 1 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 26 1 false (4),
.cycle 12 4 true (0),
.cycle 13 2 true (0)
])
theorem kid04_part293_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part293) = true := by rfl

def kid04_part294 : Audit := .cycle 0 11 true (0)
theorem kid04_part294_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part294) = true := by rfl

def kid04_part295 : Audit := .cycle 1 10 true (1)
theorem kid04_part295_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part295) = true := by rfl

def kid04_part296 : Audit := .split 23 (5,true) (byMove [
.cycle 0 54 true (0),
.cycle 0 127 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 36 1 false (8),
.cycle 33 1 false (9),
.cycle 0 29 true (0),
.last 24 (1,true),
.cycle 34 1 false (8),
.cycle 31 1 false (9),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.last 25 (1,true),
.cycle 45 1 false (9),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 22 2 true (2),
.cycle 38 1 false (8),
.cycle 0 29 true (0),
.last 24 (1,true),
.cycle 33 1 false (9),
.cycle 5 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 36, 1, 16, 16, 64],64⟩,
.cycle 26 11 true (6)
])
theorem kid04_part296_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part296) = true := by rfl

def kid04_part297 : Audit := .split 21 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 91 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 35 1 false (9),
.cycle 23 1 false (3),
.cycle 27 1 false (7),
.last 22 (1,true),
.cycle 0 26 true (0),
.cycle 33 1 false (9),
.cycle 26 1 false (8),
.cycle 25 1 false (7),
.last 23 (1,true),
.cycle 37 1 false (7),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 29 1 false (7),
.cycle 2 36 true (0),
.last 22 (1,true),
.cycle 35 1 false (9),
.cycle 5 40 true (0),
.cycle 8 15 true (0),
.cycle 3 22 true (0)
])
theorem kid04_part297_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part297) = true := by rfl

def kid04_part298 : Audit := .cycle 9 2 true (3)
theorem kid04_part298_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part298) = true := by rfl

def kid04_part299 : Audit := .cycle 10 1 true (4)
theorem kid04_part299_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part299) = true := by rfl

def kid04_part300 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 25 5 false (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.last 18 (5,true),
.last 26 (5,true),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 6 8 true (2)
])
theorem kid04_part300_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part300) = true := by rfl

def kid04_part301 : Audit := .cycle 7 5 true (2)
theorem kid04_part301_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part301) = true := by rfl

def kid04_part302 : Audit := .cycle 0 13 true (0)
theorem kid04_part302_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part302) = true := by rfl

def kid04_part303 : Audit := .split 19 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 30 1 false (6),
.last 20 (1,true),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 21 (1,true),
.cycle 30 1 false (4),
.cycle 32 1 false (6),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 21 1 false (1),
.cycle 2 19 true (0),
.last 20 (1,true),
.cycle 24 1 false (4),
.cycle 0 21 true (0),
.cycle 40 1 false (8),
.cycle 19 24 true (3)
])
theorem kid04_part303_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part303) = true := by rfl

def kid04_part304 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 9 4 true (3),
.cycle 23 3 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 37 1 false (9),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 11 2 true (3),
.cycle 26 3 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 8 7 true (2)
])
theorem kid04_part304_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part304) = true := by rfl

def kid04_part305 : Audit := .split 14 (5,true) (byMove [
.cycle 0 27 true (-1),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 29 1 false (7),
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.last 16 (1,true),
.cycle 39 1 false (5),
.cycle 33 1 false (7),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 15 1 false (-1),
.cycle 2 19 true (0),
.last 15 (1,true),
.cycle 31 1 false (7),
.cycle 14 32 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 48, 1, 16, 16, 64],64⟩,
.cycle 17 3 true (3)
])
theorem kid04_part305_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part305) = true := by rfl

def kid04_part306 : Audit := .cycle 0 11 true (0)
theorem kid04_part306_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part306) = true := by rfl

def kid04_part307 : Audit := .cycle 1 10 true (1)
theorem kid04_part307_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part307) = true := by rfl

def kid04_part308 : Audit := .cycle 2 9 true (1)
theorem kid04_part308_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part308) = true := by rfl

def kid04_part309 : Audit := .cycle 2 12 true (1)
theorem kid04_part309_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part309) = true := by rfl

def kid04_part310 : Audit := .cycle 9 2 true (3)
theorem kid04_part310_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part310) = true := by rfl

def kid04_part311 : Audit := .cycle 10 1 true (4)
theorem kid04_part311_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part311) = true := by rfl

def kid04_part287 : Audit := .split 10 (5,false) (byMove [(kid04_part288),(kid04_part289),(kid04_part290),(kid04_part291),(kid04_part292),(kid04_part293),(kid04_part294),(kid04_part295),(kid04_part296),(kid04_part297),(kid04_part298),(kid04_part299),(kid04_part300),(kid04_part301),(kid04_part302),(kid04_part303),(kid04_part304),(kid04_part305),(kid04_part306),(kid04_part307),(kid04_part308),(kid04_part309),(kid04_part310),(kid04_part311)])

theorem kid04_part287_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part287) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part288),(kid04_part289),(kid04_part290),(kid04_part291),(kid04_part292),(kid04_part293),(kid04_part294),(kid04_part295),(kid04_part296),(kid04_part297),(kid04_part298),(kid04_part299),(kid04_part300),(kid04_part301),(kid04_part302),(kid04_part303),(kid04_part304),(kid04_part305),(kid04_part306),(kid04_part307),(kid04_part308),(kid04_part309),(kid04_part310),(kid04_part311)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part288_checked

  · exact kid04_part294_checked

  · exact kid04_part300_checked

  · exact kid04_part306_checked

  · exact kid04_part289_checked

  · exact kid04_part295_checked

  · exact kid04_part301_checked

  · exact kid04_part307_checked

  · exact kid04_part290_checked

  · exact kid04_part296_checked

  · exact kid04_part302_checked

  · exact kid04_part308_checked

  · exact kid04_part291_checked

  · exact kid04_part297_checked

  · exact kid04_part303_checked

  · exact kid04_part309_checked

  · exact kid04_part292_checked

  · exact kid04_part298_checked

  · exact kid04_part304_checked

  · exact kid04_part310_checked

  · exact kid04_part293_checked

  · exact kid04_part299_checked

  · exact kid04_part305_checked

  · exact kid04_part311_checked

def kid04_part312 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 17 4 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 20 3 false (1),
.last 21 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 19 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 9 4 true (2),
.cycle 12 1 true (4),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 20 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.cycle 17 4 false (1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 17 4 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.last 14 (5,false),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 14 (5,false),
.cycle 20 3 false (1),
.last 21 (5,false),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 11 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 6 7 true (2),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 18 (5,true),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
])
theorem kid04_part312_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part312) = true := by rfl

def kid04_part313 : Audit := .cycle 7 4 true (2)
theorem kid04_part313_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part313) = true := by rfl

def kid04_part314 : Audit := .cycle 0 12 true (0)
theorem kid04_part314_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part314) = true := by rfl

def kid04_part315 : Audit := .cycle 17 1 false (1)
theorem kid04_part315_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part315) = true := by rfl

def kid04_part316 : Audit := .cycle 16 1 false (4)
theorem kid04_part316_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part316) = true := by rfl

def kid04_part318 : Audit := .cycle 0 20 true (0)
theorem kid04_part318_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part318) = true := by rfl

def kid04_part319 : Audit := .cycle 0 14 true (0)
theorem kid04_part319_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part319) = true := by rfl

def kid04_part320 : Audit := .cycle 21 1 false (1)
theorem kid04_part320_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part320) = true := by rfl

def kid04_part321 : Audit := .cycle 0 16 true (0)
theorem kid04_part321_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part321) = true := by rfl

def kid04_part322 : Audit := .split 12 (5,true) (byMove [
.cycle 20 2 false (0),
.last 17 (1,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 14 2 false (0),
.last 15 (1,true),
.cycle 14 2 false (2),
.cycle 14 2 false (2),
.last 14 (1,true),
.cycle 16 2 false (0),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 15 2 false (1),
.last 15 (1,true),
.cycle 17 2 false (1),
.cycle 19 2 false (1)
])
theorem kid04_part322_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part322) = true := by rfl

def kid04_part323 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 21 (1,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 17 1 false (-1),
.last 25 (1,true),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 21 (1,true),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 11 2 true (0)
])
theorem kid04_part323_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part323) = true := by rfl

def kid04_part324 : Audit := .cycle 2 10 true (1)
theorem kid04_part324_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part324) = true := by rfl

def kid04_part325 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 43 1 false (9),
.cycle 35 1 false (7),
.cycle 9 3 true (2),
.cycle 1 12 true (1),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 1 12 true (1)
])
theorem kid04_part325_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part325) = true := by rfl

def kid04_part326 : Audit := .split 16 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 3 false (-1),
.cycle 0 20 true (-1),
.cycle 25 3 false (3),
.last 17 (1,true),
.cycle 17 3 false (1),
.cycle 0 18 true (0),
.cycle 18 3 false (2),
.cycle 20 1 false (4),
.last 18 (1,true),
.cycle 20 3 false (0),
.cycle 27 3 false (3),
.cycle 17 1 false (-1),
.cycle 17 3 false (-1),
.cycle 17 3 false (0),
.cycle 2 16 true (0),
.last 17 (1,true),
.cycle 19 3 false (1),
.cycle 0 18 true (0),
.cycle 12 6 true (0),
.cycle 0 39 true (0)
])
theorem kid04_part326_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part326) = true := by rfl

def kid04_part327 : Audit := .cycle 0 12 true (0)
theorem kid04_part327_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part327) = true := by rfl

def kid04_part328 : Audit := .cycle 8 3 true (2)
theorem kid04_part328_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part328) = true := by rfl

def kid04_part329 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 3 false (0),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 43 1 false (9),
.cycle 35 1 false (7),
.cycle 9 3 true (2),
.cycle 12 1 true (4),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 3 false (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.cycle 12 1 true (4)
])
theorem kid04_part329_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part329) = true := by rfl

def kid04_part330 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.cycle 15 5 false (1),
.cycle 0 17 true (0),
.cycle 18 5 false (1),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 13 (5,true),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 15 5 false (1),
.cycle 5 8 true (1),
.cycle 8 7 true (1),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.cycle 34 22 true (2),
.last 13 (5,true)
])
theorem kid04_part330_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part330) = true := by rfl

def kid04_part331 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 18 5 false (2),
.cycle 26 5 false (6),
.cycle 18 5 false (0),
.cycle 19 5 false (3),
.cycle 19 5 false (4),
.last 17 (5,true),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 12 6 true (0),
.cycle 1 19 true (0),
.cycle 17 5 false (1),
.cycle 5 12 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 8, 256, 4096, 16, 4096],[256, 1024, 4112, 1, 16, 4096, 256, 1024, 16, 1, 16, 4096, 4096],5120⟩,
.last 17 (5,true)
])
theorem kid04_part331_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part331) = true := by rfl

def kid04_part332 : Audit := .cycle 2 12 true (1)
theorem kid04_part332_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part332) = true := by rfl

def kid04_part333 : Audit := .cycle 18 1 false (0)
theorem kid04_part333_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part333) = true := by rfl

def kid04_part334 : Audit := .split 12 (5,true) (byMove [
.cycle 24 2 false (4),
.cycle 28 2 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.last 13 (1,true),
.cycle 14 2 false (0),
.cycle 17 2 false (3),
.cycle 16 2 false (4),
.cycle 16 2 false (4),
.last 14 (1,true),
.cycle 16 2 false (0),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 22 2 false (4),
.last 13 (1,true),
.cycle 15 2 false (1),
.cycle 5 8 true (0),
.cycle 25 2 false (5),
.cycle 8 10 true (0)
])
theorem kid04_part334_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part334) = true := by rfl

def kid04_part335 : Audit := .split 12 (5,true) (byMove [
.cycle 11 7 false (1),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 6 true (0),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 5 8 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 14 3 true (2)
])
theorem kid04_part335_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part335) = true := by rfl

def kid04_part336 : Audit := .cycle 2 10 true (1)
theorem kid04_part336_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part336) = true := by rfl

def kid04_part337 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (5,true),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.last 14 (5,true),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 1 12 true (1)
])
theorem kid04_part337_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part337) = true := by rfl

def kid04_part338 : Audit := .cycle 7 4 true (2)
theorem kid04_part338_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part338) = true := by rfl

def kid04_part339 : Audit := .cycle 0 12 true (0)
theorem kid04_part339_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part339) = true := by rfl

def kid04_part340 : Audit := .cycle 8 3 true (2)
theorem kid04_part340_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part340) = true := by rfl

def kid04_part341 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 18 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 0 20 true (-1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.cycle 12 1 true (4)
])
theorem kid04_part341_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part341) = true := by rfl

def kid04_part317 : Audit := .split 10 (5,false) (byMove [(kid04_part318),(kid04_part319),(kid04_part320),(kid04_part321),(kid04_part322),(kid04_part323),(kid04_part324),(kid04_part325),(kid04_part326),(kid04_part327),(kid04_part328),(kid04_part329),(kid04_part330),(kid04_part331),(kid04_part332),(kid04_part333),(kid04_part334),(kid04_part335),(kid04_part336),(kid04_part337),(kid04_part338),(kid04_part339),(kid04_part340),(kid04_part341)])

theorem kid04_part317_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part317) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part318),(kid04_part319),(kid04_part320),(kid04_part321),(kid04_part322),(kid04_part323),(kid04_part324),(kid04_part325),(kid04_part326),(kid04_part327),(kid04_part328),(kid04_part329),(kid04_part330),(kid04_part331),(kid04_part332),(kid04_part333),(kid04_part334),(kid04_part335),(kid04_part336),(kid04_part337),(kid04_part338),(kid04_part339),(kid04_part340),(kid04_part341)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part318_checked

  · exact kid04_part324_checked

  · exact kid04_part330_checked

  · exact kid04_part336_checked

  · exact kid04_part319_checked

  · exact kid04_part325_checked

  · exact kid04_part331_checked

  · exact kid04_part337_checked

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

def kid04_part342 : Audit := .cycle 0 10 true (0)
theorem kid04_part342_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part342) = true := by rfl

def kid04_part343 : Audit := .cycle 1 9 true (1)
theorem kid04_part343_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part343) = true := by rfl

def kid04_part344 : Audit := .cycle 2 8 true (1)
theorem kid04_part344_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part344) = true := by rfl

def kid04_part345 : Audit := .cycle 2 11 true (1)
theorem kid04_part345_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part345) = true := by rfl

def kid04_part346 : Audit := .cycle 9 1 true (3)
theorem kid04_part346_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part346) = true := by rfl

def kid04_part347 : Audit := .split 10 (5,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 19 3 false (2),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 9 3 true (3),
.cycle 1 12 true (1),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 19 (5,true),
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 19 3 false (2),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 27 1 false (1),
.cycle 21 1 false (1),
.cycle 19 3 false (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 30 true (0),
.cycle 0 23 true (0),
.cycle 9 3 true (3),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 32 1 false (4),
.cycle 8 7 true (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (5,true) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 9 13 true (3),
.cycle 0 22 true (0),
.cycle 8 13 true (2),
.cycle 39 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.cycle 9 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 4, 64],[4, 64, 36, 1, 16, 32, 64],64⟩,
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 9 16 true (3),
.cycle 2 21 true (1),
.cycle 8 14 true (2),
.cycle 9 18 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 9 12 true (3),
.cycle 10 11 true (3)
]),
.cycle 3 8 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 21 1 false (1),
.last 20 (5,true),
.cycle 19 7 false (1),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.cycle 2 13 true (1),
.last 19 (5,true),
.last 13 (5,true),
.last 17 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true)
]),
.split 20 (5,true) (byMove [
.cycle 0 98 true (0),
.last 21 (1,true),
.cycle 21 3 false (1),
.last 23 (1,true),
.cycle 28 3 false (5),
.cycle 32 3 false (2),
.cycle 6 15 true (0),
.last 21 (1,true),
.cycle 31 10 true (2),
.cycle 0 88 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 32, 53, 64],[4, 64, 53, 1, 16, 16, 64],64⟩,
.cycle 0 26 true (0),
.cycle 34 3 false (5),
.last 21 (1,true),
.cycle 21 3 false (1),
.cycle 36 3 false (7),
.cycle 25 3 false (6),
.cycle 46 3 false (5),
.cycle 2 32 true (0),
.last 21 (1,true),
.cycle 2 23 true (0),
.cycle 5 40 true (0),
.cycle 8 14 true (0),
.cycle 22 5 true (3)
]),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.split 11 (5,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 27 1 false (1),
.cycle 21 1 false (1),
.cycle 28 3 false (5),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 24 1 false (6),
.last 13 (1,true),
.last 17 (1,true),
.cycle 2 13 true (1),
.cycle 27 1 false (3),
.cycle 8 8 true (2),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid04_part347_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part347) = true := by rfl

def kid04_part251 : Audit := .split 9 (4,false) (byMove [(kid04_part252),(kid04_part253),(kid04_part254),(kid04_part255),(kid04_part256),(kid04_part257),(kid04_part282),(kid04_part283),(kid04_part284),(kid04_part285),(kid04_part286),(kid04_part287),(kid04_part312),(kid04_part313),(kid04_part314),(kid04_part315),(kid04_part316),(kid04_part317),(kid04_part342),(kid04_part343),(kid04_part344),(kid04_part345),(kid04_part346),(kid04_part347)])

theorem kid04_part251_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (kid04_part251) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid04_part252),(kid04_part253),(kid04_part254),(kid04_part255),(kid04_part256),(kid04_part257),(kid04_part282),(kid04_part283),(kid04_part284),(kid04_part285),(kid04_part286),(kid04_part287),(kid04_part312),(kid04_part313),(kid04_part314),(kid04_part315),(kid04_part316),(kid04_part317),(kid04_part342),(kid04_part343),(kid04_part344),(kid04_part345),(kid04_part346),(kid04_part347)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part252_checked

  · exact kid04_part282_checked

  · exact kid04_part312_checked

  · exact kid04_part342_checked

  · exact kid04_part253_checked

  · exact kid04_part283_checked

  · exact kid04_part313_checked

  · exact kid04_part343_checked

  · exact kid04_part254_checked

  · exact kid04_part284_checked

  · exact kid04_part314_checked

  · exact kid04_part344_checked

  · exact kid04_part255_checked

  · exact kid04_part285_checked

  · exact kid04_part315_checked

  · exact kid04_part345_checked

  · exact kid04_part256_checked

  · exact kid04_part286_checked

  · exact kid04_part316_checked

  · exact kid04_part346_checked

  · exact kid04_part257_checked

  · exact kid04_part287_checked

  · exact kid04_part317_checked

  · exact kid04_part347_checked

def kid04_part349 : Audit := .cycle 0 10 true (0)
theorem kid04_part349_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part349) = true := by rfl

def kid04_part350 : Audit := .cycle 1 9 true (1)
theorem kid04_part350_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part350) = true := by rfl

def kid04_part351 : Audit := .cycle 20 1 false (2)
theorem kid04_part351_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part351) = true := by rfl

def kid04_part352 : Audit := .cycle 17 1 false (1)
theorem kid04_part352_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part352) = true := by rfl

def kid04_part353 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 14 1 false (0),
.cycle 13 2 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (2),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 16 4 false (0),
.cycle 0 14 true (0),
.cycle 18 5 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 10 3 true (1),
.cycle 18 9 false (2),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 16 4 false (0),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 18 13 false (2),
.cycle 19 11 false (2)
]),
.split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 23 5 false (3),
.cycle 24 5 false (4),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.last 17 (5,true),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 25 5 false (3),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 13 4 true (0),
.last 17 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 13 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 23 1 false (3),
.last 14 (1,true),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.cycle 16 1 false (2),
.cycle 16 1 false (2),
.last 15 (1,true),
.cycle 18 1 false (0),
.cycle 25 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 2 13 true (0),
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 0 15 true (0),
.cycle 16 3 true (1),
.cycle 24 1 false (2)
]),
.cycle 13 2 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (2),
.cycle 8 4 true (2)
])
theorem kid04_part353_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part353) = true := by rfl

def kid04_part354 : Audit := .split 12 (5,true) (byMove [
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
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 28 1 false (0),
.cycle 1 13 false (3),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
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
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 1 false (3),
.cycle 24 1 false (4),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
]),
.cycle 13 1 false (1),
.split 14 (1,true) (byMove [
.cycle 23 1 false (1),
.cycle 24 1 false (0),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 16 1 false (0),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 9 15 false (3),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.last 15 (4,false),
.cycle 10 5 false (2),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 24 1 false (2),
.cycle 12 4 true (-1),
.cycle 12 3 false (0),
.cycle 10 21 false (4),
.cycle 30 1 false (0),
.cycle 2 13 false (3),
.cycle 9 17 false (3),
.last 15 (4,false),
.cycle 20 1 false (0)
]),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 10 8 false (2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 22 1 false (2),
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 0 15 true (-1),
.cycle 15 1 false (1),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 2 13 false (3),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.cycle 10 5 false (2),
.cycle 12 4 true (-1)
]),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.split 13 (4,false) (byMove [
.cycle 22 1 false (2),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 15 1 false (1),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 9 14 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 13 1 true (1),
.cycle 10 4 true (0),
.cycle 17 1 false (1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 23 1 false (3),
.cycle 12 3 true (0),
.cycle 10 6 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 9 16 true (0),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
]),
.cycle 11 2 true (0)
])
theorem kid04_part354_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part354) = true := by rfl

def kid04_part355 : Audit := .cycle 0 10 true (0)
theorem kid04_part355_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part355) = true := by rfl

def kid04_part356 : Audit := .cycle 1 9 true (1)
theorem kid04_part356_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part356) = true := by rfl

def kid04_part357 : Audit := .split 22 (4,false) (byMove [
.cycle 0 61 true (0),
.cycle 55 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.split 24 (1,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 37 true (0),
.cycle 0 48 true (0),
.cycle 0 29 true (0),
.cycle 0 29 true (0),
.last 25 (5,true),
.cycle 6 44 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 1, 4, 64],[4, 2, 6, 1, 32, 64, 64],64⟩,
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 8 17 true (0),
.last 25 (5,true),
.cycle 0 31 true (0),
.cycle 0 41 true (0),
.cycle 21 4 true (2),
.cycle 31 1 false (7),
.last 26 (5,true),
.last 25 (5,true),
.cycle 2 24 true (0),
.cycle 1 25 true (0),
.cycle 2 40 true (0),
.cycle 0 26 true (0),
.cycle 0 42 true (0),
.last 25 (5,true)
]),
.cycle 39 1 false (9),
.cycle 35 1 false (9),
.cycle 23 1 false (3),
.split 25 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 26 1 true (4),
.cycle 28 1 false (6),
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.cycle 26 1 true (6),
.cycle 28 1 false (8),
.last 27 (1,true),
.cycle 31 1 false (7),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 30 1 false (8),
.cycle 28 1 true (4),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 35 1 false (9),
.cycle 38 1 false (10),
.cycle 26 1 true (6),
.cycle 37 1 true (7)
]),
.cycle 31 1 false (7),
.split 24 (1,true) (byMove [
.cycle 61 1 false (7),
.cycle 47 1 false (9),
.cycle 21 4 false (3),
.cycle 0 36 true (0),
.cycle 39 1 false (9),
.last 25 (5,true),
.cycle 6 48 true (0),
.cycle 7 60 true (0),
.cycle 0 66 true (0),
.cycle 55 1 false (7),
.last 29 (5,true),
.cycle 25 20 true (2),
.cycle 41 1 false (9),
.cycle 18 9 false (3),
.cycle 21 4 false (3),
.cycle 0 111 true (0),
.last 26 (5,true),
.last 25 (5,true),
.cycle 2 26 true (0),
.cycle 1 32 true (0),
.cycle 2 61 true (0),
.cycle 4 68 true (0),
.cycle 26 28 true (2),
.cycle 0 34 true (0)
]),
.cycle 39 1 false (9),
.split 26 (1,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 41 true (0),
.cycle 0 56 true (0),
.cycle 0 31 true (0),
.cycle 0 33 true (0),
.last 27 (5,true),
.cycle 6 48 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 4, 64],[4, 2, 15, 1, 32, 64, 64],64⟩,
.cycle 0 48 true (0),
.cycle 0 28 true (0),
.cycle 8 19 true (0),
.last 27 (5,true),
.cycle 0 35 true (0),
.cycle 0 47 true (0),
.cycle 21 6 true (1),
.cycle 33 1 false (7),
.last 28 (5,true),
.last 27 (5,true),
.cycle 2 26 true (0),
.cycle 1 27 true (0),
.cycle 2 44 true (0),
.cycle 0 28 true (0),
.cycle 0 53 true (0),
.last 27 (5,true)
]),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 20 3 false (3),
.split 24 (1,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 38 true (0),
.cycle 0 30 true (0),
.cycle 0 29 true (0),
.cycle 0 29 true (0),
.last 25 (5,true),
.cycle 6 44 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 1, 4, 64],[4, 2, 6, 1, 32, 64, 64],64⟩,
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 8 17 true (0),
.last 25 (5,true),
.cycle 0 31 true (0),
.cycle 18 10 true (1),
.cycle 0 37 true (0),
.cycle 5 20 true (0),
.last 26 (5,true),
.last 25 (5,true),
.cycle 2 24 true (0),
.cycle 1 25 true (0),
.cycle 2 40 true (0),
.cycle 0 26 true (0),
.cycle 0 42 true (0),
.last 25 (5,true)
]),
.cycle 1 28 true (0),
.cycle 0 91 true (0),
.cycle 43 1 false (9),
.split 25 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 0 59 true (0),
.cycle 26 1 true (4),
.cycle 37 1 true (5),
.cycle 0 26 true (0),
.last 53 (1,true),
.cycle 26 15 true (3),
.cycle 35 1 true (5),
.cycle 26 1 true (6),
.cycle 9 17 true (0),
.last 27 (1,true),
.cycle 28 15 true (3),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.cycle 26 15 true (4),
.cycle 28 1 true (4),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 7 44 true (0),
.cycle 0 83 true (0),
.cycle 26 1 true (6),
.cycle 37 1 true (7)
]),
.cycle 26 12 true (4)
])
theorem kid04_part357_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part357) = true := by rfl

def kid04_part358 : Audit := .cycle 29 1 false (7)
theorem kid04_part358_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part358) = true := by rfl

def kid04_part359 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 34 1 false (6),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 25 1 false (3),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 34 1 false (8),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 25 1 false (5),
.cycle 26 1 false (6),
.last 24 (1,true),
.cycle 29 1 false (5),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 25 1 false (3),
.cycle 28 1 false (6),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 33 1 false (7),
.cycle 36 1 false (8),
.cycle 27 1 false (3),
.cycle 35 1 false (7)
]),
.cycle 22 1 false (4),
.cycle 16 1 false (2),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 24 (5,true) (byMove [
.cycle 0 55 true (0),
.cycle 0 130 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 39 1 false (11),
.cycle 0 31 true (0),
.cycle 31 1 false (9),
.last 25 (1,true),
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 29 1 false (9),
.cycle 30 1 false (10),
.last 26 (1,true),
.cycle 37 1 false (9),
.cycle 33 1 false (9),
.cycle 25 1 false (3),
.cycle 41 1 false (11),
.cycle 36 1 false (10),
.cycle 2 42 true (0),
.last 25 (1,true),
.cycle 32 1 false (10),
.cycle 5 46 true (0),
.cycle 59 16 true (11),
.cycle 26 14 true (6)
]),
.split 22 (5,true) (byMove [
.cycle 0 40 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 24 1 false (4),
.cycle 0 26 true (0),
.cycle 33 1 false (9),
.last 23 (1,true),
.cycle 25 1 false (5),
.cycle 0 24 true (0),
.cycle 26 1 false (8),
.cycle 26 1 false (8),
.last 24 (1,true),
.cycle 30 1 false (8),
.cycle 35 1 false (9),
.cycle 23 1 false (3),
.cycle 35 1 false (9),
.cycle 30 1 false (8),
.cycle 2 22 true (0),
.last 23 (1,true),
.cycle 27 1 false (7),
.cycle 0 24 true (0),
.cycle 46 1 false (12),
.cycle 22 30 true (4)
]),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 20 4 false (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 14 true (2),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.cycle 8 10 true (2),
.cycle 24 4 false (6),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 9 4 true (3)
]),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 31 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 31 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 22 1 false (4),
.cycle 23 1 false (5),
.last 22 (1,true),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 25 1 false (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (6),
.cycle 33 1 false (7),
.cycle 33 1 false (7),
.cycle 30 1 false (6)
]),
.split 15 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 0 60 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 22 1 false (6),
.last 16 (1,true),
.cycle 17 1 false (1),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 20 1 false (6),
.last 17 (1,true),
.cycle 28 1 false (6),
.cycle 24 1 false (6),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 28 1 false (6),
.cycle 0 35 true (0),
.last 16 (1,true),
.cycle 29 1 false (7),
.cycle 5 11 true (0),
.cycle 25 3 true (5),
.cycle 17 6 true (3)
]),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid04_part359_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part359) = true := by rfl

def kid04_part360 : Audit := .cycle 9 1 true (3)
theorem kid04_part360_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part360) = true := by rfl

def kid04_part362 : Audit := .cycle 2 11 true (1)
theorem kid04_part362_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part362) = true := by rfl

def kid04_part363 : Audit := .cycle 1 12 true (1)
theorem kid04_part363_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part363) = true := by rfl

def kid04_part364 : Audit := .split 13 (4,false) (byMove [
.cycle 0 27 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 19 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 19 5 false (1),
.cycle 18 4 false (1),
.cycle 16 1 false (0),
.cycle 0 24 true (-2),
.cycle 28 1 false (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 1 true (1),
.cycle 21 9 false (1)
])
theorem kid04_part364_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part364) = true := by rfl

def kid04_part365 : Audit := .cycle 0 13 true (0)
theorem kid04_part365_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part365) = true := by rfl

def kid04_part366 : Audit := .cycle 8 4 true (2)
theorem kid04_part366_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part366) = true := by rfl

def kid04_part367 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.cycle 21 7 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 6 8 true (2)
])
theorem kid04_part367_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part367) = true := by rfl

def kid04_part368 : Audit := .cycle 0 12 true (0)
theorem kid04_part368_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part368) = true := by rfl

def kid04_part369 : Audit := .cycle 1 11 true (1)
theorem kid04_part369_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part369) = true := by rfl

def kid04_part370 : Audit := .split 24 (4,false) (byMove [
.cycle 2 24 true (1),
.cycle 43 1 false (3),
.cycle 53 1 false (1),
.cycle 0 26 true (0),
.cycle 8 17 true (2),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 12 13 true (2),
.cycle 3 22 true (1),
.cycle 24 1 true (4),
.cycle 9 16 true (2),
.cycle 6 19 true (2),
.cycle 7 22 true (2),
.cycle 10 19 true (1),
.cycle 2 25 true (1),
.last 26 (5,true),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 2 26 true (1),
.cycle 24 1 true (4),
.cycle 6 20 true (2)
])
theorem kid04_part370_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part370) = true := by rfl

def kid04_part371 : Audit := .cycle 3 9 true (1)
theorem kid04_part371_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part371) = true := by rfl

def kid04_part372 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 6 true (2),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (5,true),
.cycle 8 15 true (2),
.cycle 12 1 true (4),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.cycle 8 12 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 6 8 true (2)
])
theorem kid04_part372_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part372) = true := by rfl

def kid04_part373 : Audit := .cycle 9 3 true (2)
theorem kid04_part373_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part373) = true := by rfl

def kid04_part374 : Audit := .cycle 6 6 true (2)
theorem kid04_part374_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part374) = true := by rfl

def kid04_part375 : Audit := .cycle 19 7 false (1)
theorem kid04_part375_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part375) = true := by rfl

def kid04_part376 : Audit := .split 13 (4,false) (byMove [
.cycle 0 48 true (-1),
.cycle 24 13 false (2),
.cycle 17 1 false (-1),
.cycle 29 1 false (-1),
.cycle 19 1 false (-1),
.last 14 (5,true),
.cycle 10 4 true (1),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 8 7 true (1),
.cycle 19 5 false (1),
.cycle 18 4 false (1),
.cycle 0 20 true (-1),
.cycle 14 6 true (-2),
.cycle 0 18 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 19 9 false (2),
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 38 (5,true),
.cycle 21 9 false (1)
])
theorem kid04_part376_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part376) = true := by rfl

def kid04_part377 : Audit := .cycle 2 12 true (1)
theorem kid04_part377_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part377) = true := by rfl

def kid04_part378 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 30 (4,false),
.cycle 41 1 false (7),
.last 14 (4,false),
.cycle 9 5 true (2),
.cycle 10 4 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.cycle 6 9 true (2)
])
theorem kid04_part378_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part378) = true := by rfl

def kid04_part379 : Audit := .split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 17 4 false (1),
.cycle 2 12 true (1),
.cycle 23 5 false (1),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 9 5 true (2),
.cycle 20 3 false (1),
.cycle 21 7 false (-1),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 17 4 false (1),
.cycle 2 12 true (1),
.cycle 11 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 6 9 true (2)
])
theorem kid04_part379_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part379) = true := by rfl

def kid04_part380 : Audit := .cycle 0 12 true (0)
theorem kid04_part380_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part380) = true := by rfl

def kid04_part381 : Audit := .cycle 1 11 true (1)
theorem kid04_part381_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part381) = true := by rfl

def kid04_part382 : Audit := .cycle 2 10 true (1)
theorem kid04_part382_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part382) = true := by rfl

def kid04_part383 : Audit := .cycle 2 13 true (1)
theorem kid04_part383_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part383) = true := by rfl

def kid04_part384 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2),
.cycle 6 7 true (2),
.cycle 8 6 true (2),
.cycle 8 10 true (2),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 6 8 true (2)
])
theorem kid04_part384_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part384) = true := by rfl

def kid04_part385 : Audit := .cycle 6 7 true (2)
theorem kid04_part385_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part385) = true := by rfl

def kid04_part361 : Audit := .split 11 (1,true) (byMove [(kid04_part362),(kid04_part363),(kid04_part364),(kid04_part365),(kid04_part366),(kid04_part367),(kid04_part368),(kid04_part369),(kid04_part370),(kid04_part371),(kid04_part372),(kid04_part373),(kid04_part374),(kid04_part375),(kid04_part376),(kid04_part377),(kid04_part378),(kid04_part379),(kid04_part380),(kid04_part381),(kid04_part382),(kid04_part383),(kid04_part384),(kid04_part385)])

theorem kid04_part361_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part361) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part362),(kid04_part363),(kid04_part364),(kid04_part365),(kid04_part366),(kid04_part367),(kid04_part368),(kid04_part369),(kid04_part370),(kid04_part371),(kid04_part372),(kid04_part373),(kid04_part374),(kid04_part375),(kid04_part376),(kid04_part377),(kid04_part378),(kid04_part379),(kid04_part380),(kid04_part381),(kid04_part382),(kid04_part383),(kid04_part384),(kid04_part385)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part362_checked

  · exact kid04_part368_checked

  · exact kid04_part374_checked

  · exact kid04_part380_checked

  · exact kid04_part363_checked

  · exact kid04_part369_checked

  · exact kid04_part375_checked

  · exact kid04_part381_checked

  · exact kid04_part364_checked

  · exact kid04_part370_checked

  · exact kid04_part376_checked

  · exact kid04_part382_checked

  · exact kid04_part365_checked

  · exact kid04_part371_checked

  · exact kid04_part377_checked

  · exact kid04_part383_checked

  · exact kid04_part366_checked

  · exact kid04_part372_checked

  · exact kid04_part378_checked

  · exact kid04_part384_checked

  · exact kid04_part367_checked

  · exact kid04_part373_checked

  · exact kid04_part379_checked

  · exact kid04_part385_checked

def kid04_part386 : Audit := .cycle 7 4 true (2)
theorem kid04_part386_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part386) = true := by rfl

def kid04_part387 : Audit := .cycle 0 12 true (0)
theorem kid04_part387_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part387) = true := by rfl

def kid04_part388 : Audit := .cycle 17 1 false (1)
theorem kid04_part388_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part388) = true := by rfl

def kid04_part390 : Audit := .cycle 0 20 true (0)
theorem kid04_part390_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part390) = true := by rfl

def kid04_part391 : Audit := .cycle 0 14 true (0)
theorem kid04_part391_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part391) = true := by rfl

def kid04_part392 : Audit := .cycle 21 1 false (1)
theorem kid04_part392_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part392) = true := by rfl

def kid04_part393 : Audit := .cycle 0 16 true (0)
theorem kid04_part393_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part393) = true := by rfl

def kid04_part394 : Audit := .cycle 14 1 false (0)
theorem kid04_part394_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part394) = true := by rfl

def kid04_part395 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 22 2 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.last 15 (1,true),
.cycle 17 2 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 2 false (2),
.cycle 14 2 false (2),
.last 15 (1,true),
.cycle 17 2 false (1),
.last 17 (1,true),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.last 15 (1,true),
.cycle 13 6 true (1),
.cycle 0 16 true (0),
.cycle 19 2 false (3),
.cycle 13 2 true (1),
.cycle 17 3 true (3)
])
theorem kid04_part395_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part395) = true := by rfl

def kid04_part396 : Audit := .cycle 2 10 true (1)
theorem kid04_part396_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part396) = true := by rfl

def kid04_part397 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 17 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 47 1 false (9),
.cycle 35 1 false (7),
.cycle 1 12 true (1),
.cycle 9 3 true (2),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 17 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 14 (5,true)
])
theorem kid04_part397_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part397) = true := by rfl

def kid04_part398 : Audit := .cycle 41 1 false (7)
theorem kid04_part398_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part398) = true := by rfl

def kid04_part399 : Audit := .cycle 0 12 true (0)
theorem kid04_part399_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part399) = true := by rfl

def kid04_part400 : Audit := .cycle 8 3 true (2)
theorem kid04_part400_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part400) = true := by rfl

def kid04_part401 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 4 true (2),
.cycle 17 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 35 1 false (7),
.cycle 9 4 true (2),
.cycle 9 3 true (2),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.cycle 17 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 4 true (2),
.cycle 11 3 true (3)
])
theorem kid04_part401_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part401) = true := by rfl

def kid04_part402 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.cycle 16 4 false (0),
.cycle 0 17 true (0),
.cycle 18 5 false (1),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 13 (5,true),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 16 4 false (0),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.last 34 (5,true),
.last 13 (5,true)
])
theorem kid04_part402_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part402) = true := by rfl

def kid04_part403 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 18 5 false (2),
.cycle 26 5 false (6),
.cycle 18 5 false (0),
.cycle 19 5 false (3),
.last 18 (5,true),
.last 17 (5,true),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 12 6 true (0),
.cycle 1 19 true (0),
.cycle 17 5 false (1),
.cycle 5 12 true (0),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid04_part403_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part403) = true := by rfl

def kid04_part404 : Audit := .cycle 2 12 true (1)
theorem kid04_part404_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part404) = true := by rfl

def kid04_part405 : Audit := .cycle 18 1 false (0)
theorem kid04_part405_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part405) = true := by rfl

def kid04_part406 : Audit := .split 13 (5,true) (byMove [
.cycle 11 8 true (0),
.cycle 27 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (2),
.last 14 (1,true),
.cycle 15 1 false (1),
.cycle 24 1 false (4),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.last 15 (1,true),
.cycle 18 1 false (0),
.cycle 20 1 false (2),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 2 20 true (0),
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 5 24 true (0),
.cycle 14 3 true (2),
.cycle 15 3 true (3)
])
theorem kid04_part406_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part406) = true := by rfl

def kid04_part407 : Audit := .split 13 (5,true) (byMove [
.cycle 13 7 false (2),
.cycle 31 11 false (4),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 17 2 false (3),
.last 14 (1,true),
.cycle 15 2 false (1),
.cycle 23 2 false (5),
.cycle 16 2 false (4),
.cycle 16 2 false (4),
.last 15 (1,true),
.cycle 17 2 false (1),
.cycle 19 2 false (3),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 13 6 true (1),
.last 14 (1,true),
.cycle 16 2 false (2),
.cycle 5 32 true (0),
.cycle 13 8 true (1),
.cycle 15 3 true (3)
])
theorem kid04_part407_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part407) = true := by rfl

def kid04_part408 : Audit := .cycle 2 10 true (1)
theorem kid04_part408_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part408) = true := by rfl

def kid04_part409 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 24 true (1),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.cycle 20 13 false (2),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 14 (5,true)
])
theorem kid04_part409_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part409) = true := by rfl

def kid04_part410 : Audit := .cycle 7 4 true (2)
theorem kid04_part410_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part410) = true := by rfl

def kid04_part411 : Audit := .cycle 0 12 true (0)
theorem kid04_part411_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part411) = true := by rfl

def kid04_part412 : Audit := .cycle 8 3 true (2)
theorem kid04_part412_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part412) = true := by rfl

def kid04_part413 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 4, 64],[4, 64, 4, 1, 32, 4, 64],64⟩,
.cycle 3 9 true (1),
.cycle 11 4 true (3),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 2 18 true (1),
.cycle 2 12 true (1),
.cycle 10 4 true (2),
.cycle 15 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 4 true (3),
.cycle 11 3 true (3)
])
theorem kid04_part413_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part413) = true := by rfl

def kid04_part389 : Audit := .split 10 (4,false) (byMove [(kid04_part390),(kid04_part391),(kid04_part392),(kid04_part393),(kid04_part394),(kid04_part395),(kid04_part396),(kid04_part397),(kid04_part398),(kid04_part399),(kid04_part400),(kid04_part401),(kid04_part402),(kid04_part403),(kid04_part404),(kid04_part405),(kid04_part406),(kid04_part407),(kid04_part408),(kid04_part409),(kid04_part410),(kid04_part411),(kid04_part412),(kid04_part413)])

theorem kid04_part389_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part389) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid04_part390),(kid04_part391),(kid04_part392),(kid04_part393),(kid04_part394),(kid04_part395),(kid04_part396),(kid04_part397),(kid04_part398),(kid04_part399),(kid04_part400),(kid04_part401),(kid04_part402),(kid04_part403),(kid04_part404),(kid04_part405),(kid04_part406),(kid04_part407),(kid04_part408),(kid04_part409),(kid04_part410),(kid04_part411),(kid04_part412),(kid04_part413)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part390_checked

  · exact kid04_part396_checked

  · exact kid04_part402_checked

  · exact kid04_part408_checked

  · exact kid04_part391_checked

  · exact kid04_part397_checked

  · exact kid04_part403_checked

  · exact kid04_part409_checked

  · exact kid04_part392_checked

  · exact kid04_part398_checked

  · exact kid04_part404_checked

  · exact kid04_part410_checked

  · exact kid04_part393_checked

  · exact kid04_part399_checked

  · exact kid04_part405_checked

  · exact kid04_part411_checked

  · exact kid04_part394_checked

  · exact kid04_part400_checked

  · exact kid04_part406_checked

  · exact kid04_part412_checked

  · exact kid04_part395_checked

  · exact kid04_part401_checked

  · exact kid04_part407_checked

  · exact kid04_part413_checked

def kid04_part415 : Audit := .cycle 10 7 false (2)
theorem kid04_part415_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part415) = true := by rfl

def kid04_part416 : Audit := .cycle 9 11 false (3)
theorem kid04_part416_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part416) = true := by rfl

def kid04_part417 : Audit := .cycle 14 1 false (0)
theorem kid04_part417_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part417) = true := by rfl

def kid04_part418 : Audit := .cycle 13 1 false (-1)
theorem kid04_part418_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part418) = true := by rfl

def kid04_part419 : Audit := .split 13 (4,false) (byMove [
.cycle 27 1 false (-1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 20 1 false (4),
.cycle 14 1 false (0),
.last 15 (1,true),
.cycle 17 1 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (1,true),
.cycle 10 7 false (2),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.cycle 28 1 false (0),
.cycle 11 3 false (1)
])
theorem kid04_part419_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part419) = true := by rfl

def kid04_part420 : Audit := .cycle 13 1 false (-1)
theorem kid04_part420_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part420) = true := by rfl

def kid04_part421 : Audit := .cycle 16 1 false (2)
theorem kid04_part421_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part421) = true := by rfl

def kid04_part422 : Audit := .split 13 (1,true) (byMove [
.cycle 10 8 true (0),
.cycle 26 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.cycle 24 1 false (6),
.last 15 (4,false),
.cycle 23 1 false (5),
.cycle 24 1 false (6),
.cycle 16 1 false (4),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 2 20 true (0),
.cycle 1 15 true (0),
.cycle 16 1 false (2),
.cycle 5 24 true (0),
.cycle 32 5 true (4),
.cycle 14 3 true (2)
])
theorem kid04_part422_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part422) = true := by rfl

def kid04_part423 : Audit := .split 14 (4,false) (byMove [
.cycle 43 1 false (1),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 18 1 false (2),
.cycle 25 1 false (5),
.cycle 15 1 false (1),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 18 1 false (0),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 10 8 true (0),
.cycle 26 12 true (0),
.cycle 20 1 false (2),
.cycle 35 7 true (3),
.cycle 11 4 true (0)
])
theorem kid04_part423_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part423) = true := by rfl

def kid04_part424 : Audit := .cycle 17 1 false (3)
theorem kid04_part424_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part424) = true := by rfl

def kid04_part425 : Audit := .cycle 16 1 false (4)
theorem kid04_part425_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part425) = true := by rfl

def kid04_part426 : Audit := .cycle 16 1 false (4)
theorem kid04_part426_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part426) = true := by rfl

def kid04_part427 : Audit := .split 14 (1,true) (byMove [
.cycle 9 13 false (3),
.cycle 24 1 false (0),
.last 16 (4,false),
.cycle 0 25 true (-1),
.cycle 16 1 false (0),
.cycle 12 3 false (0),
.cycle 6 9 false (3),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 32, 64],[33, 33, 16, 33, 33, 1, 64],80⟩,
.last 16 (4,false),
.cycle 9 11 false (3),
.cycle 8 11 true (-1),
.cycle 36 1 false (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 19 1 false (1),
.cycle 12 4 true (-1),
.cycle 12 3 false (0),
.cycle 24 1 false (0),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 32, 64],[33, 33, 16, 33, 33, 1, 64],80⟩,
.cycle 10 7 false (2),
.cycle 26 1 false (0),
.cycle 32 1 false (0),
.cycle 10 9 false (2)
])
theorem kid04_part427_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part427) = true := by rfl

def kid04_part428 : Audit := .cycle 16 1 false (0)
theorem kid04_part428_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part428) = true := by rfl

def kid04_part429 : Audit := .cycle 18 1 false (2)
theorem kid04_part429_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part429) = true := by rfl

def kid04_part430 : Audit := .cycle 13 1 false (-1)
theorem kid04_part430_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part430) = true := by rfl

def kid04_part431 : Audit := .split 13 (4,false) (byMove [
.cycle 10 8 false (2),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.last 14 (1,true),
.cycle 21 1 false (3),
.cycle 18 1 false (2),
.cycle 24 1 false (4),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 7 false (2),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 5 9 false (3),
.cycle 14 13 true (0),
.cycle 12 4 true (-1)
])
theorem kid04_part431_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part431) = true := by rfl

def kid04_part432 : Audit := .cycle 13 1 false (-1)
theorem kid04_part432_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part432) = true := by rfl

def kid04_part433 : Audit := .cycle 10 6 true (0)
theorem kid04_part433_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part433) = true := by rfl

def kid04_part434 : Audit := .split 13 (1,true) (byMove [
.cycle 26 12 true (0),
.cycle 23 1 false (1),
.last 15 (4,false),
.cycle 0 21 true (0),
.cycle 15 1 false (1),
.cycle 10 8 true (0),
.cycle 6 8 true (0),
.far true 1 ⟨0,[0, 0],[0, 32, 40, 8, 64, 32, 64],[32, 32, 16, 32, 32, 0, 64],80⟩,
.last 15 (4,false),
.cycle 24 10 true (0),
.cycle 1 15 true (0),
.cycle 1 20 true (0),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.last 15 (4,false),
.cycle 18 1 false (2),
.cycle 1 21 true (0),
.cycle 12 2 true (0),
.cycle 2 20 true (0),
.cycle 1 15 true (0),
.cycle 10 6 true (0),
.cycle 5 24 true (0),
.cycle 1 15 true (0),
.cycle 14 3 true (2)
])
theorem kid04_part434_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part434) = true := by rfl

def kid04_part435 : Audit := .cycle 15 1 false (1)
theorem kid04_part435_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part435) = true := by rfl

def kid04_part436 : Audit := .cycle 5 8 true (0)
theorem kid04_part436_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part436) = true := by rfl

def kid04_part437 : Audit := .split 21 (4,false) (byMove [
.cycle 18 18 true (2),
.last 22 (1,true),
.cycle 29 1 false (-1),
.cycle 0 23 true (0),
.cycle 8 14 true (0),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 18 18 true (2),
.cycle 12 24 true (0),
.cycle 18 16 true (2),
.cycle 21 1 true (5),
.cycle 16 6 true (2),
.cycle 6 16 true (0),
.last 22 (1,true),
.last 31 (1,true),
.cycle 12 26 true (0),
.cycle 19 3 true (3),
.cycle 14 8 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 20 true (2),
.cycle 21 1 true (5),
.cycle 14 9 true (2)
])
theorem kid04_part437_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part437) = true := by rfl

def kid04_part438 : Audit := .cycle 14 3 true (2)
theorem kid04_part438_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part438) = true := by rfl

def kid04_part414 : Audit := .split 12 (5,true) (byMove [(kid04_part415),(kid04_part416),(kid04_part417),(kid04_part418),(kid04_part419),(kid04_part420),(kid04_part421),(kid04_part422),(kid04_part423),(kid04_part424),(kid04_part425),(kid04_part426),(kid04_part427),(kid04_part428),(kid04_part429),(kid04_part430),(kid04_part431),(kid04_part432),(kid04_part433),(kid04_part434),(kid04_part435),(kid04_part436),(kid04_part437),(kid04_part438)])

theorem kid04_part414_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part414) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part415),(kid04_part416),(kid04_part417),(kid04_part418),(kid04_part419),(kid04_part420),(kid04_part421),(kid04_part422),(kid04_part423),(kid04_part424),(kid04_part425),(kid04_part426),(kid04_part427),(kid04_part428),(kid04_part429),(kid04_part430),(kid04_part431),(kid04_part432),(kid04_part433),(kid04_part434),(kid04_part435),(kid04_part436),(kid04_part437),(kid04_part438)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part415_checked

  · exact kid04_part421_checked

  · exact kid04_part427_checked

  · exact kid04_part433_checked

  · exact kid04_part416_checked

  · exact kid04_part422_checked

  · exact kid04_part428_checked

  · exact kid04_part434_checked

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

def kid04_part439 : Audit := .cycle 0 10 true (0)
theorem kid04_part439_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part439) = true := by rfl

def kid04_part440 : Audit := .cycle 1 9 true (1)
theorem kid04_part440_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part440) = true := by rfl

def kid04_part441 : Audit := .cycle 2 8 true (1)
theorem kid04_part441_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part441) = true := by rfl

def kid04_part442 : Audit := .cycle 2 11 true (1)
theorem kid04_part442_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part442) = true := by rfl

def kid04_part443 : Audit := .split 10 (4,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 36 1 false (4),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 18 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (5,true),
.last 22 (5,true),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 31 1 false (3),
.cycle 0 16 true (0),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 36 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (2),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 42 12 true (4),
.cycle 22 12 true (2),
.cycle 9 4 true (3),
.cycle 9 3 true (3),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 31 1 false (3),
.cycle 17 4 false (1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 8 12 true (2),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 22 (5,true),
.cycle 21 1 false (1),
.cycle 19 7 false (1),
.last 18 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 8 10 true (2),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.last 20 (5,true),
.last 18 (5,true),
.last 14 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true)
]),
.split 16 (1,true) (byMove [
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.cycle 0 21 true (0),
.cycle 0 18 true (0),
.cycle 8 9 true (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 39 true (0),
.cycle 3 14 true (1),
.cycle 0 20 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 394544, 131105, 1024, 128, 256, 32768, 260, 131104, 1024, 2, 4, 8, 1168, 1, 16, 262144],[256, 32, 1168, 1, 32, 262144, 256, 131072, 1040, 4096, 131072, 262144, 4, 32, 1040, 1, 32, 262144, 262144],287244⟩,
.cycle 6 11 true (1),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[128, 256, 8, 16778272, 1, 1024, 8192, 16384, 8, 256, 32, 65536, 8192, 16384, 2097152, 256, 32, 65536, 128, 256, 8, 1024, 1, 1024, 16777216],[256, 1024, 1152, 1, 32, 16777216, 16384, 32, 1024, 1, 32, 16777216, 16384, 16777216, 1024, 262144, 8388608, 16777216, 256, 1024, 1024, 1, 32, 16777216, 16777216],18383630⟩,
.cycle 11 6 true (1),
.cycle 2 17 true (1),
.last 18 (5,true),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.last 37 (5,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 396592, 131105, 1024, 128, 256, 32768, 260, 133152, 1024, 2, 4, 8, 1168, 1, 16, 262144],[256, 2048, 1168, 1, 32, 262144, 256, 2048, 1040, 4096, 131072, 262144, 4, 32, 1040, 1, 32, 262144, 262144],287244⟩
]),
.cycle 2 11 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 37 1 false (5),
.cycle 36 1 false (4),
.cycle 18 1 false (0),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (3),
.cycle 0 26 true (0),
.cycle 24 1 false (6),
.cycle 9 4 true (3),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 32 1 false (4),
.cycle 18 1 false (0),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3)
]),
.split 11 (5,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 18 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 8 7 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 9 4 true (3),
.last 13 (1,true),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.cycle 29 1 false (3),
.cycle 19 6 false (1),
.cycle 8 8 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid04_part443_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part443) = true := by rfl

def kid04_part444 : Audit := .cycle 9 1 true (3)
theorem kid04_part444_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part444) = true := by rfl

def kid04_part348 : Audit := .split 9 (5,false) (byMove [(kid04_part349),(kid04_part350),(kid04_part351),(kid04_part352),(kid04_part353),(kid04_part354),(kid04_part355),(kid04_part356),(kid04_part357),(kid04_part358),(kid04_part359),(kid04_part360),(kid04_part361),(kid04_part386),(kid04_part387),(kid04_part388),(kid04_part389),(kid04_part414),(kid04_part439),(kid04_part440),(kid04_part441),(kid04_part442),(kid04_part443),(kid04_part444)])

theorem kid04_part348_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (kid04_part348) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part349),(kid04_part350),(kid04_part351),(kid04_part352),(kid04_part353),(kid04_part354),(kid04_part355),(kid04_part356),(kid04_part357),(kid04_part358),(kid04_part359),(kid04_part360),(kid04_part361),(kid04_part386),(kid04_part387),(kid04_part388),(kid04_part389),(kid04_part414),(kid04_part439),(kid04_part440),(kid04_part441),(kid04_part442),(kid04_part443),(kid04_part444)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part349_checked

  · exact kid04_part355_checked

  · exact kid04_part361_checked

  · exact kid04_part439_checked

  · exact kid04_part350_checked

  · exact kid04_part356_checked

  · exact kid04_part386_checked

  · exact kid04_part440_checked

  · exact kid04_part351_checked

  · exact kid04_part357_checked

  · exact kid04_part387_checked

  · exact kid04_part441_checked

  · exact kid04_part352_checked

  · exact kid04_part358_checked

  · exact kid04_part388_checked

  · exact kid04_part442_checked

  · exact kid04_part353_checked

  · exact kid04_part359_checked

  · exact kid04_part389_checked

  · exact kid04_part443_checked

  · exact kid04_part354_checked

  · exact kid04_part360_checked

  · exact kid04_part414_checked

  · exact kid04_part444_checked

def kid04_part446 : Audit := .cycle 2 10 true (1)
theorem kid04_part446_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part446) = true := by rfl

def kid04_part447 : Audit := .cycle 11 11 false (1)
theorem kid04_part447_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part447) = true := by rfl

def kid04_part448 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 true (-3),
.cycle 17 1 true (-3),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 11 21 false (1),
.cycle 1 17 false (3),
.cycle 11 12 false (1),
.cycle 11 15 false (1),
.last 19 (5,true),
.cycle 17 1 true (-3)
]),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 true (-2),
.split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 true (-2),
.cycle 17 1 false (-1),
.cycle 0 18 true (-2),
.cycle 11 13 true (-2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 16 2 true (-2),
.cycle 17 1 true (-1),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.last 19 (5,true),
.cycle 17 1 false (-1),
.cycle 11 21 false (3),
.cycle 1 17 false (3),
.cycle 11 12 true (-2),
.cycle 11 15 true (-2),
.cycle 16 2 true (-2),
.cycle 17 1 true (-1)
]),
.cycle 13 4 false (0),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.split 17 (5,false) (byMove [
.cycle 11 12 false (1),
.last 38 (5,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 11 13 false (1),
.cycle 20 1 false (-2),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 11 15 false (1),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 2 17 false (3),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.cycle 7 23 false (3),
.cycle 11 9 false (1),
.last 18 (5,true)
]),
.cycle 11 20 false (2),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 16 1 true (-2),
.split 17 (5,false) (byMove [
.cycle 11 13 false (1),
.cycle 20 1 false (-2),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 7 22 false (3),
.cycle 11 13 true (-2),
.cycle 11 13 false (1),
.cycle 11 11 false (1),
.cycle 16 2 true (-2),
.cycle 17 1 true (-1),
.cycle 11 8 false (1),
.cycle 20 1 false (-2),
.cycle 15 3 false (-1),
.cycle 11 14 true (-2),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 11 24 false (3),
.cycle 11 20 false (2),
.cycle 2 16 false (3),
.cycle 11 15 true (-2),
.cycle 16 2 true (-2),
.cycle 17 1 true (-1)
])
])
theorem kid04_part448_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part448) = true := by rfl

def kid04_part449 : Audit := .cycle 0 12 true (0)
theorem kid04_part449_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part449) = true := by rfl

def kid04_part450 : Audit := .cycle 14 3 false (0)
theorem kid04_part450_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part450) = true := by rfl

def kid04_part452 : Audit := .cycle 0 23 false (3)
theorem kid04_part452_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part452) = true := by rfl

def kid04_part453 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 14 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 13 1 true (-1),
.cycle 14 11 false (-1),
.cycle 15 11 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 26 11 false (0),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 17 11 false (2),
.last 14 (4,false),
.cycle 13 1 true (-1)
])
theorem kid04_part453_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part453) = true := by rfl

def kid04_part454 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 14 true (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.last 14 (5,false),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 32 1 false (-2),
.cycle 1 13 false (3),
.cycle 25 1 false (-1),
.cycle 28 1 false (0),
.cycle 13 1 true (-1),
.last 14 (5,false)
])
theorem kid04_part454_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part454) = true := by rfl

def kid04_part455 : Audit := .cycle 0 13 true (0)
theorem kid04_part455_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part455) = true := by rfl

def kid04_part456 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 false (3),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 0 17 false (3),
.cycle 12 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 true (-2),
.last 17 (5,false),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 12 20 false (2),
.cycle 1 16 false (3),
.cycle 12 11 false (0),
.cycle 12 14 true (-2),
.cycle 16 1 true (-2),
.last 17 (5,false)
])
theorem kid04_part456_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part456) = true := by rfl

def kid04_part457 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 13 1 true (-1),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 11 15 false (3),
.cycle 1 13 false (3),
.cycle 12 11 false (1),
.cycle 12 14 true (-1),
.last 14 (4,false),
.cycle 13 1 true (-1)
])
theorem kid04_part457_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part457) = true := by rfl

def kid04_part458 : Audit := .cycle 0 12 true (0)
theorem kid04_part458_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part458) = true := by rfl

def kid04_part459 : Audit := .cycle 1 11 true (1)
theorem kid04_part459_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part459) = true := by rfl

def kid04_part460 : Audit := .cycle 24 1 false (2)
theorem kid04_part460_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part460) = true := by rfl

def kid04_part461 : Audit := .cycle 21 1 false (1)
theorem kid04_part461_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part461) = true := by rfl

def kid04_part462 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 18 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.last 13 (5,false),
.cycle 9 4 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid04_part462_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part462) = true := by rfl

def kid04_part463 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 9 4 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 17 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid04_part463_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part463) = true := by rfl

def kid04_part464 : Audit := .cycle 15 3 false (0)
theorem kid04_part464_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part464) = true := by rfl

def kid04_part465 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 6 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 14 6 false (1),
.cycle 14 6 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 15 6 false (1),
.cycle 14 6 false (-1),
.cycle 14 6 false (-1),
.cycle 16 6 false (1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.cycle 18 6 false (0),
.cycle 0 16 true (-1),
.cycle 17 6 false (1),
.last 14 (4,false),
.cycle 16 6 false (0)
])
theorem kid04_part465_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part465) = true := by rfl

def kid04_part466 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 0 39 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 19 true (-1),
.cycle 0 22 true (-2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 0 21 true (-1),
.last 14 (5,false),
.cycle 0 31 false (3),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[80, 336, 32768, 512, 128, 16777216, 256, 64, 320, 32768, 8192, 16777216, 256, 64, 320, 32768, 8192, 16777216, 64, 80, 32768, 512, 128, 16777216, 16777216],[336, 32, 16, 448, 64, 256, 64, 32, 16, 448, 4096, 16384, 64, 8388608, 4194304, 256, 4096, 16384, 80, 32, 16, 320, 64, 256, 16777216],25298976⟩,
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 5 false (2),
.cycle 0 25 false (3),
.cycle 0 16 true (-1),
.cycle 0 24 true (-2),
.cycle 0 27 false (3),
.last 14 (5,false)
])
theorem kid04_part466_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part466) = true := by rfl

def kid04_part467 : Audit := .cycle 24 1 false (0)
theorem kid04_part467_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part467) = true := by rfl

def kid04_part468 : Audit := .split 16 (4,false) (byMove [
.cycle 12 11 false (0),
.last 62 (5,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 0 20 true (-2),
.last 18 (5,false),
.cycle 20 1 false (0),
.cycle 0 23 true (-2),
.cycle 12 5 false (0),
.cycle 15 2 true (-2),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 52 14 true (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 0 20 true (-2),
.cycle 14 3 false (0),
.cycle 12 6 false (0),
.cycle 6 46 false (4),
.cycle 12 8 false (0),
.cycle 11 6 false (1)
])
theorem kid04_part468_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part468) = true := by rfl

def kid04_part469 : Audit := .split 13 (5,false) (byMove [
.cycle 12 11 false (0),
.cycle 0 32 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 14 12 true (-2),
.cycle 17 14 true (-2),
.last 15 (4,false),
.cycle 0 28 true (-1),
.cycle 12 5 false (0),
.cycle 12 2 true (-1),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 15 14 true (-3),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 2 23 false (3),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.cycle 0 28 true (-1),
.cycle 12 8 false (0),
.cycle 11 3 false (1)
])
theorem kid04_part469_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part469) = true := by rfl

def kid04_part470 : Audit := .cycle 0 12 true (0)
theorem kid04_part470_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part470) = true := by rfl

def kid04_part471 : Audit := .cycle 1 11 true (1)
theorem kid04_part471_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part471) = true := by rfl

def kid04_part472 : Audit := .cycle 2 10 true (1)
theorem kid04_part472_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part472) = true := by rfl

def kid04_part473 : Audit := .cycle 2 13 true (1)
theorem kid04_part473_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part473) = true := by rfl

def kid04_part474 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.last 17 (5,false),
.cycle 22 1 false (-2),
.cycle 0 14 true (0),
.cycle 16 5 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.last 13 (5,false),
.cycle 16 7 false (1),
.last 17 (5,false),
.cycle 15 8 true (-3),
.cycle 2 13 true (1),
.cycle 16 5 false (0),
.cycle 17 9 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid04_part474_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part474) = true := by rfl

def kid04_part475 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 13 14 false (1),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 16 5 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.cycle 13 9 false (1),
.last 20 (4,false),
.cycle 2 13 true (1),
.cycle 16 5 false (0),
.cycle 11 3 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid04_part475_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part475) = true := by rfl

def kid04_part451 : Audit := .split 11 (5,true) (byMove [(kid04_part452),(kid04_part453),(kid04_part454),(kid04_part455),(kid04_part456),(kid04_part457),(kid04_part458),(kid04_part459),(kid04_part460),(kid04_part461),(kid04_part462),(kid04_part463),(kid04_part464),(kid04_part465),(kid04_part466),(kid04_part467),(kid04_part468),(kid04_part469),(kid04_part470),(kid04_part471),(kid04_part472),(kid04_part473),(kid04_part474),(kid04_part475)])

theorem kid04_part451_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part451) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part452),(kid04_part453),(kid04_part454),(kid04_part455),(kid04_part456),(kid04_part457),(kid04_part458),(kid04_part459),(kid04_part460),(kid04_part461),(kid04_part462),(kid04_part463),(kid04_part464),(kid04_part465),(kid04_part466),(kid04_part467),(kid04_part468),(kid04_part469),(kid04_part470),(kid04_part471),(kid04_part472),(kid04_part473),(kid04_part474),(kid04_part475)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part452_checked

  · exact kid04_part458_checked

  · exact kid04_part464_checked

  · exact kid04_part470_checked

  · exact kid04_part453_checked

  · exact kid04_part459_checked

  · exact kid04_part465_checked

  · exact kid04_part471_checked

  · exact kid04_part454_checked

  · exact kid04_part460_checked

  · exact kid04_part466_checked

  · exact kid04_part472_checked

  · exact kid04_part455_checked

  · exact kid04_part461_checked

  · exact kid04_part467_checked

  · exact kid04_part473_checked

  · exact kid04_part456_checked

  · exact kid04_part462_checked

  · exact kid04_part468_checked

  · exact kid04_part474_checked

  · exact kid04_part457_checked

  · exact kid04_part463_checked

  · exact kid04_part469_checked

  · exact kid04_part475_checked

def kid04_part476 : Audit := .cycle 0 11 true (0)
theorem kid04_part476_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part476) = true := by rfl

def kid04_part477 : Audit := .cycle 1 10 true (1)
theorem kid04_part477_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part477) = true := by rfl

def kid04_part478 : Audit := .cycle 0 23 true (0)
theorem kid04_part478_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part478) = true := by rfl

def kid04_part479 : Audit := .cycle 3 8 true (1)
theorem kid04_part479_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part479) = true := by rfl

def kid04_part480 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 16 5 false (1),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.cycle 23 1 false (-3),
.cycle 0 14 true (0),
.cycle 16 5 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.cycle 8 6 true (1),
.cycle 13 16 false (1),
.cycle 2 13 true (1),
.cycle 8 16 false (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (5,true),
.last 24 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (1),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 22 (5,true),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 9 3 true (1),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 44 22 false (0),
.split 12 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.cycle 23 1 false (-3),
.cycle 9 5 true (1),
.cycle 16 5 false (1),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 13 (5,true),
.cycle 16 7 false (1),
.cycle 8 9 true (1),
.last 36 (5,true),
.cycle 5 8 true (1),
.cycle 44 22 false (0),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 16 11 false (2),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 19 9 false (2),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (1),
.cycle 8 6 true (1),
.last 33 (5,true),
.cycle 2 13 true (1),
.cycle 8 8 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid04_part480_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part480) = true := by rfl

def kid04_part482 : Audit := .cycle 0 12 true (0)
theorem kid04_part482_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part482) = true := by rfl

def kid04_part483 : Audit := .cycle 1 11 true (1)
theorem kid04_part483_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part483) = true := by rfl

def kid04_part484 : Audit := .cycle 2 10 true (1)
theorem kid04_part484_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part484) = true := by rfl

def kid04_part485 : Audit := .cycle 2 13 true (1)
theorem kid04_part485_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part485) = true := by rfl

def kid04_part486 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.cycle 22 1 false (-2),
.cycle 0 14 true (0),
.cycle 16 5 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 16 7 false (1),
.last 14 (5,true),
.cycle 15 8 true (-3),
.cycle 2 13 true (1),
.last 24 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.cycle 17 9 false (1)
])
theorem kid04_part486_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part486) = true := by rfl

def kid04_part487 : Audit := .split 13 (5,true) (byMove [
.cycle 0 27 false (3),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 20 (4,false),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 17 1 false (1),
.cycle 17 5 false (1),
.cycle 15 8 false (1),
.last 15 (4,false),
.cycle 28 1 false (0),
.last 18 (4,false),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.cycle 12 2 true (1)
])
theorem kid04_part487_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part487) = true := by rfl

def kid04_part488 : Audit := .cycle 0 12 true (0)
theorem kid04_part488_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part488) = true := by rfl

def kid04_part489 : Audit := .cycle 1 11 true (1)
theorem kid04_part489_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part489) = true := by rfl

def kid04_part490 : Audit := .split 25 (4,false) (byMove [
.cycle 0 30 true (0),
.cycle 1 38 true (1),
.cycle 0 38 true (0),
.cycle 2 42 true (1),
.cycle 30 19 false (3),
.cycle 14 14 true (1),
.cycle 9 17 true (1),
.cycle 7 20 true (1),
.cycle 0 28 true (0),
.cycle 14 12 true (1),
.cycle 8 19 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 4, 32, 4, 8192, 16384, 8, 256, 32, 4, 128, 256, 8, 256, 32, 4, 262144],[256, 32, 4, 1, 32, 262144, 16384, 32, 4, 1, 4, 262144, 256, 32, 8, 1, 8, 262144, 262144],262144⟩,
.cycle 9 22 true (1),
.cycle 30 23 false (3),
.cycle 9 19 true (1),
.cycle 0 36 true (0),
.last 40 (5,true),
.last 29 (5,true),
.cycle 9 17 true (1),
.cycle 6 23 true (1),
.cycle 0 28 true (0),
.cycle 4 22 true (1),
.cycle 6 25 true (1),
.cycle 26 14 true (4)
])
theorem kid04_part490_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part490) = true := by rfl

def kid04_part491 : Audit := .cycle 0 23 true (0)
theorem kid04_part491_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part491) = true := by rfl

def kid04_part492 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (1),
.cycle 3 10 true (1),
.cycle 18 7 false (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (5,true),
.last 27 (5,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 9 4 true (1),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 8 14 true (1),
.last 25 (5,true),
.cycle 8 6 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid04_part492_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part492) = true := by rfl

def kid04_part493 : Audit := .cycle 11 1 true (3)
theorem kid04_part493_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part493) = true := by rfl

def kid04_part494 : Audit := .cycle 9 3 true (1)
theorem kid04_part494_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part494) = true := by rfl

def kid04_part495 : Audit := .cycle 16 9 false (2)
theorem kid04_part495_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part495) = true := by rfl

def kid04_part496 : Audit := .cycle 0 14 true (0)
theorem kid04_part496_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part496) = true := by rfl

def kid04_part497 : Audit := .cycle 4 8 true (1)
theorem kid04_part497_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part497) = true := by rfl

def kid04_part498 : Audit := .split 12 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.cycle 22 1 false (-2),
.cycle 9 5 true (1),
.cycle 16 5 false (1),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 0 31 true (0),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 13 (5,true),
.cycle 16 7 false (1),
.last 14 (5,true),
.last 25 (5,true),
.cycle 5 8 true (1),
.last 24 (5,true),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 16 11 false (2),
.last 13 (5,true)
])
theorem kid04_part498_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part498) = true := by rfl

def kid04_part499 : Audit := .split 13 (5,true) (byMove [
.cycle 0 48 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 33 1 false (1),
.last 20 (4,false),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.cycle 1 15 true (1),
.last 15 (4,false),
.cycle 2 14 true (1),
.last 18 (4,false),
.cycle 25 1 false (5),
.cycle 45 22 false (0),
.cycle 15 8 false (1),
.last 15 (4,false),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 15 1 false (-1),
.cycle 17 11 false (2),
.cycle 1 15 true (1),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.cycle 17 9 false (1),
.cycle 14 3 true (2)
])
theorem kid04_part499_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part499) = true := by rfl

def kid04_part500 : Audit := .cycle 0 12 true (0)
theorem kid04_part500_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part500) = true := by rfl

def kid04_part501 : Audit := .cycle 1 11 true (1)
theorem kid04_part501_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part501) = true := by rfl

def kid04_part502 : Audit := .cycle 2 10 true (1)
theorem kid04_part502_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part502) = true := by rfl

def kid04_part503 : Audit := .cycle 2 13 true (1)
theorem kid04_part503_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part503) = true := by rfl

def kid04_part504 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 26 1 false (-2),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 19 true (1),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (1),
.last 14 (5,true),
.cycle 6 15 false (4),
.cycle 2 13 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid04_part504_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part504) = true := by rfl

def kid04_part505 : Audit := .cycle 11 1 true (3)
theorem kid04_part505_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part505) = true := by rfl

def kid04_part481 : Audit := .split 11 (5,false) (byMove [(kid04_part482),(kid04_part483),(kid04_part484),(kid04_part485),(kid04_part486),(kid04_part487),(kid04_part488),(kid04_part489),(kid04_part490),(kid04_part491),(kid04_part492),(kid04_part493),(kid04_part494),(kid04_part495),(kid04_part496),(kid04_part497),(kid04_part498),(kid04_part499),(kid04_part500),(kid04_part501),(kid04_part502),(kid04_part503),(kid04_part504),(kid04_part505)])

theorem kid04_part481_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part481) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part482),(kid04_part483),(kid04_part484),(kid04_part485),(kid04_part486),(kid04_part487),(kid04_part488),(kid04_part489),(kid04_part490),(kid04_part491),(kid04_part492),(kid04_part493),(kid04_part494),(kid04_part495),(kid04_part496),(kid04_part497),(kid04_part498),(kid04_part499),(kid04_part500),(kid04_part501),(kid04_part502),(kid04_part503),(kid04_part504),(kid04_part505)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid04_part486_checked

  · exact kid04_part492_checked

  · exact kid04_part498_checked

  · exact kid04_part504_checked

  · exact kid04_part487_checked

  · exact kid04_part493_checked

  · exact kid04_part499_checked

  · exact kid04_part505_checked

def kid04_part506 : Audit := .cycle 14 5 false (1)
theorem kid04_part506_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part506) = true := by rfl

def kid04_part507 : Audit := .cycle 11 6 false (1)
theorem kid04_part507_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part507) = true := by rfl

def kid04_part508 : Audit := .split 16 (4,false) (byMove [
.cycle 288 116 false (-4),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 11 12 false (1),
.last 46 (5,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 true (-3),
.last 20 (5,true),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 11 14 false (1),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 11 15 false (1),
.last 46 (5,true),
.cycle 11 12 false (1),
.last 50 (5,true),
.last 19 (5,true),
.last 20 (5,true)
]),
.cycle 13 4 true (-2),
.cycle 11 7 false (1),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.cycle 12 6 true (-2),
.split 17 (5,false) (byMove [
.cycle 11 12 false (1),
.cycle 0 29 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 true (-2),
.cycle 17 1 false (-1),
.cycle 0 21 true (-2),
.cycle 0 29 true (-2),
.cycle 0 23 true (-2),
.cycle 0 25 true (-2),
.cycle 12 6 true (-2),
.last 18 (5,true),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 0 23 true (-2),
.cycle 18 1 false (-2),
.last 19 (5,true),
.cycle 17 1 false (-1),
.cycle 0 21 true (-2),
.cycle 14 4 true (-2),
.cycle 11 7 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 32, 8, 64],[4, 15, 15, 1, 15, 64, 64],64⟩,
.cycle 11 9 false (1),
.last 18 (5,true)
]),
.cycle 13 4 false (0),
.cycle 11 7 false (1),
.cycle 13 6 true (-3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.split 17 (5,false) (byMove [
.cycle 11 12 false (1),
.cycle 13 16 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.last 46 (5,true),
.cycle 13 8 true (-3),
.cycle 15 3 false (-1),
.cycle 13 6 true (-3),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.last 56 (5,true),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.last 46 (5,true),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.last 23 (5,true),
.cycle 11 9 false (1),
.last 18 (5,true)
]),
.cycle 9 8 false (2),
.cycle 11 10 false (1),
.cycle 0 25 true (-2),
.cycle 11 9 false (1),
.cycle 11 12 false (1),
.split 17 (5,false) (byMove [
.cycle 0 29 true (-2),
.cycle 13 8 true (-3),
.cycle 15 3 false (-1),
.cycle 13 6 true (-2),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 0 21 true (-2),
.cycle 0 29 true (-2),
.cycle 0 23 true (-2),
.cycle 0 25 true (-2),
.cycle 8 10 false (2),
.last 18 (5,true),
.cycle 11 8 false (1),
.cycle 11 11 false (1),
.cycle 15 3 false (-1),
.cycle 11 9 false (1),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 0 21 true (-2),
.cycle 10 8 false (2),
.cycle 11 10 false (1),
.cycle 68 20 false (0),
.cycle 11 12 false (1),
.last 18 (5,true)
])
])
theorem kid04_part508_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part508) = true := by rfl

def kid04_part509 : Audit := .cycle 2 11 true (1)
theorem kid04_part509_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part509) = true := by rfl

def kid04_part510 : Audit := .cycle 14 3 false (0)
theorem kid04_part510_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part510) = true := by rfl

def kid04_part512 : Audit := .cycle 0 15 true (0)
theorem kid04_part512_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part512) = true := by rfl

def kid04_part513 : Audit := .split 13 (5,false) (byMove [
.cycle 83 30 false (0),
.cycle 0 23 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 12 2 true (-1),
.last 15 (4,false),
.cycle 0 21 true (-1),
.cycle 0 27 true (-2),
.cycle 0 35 true (-2),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 1, 64],[35, 32, 16, 35, 1, 2, 64],80⟩,
.cycle 6 116 false (6),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 0 25 true (-2),
.cycle 16 43 true (-4),
.cycle 0 21 true (-1),
.cycle 18 45 true (-4),
.cycle 11 3 false (1)
])
theorem kid04_part513_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part513) = true := by rfl

def kid04_part514 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 25 1 false (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 21 1 false (1),
.last 14 (5,false),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 27 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 28 1 false (-2),
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 0 19 true (-1),
.cycle 30 1 false (-2),
.last 14 (5,false)
])
theorem kid04_part514_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part514) = true := by rfl

def kid04_part515 : Audit := .cycle 16 1 false (0)
theorem kid04_part515_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part515) = true := by rfl

def kid04_part516 : Audit := .split 16 (4,false) (byMove [
.cycle 289 116 false (-5),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 13 4 true (-2),
.cycle 12 7 false (0),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.cycle 12 6 true (-2),
.last 17 (5,false),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 13 6 true (-3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 9 8 false (2),
.cycle 12 10 false (0),
.cycle 0 25 true (-2),
.cycle 12 9 false (0),
.cycle 12 12 false (0),
.last 17 (5,false)
])
theorem kid04_part516_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part516) = true := by rfl

def kid04_part517 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 21 4 true (-2),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 17 1 true (1),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 23 6 true (-3),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 9 19 false (2),
.cycle 0 17 true (-1),
.cycle 0 33 true (-2),
.cycle 0 19 true (-1),
.last 14 (4,false),
.cycle 20 1 true (-2)
])
theorem kid04_part517_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part517) = true := by rfl

def kid04_part518 : Audit := .cycle 2 11 true (1)
theorem kid04_part518_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part518) = true := by rfl

def kid04_part519 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 27 true (-2),
.last 15 (4,false),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 22 1 false (0),
.cycle 2 13 true (1),
.cycle 12 2 true (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 17 5 false (0),
.cycle 14 8 false (0),
.last 15 (4,false),
.cycle 23 1 false (-1),
.last 20 (4,false),
.cycle 16 1 false (0),
.cycle 2 13 true (1),
.cycle 10 4 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 17 9 false (1),
.cycle 1 14 true (1)
])
theorem kid04_part519_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part519) = true := by rfl

def kid04_part520 : Audit := .split 13 (4,false) (byMove [
.cycle 0 27 false (3),
.last 15 (5,false),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 19 1 false (-1),
.cycle 16 1 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.last 14 (5,false),
.cycle 17 5 false (0),
.last 15 (5,false),
.cycle 0 25 true (-2),
.cycle 28 1 false (0),
.cycle 19 1 false (-1),
.last 17 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 1 true (1),
.last 14 (5,false)
])
theorem kid04_part520_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part520) = true := by rfl

def kid04_part521 : Audit := .cycle 0 13 true (0)
theorem kid04_part521_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part521) = true := by rfl

def kid04_part522 : Audit := .cycle 8 4 true (1)
theorem kid04_part522_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part522) = true := by rfl

def kid04_part523 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 30 (4,false),
.cycle 41 1 false (7),
.last 14 (4,false),
.cycle 13 1 true (3),
.cycle 9 5 true (1),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.cycle 13 1 true (3)
])
theorem kid04_part523_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part523) = true := by rfl

def kid04_part524 : Audit := .cycle 15 3 false (0)
theorem kid04_part524_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part524) = true := by rfl

def kid04_part525 : Audit := .split 13 (5,false) (byMove [
.cycle 19 6 false (-1),
.cycle 27 6 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 15 6 false (1),
.cycle 12 2 true (-1),
.last 15 (4,false),
.cycle 16 6 false (2),
.cycle 14 6 false (0),
.cycle 14 6 false (0),
.cycle 14 6 false (-1),
.cycle 14 6 false (-1),
.cycle 17 6 false (1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 18 6 false (0),
.cycle 14 6 false (0),
.cycle 14 6 false (0),
.cycle 5 9 false (3),
.cycle 16 6 false (0),
.cycle 11 3 false (1)
])
theorem kid04_part525_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part525) = true := by rfl

def kid04_part526 : Audit := .split 13 (4,false) (byMove [
.cycle 16 13 true (0),
.cycle 28 13 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 18 13 true (-1),
.cycle 0 25 true (-2),
.cycle 14 13 true (0),
.cycle 14 1 false (0),
.cycle 20 13 true (-1),
.last 14 (5,false),
.cycle 20 13 true (0),
.cycle 36 13 true (0),
.cycle 20 13 true (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 5 false (2),
.cycle 97 13 true (1),
.cycle 14 13 true (0),
.cycle 0 27 true (-2),
.cycle 103 13 true (1),
.last 14 (5,false)
])
theorem kid04_part526_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part526) = true := by rfl

def kid04_part527 : Audit := .cycle 19 1 false (-1)
theorem kid04_part527_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part527) = true := by rfl

def kid04_part528 : Audit := .split 16 (4,false) (byMove [
.cycle 12 11 false (0),
.last 28 (5,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 12 7 false (0),
.last 18 (5,false),
.cycle 0 32 true (-2),
.cycle 0 29 true (-2),
.cycle 12 5 false (0),
.cycle 15 2 true (-2),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 17 (5,false),
.cycle 12 10 false (0),
.cycle 14 3 false (0),
.cycle 12 6 false (0),
.cycle 5 12 false (3),
.cycle 12 8 false (0),
.cycle 11 6 false (1)
])
theorem kid04_part528_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part528) = true := by rfl

def kid04_part529 : Audit := .split 13 (5,false) (byMove [
.cycle 12 11 false (0),
.cycle 50 15 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 12 7 false (1),
.cycle 13 2 true (-1),
.last 15 (4,false),
.cycle 14 13 true (-1),
.cycle 12 5 false (0),
.cycle 12 2 true (-1),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 12 9 false (1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 12 10 false (1),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.cycle 5 9 false (3),
.cycle 12 8 false (0),
.cycle 11 3 false (1)
])
theorem kid04_part529_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part529) = true := by rfl

def kid04_part530 : Audit := .cycle 2 11 true (1)
theorem kid04_part530_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part530) = true := by rfl

def kid04_part531 : Audit := .cycle 10 2 true (1)
theorem kid04_part531_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part531) = true := by rfl

def kid04_part532 : Audit := .cycle 15 5 false (1)
theorem kid04_part532_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part532) = true := by rfl

def kid04_part533 : Audit := .cycle 0 13 true (0)
theorem kid04_part533_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part533) = true := by rfl

def kid04_part534 : Audit := .cycle 15 7 false (1)
theorem kid04_part534_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part534) = true := by rfl

def kid04_part535 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.cycle 10 4 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 17 9 false (1),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 28 (4,false),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 13 1 true (3),
.cycle 17 11 false (2),
.cycle 11 5 true (1),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.cycle 17 9 false (1),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.cycle 13 1 true (3)
])
theorem kid04_part535_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part535) = true := by rfl

def kid04_part511 : Audit := .split 11 (5,true) (byMove [(kid04_part512),(kid04_part513),(kid04_part514),(kid04_part515),(kid04_part516),(kid04_part517),(kid04_part518),(kid04_part519),(kid04_part520),(kid04_part521),(kid04_part522),(kid04_part523),(kid04_part524),(kid04_part525),(kid04_part526),(kid04_part527),(kid04_part528),(kid04_part529),(kid04_part530),(kid04_part531),(kid04_part532),(kid04_part533),(kid04_part534),(kid04_part535)])

theorem kid04_part511_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part511) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part512),(kid04_part513),(kid04_part514),(kid04_part515),(kid04_part516),(kid04_part517),(kid04_part518),(kid04_part519),(kid04_part520),(kid04_part521),(kid04_part522),(kid04_part523),(kid04_part524),(kid04_part525),(kid04_part526),(kid04_part527),(kid04_part528),(kid04_part529),(kid04_part530),(kid04_part531),(kid04_part532),(kid04_part533),(kid04_part534),(kid04_part535)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid04_part516_checked

  · exact kid04_part522_checked

  · exact kid04_part528_checked

  · exact kid04_part534_checked

  · exact kid04_part517_checked

  · exact kid04_part523_checked

  · exact kid04_part529_checked

  · exact kid04_part535_checked

def kid04_part536 : Audit := .cycle 0 11 true (0)
theorem kid04_part536_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part536) = true := by rfl

def kid04_part537 : Audit := .cycle 1 10 true (1)
theorem kid04_part537_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part537) = true := by rfl

def kid04_part538 : Audit := .cycle 2 9 true (1)
theorem kid04_part538_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part538) = true := by rfl

def kid04_part539 : Audit := .cycle 2 12 true (1)
theorem kid04_part539_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part539) = true := by rfl

def kid04_part540 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.cycle 15 7 false (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.last 21 (5,false),
.cycle 0 14 true (0),
.cycle 16 5 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 16 7 false (1),
.cycle 17 9 false (1),
.last 21 (5,false),
.cycle 2 13 true (1),
.cycle 13 14 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (1),
.cycle 17 13 false (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 15 9 false (2),
.cycle 16 11 false (2),
.cycle 15 5 false (1),
.cycle 2 12 true (1),
.cycle 15 7 false (1),
.split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.last 21 (5,false),
.cycle 9 5 true (1),
.cycle 16 5 false (1),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 21 (5,false),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 14 (5,false),
.cycle 16 7 false (1),
.cycle 17 9 false (1),
.last 21 (5,false),
.cycle 5 8 true (1),
.cycle 13 14 false (1),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 16 11 false (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 16 11 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 16 13 false (3),
.cycle 17 15 false (3),
.cycle 16 9 false (2),
.cycle 2 13 true (1),
.cycle 16 11 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid04_part540_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part540) = true := by rfl

def kid04_part541 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.cycle 15 7 false (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 16 5 false (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 16 7 false (1),
.cycle 12 2 true (1),
.last 20 (4,false),
.cycle 2 13 true (1),
.cycle 12 12 false (2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 11 2 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 24 (4,false) (byMove [
.cycle 2 24 true (1),
.cycle 10 15 true (2),
.cycle 28 21 false (3),
.cycle 0 26 true (0),
.cycle 28 23 false (3),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 12 13 true (2),
.cycle 3 22 true (1),
.cycle 24 1 true (4),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 4, 32, 4, 8192, 16384, 8, 256, 32, 4, 128, 256, 8, 256, 32, 4, 262144],[256, 2048, 4, 1, 133120, 262144, 16384, 131072, 4, 1, 4, 262144, 256, 2048, 8, 1, 8, 262144, 262144],262144⟩,
.cycle 28 25 false (3),
.last 26 (5,true),
.cycle 0 85 true (-2),
.cycle 2 25 true (1),
.cycle 0 91 true (-2),
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 2 26 true (1),
.cycle 24 1 true (4),
.cycle 11 14 true (2)
]),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 17 9 false (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 28 (5,true),
.cycle 8 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 9 4 true (1),
.cycle 17 13 false (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 36 (5,true),
.cycle 8 6 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 15 9 false (2),
.split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.cycle 10 4 true (2),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 17 9 false (1),
.cycle 14 11 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 28 (4,false),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 19 15 false (3),
.cycle 17 11 false (2),
.cycle 12 2 true (2),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.cycle 17 9 false (1),
.cycle 14 11 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.cycle 11 3 true (2)
]),
.cycle 15 5 false (1),
.cycle 2 12 true (1),
.cycle 15 7 false (1),
.split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.last 20 (4,false),
.cycle 9 5 true (1),
.cycle 16 5 false (1),
.cycle 15 1 false (-1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.cycle 32 1 false (6),
.cycle 16 7 false (1),
.cycle 12 2 true (1),
.last 20 (4,false),
.cycle 5 8 true (1),
.cycle 12 12 false (2),
.cycle 15 1 false (-1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 16 11 false (2),
.cycle 11 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 16 11 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 27 31 false (5),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 16 13 false (3),
.last 14 (5,true),
.cycle 16 9 false (2),
.cycle 2 13 true (1),
.cycle 16 11 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid04_part541_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part541) = true := by rfl

def kid04_part445 : Audit := .split 10 (1,true) (byMove [(kid04_part446),(kid04_part447),(kid04_part448),(kid04_part449),(kid04_part450),(kid04_part451),(kid04_part476),(kid04_part477),(kid04_part478),(kid04_part479),(kid04_part480),(kid04_part481),(kid04_part506),(kid04_part507),(kid04_part508),(kid04_part509),(kid04_part510),(kid04_part511),(kid04_part536),(kid04_part537),(kid04_part538),(kid04_part539),(kid04_part540),(kid04_part541)])

theorem kid04_part445_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (kid04_part445) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part446),(kid04_part447),(kid04_part448),(kid04_part449),(kid04_part450),(kid04_part451),(kid04_part476),(kid04_part477),(kid04_part478),(kid04_part479),(kid04_part480),(kid04_part481),(kid04_part506),(kid04_part507),(kid04_part508),(kid04_part509),(kid04_part510),(kid04_part511),(kid04_part536),(kid04_part537),(kid04_part538),(kid04_part539),(kid04_part540),(kid04_part541)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part446_checked

  · exact kid04_part476_checked

  · exact kid04_part506_checked

  · exact kid04_part536_checked

  · exact kid04_part447_checked

  · exact kid04_part477_checked

  · exact kid04_part507_checked

  · exact kid04_part537_checked

  · exact kid04_part448_checked

  · exact kid04_part478_checked

  · exact kid04_part508_checked

  · exact kid04_part538_checked

  · exact kid04_part449_checked

  · exact kid04_part479_checked

  · exact kid04_part509_checked

  · exact kid04_part539_checked

  · exact kid04_part450_checked

  · exact kid04_part480_checked

  · exact kid04_part510_checked

  · exact kid04_part540_checked

  · exact kid04_part451_checked

  · exact kid04_part481_checked

  · exact kid04_part511_checked

  · exact kid04_part541_checked

def kid04_part543 : Audit := .cycle 9 5 false (2)
theorem kid04_part543_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part543) = true := by rfl

def kid04_part544 : Audit := .cycle 0 16 true (-1)
theorem kid04_part544_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part544) = true := by rfl

def kid04_part545 : Audit := .cycle 14 1 false (0)
theorem kid04_part545_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part545) = true := by rfl

def kid04_part546 : Audit := .cycle 13 1 false (-1)
theorem kid04_part546_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part546) = true := by rfl

def kid04_part547 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 9 7 false (2),
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.last 17 (5,true),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 9 9 false (2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 20 3 false (-2),
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 0 20 true (-2),
.last 16 (5,true),
.last 17 (5,true)
]),
.cycle 16 3 false (0),
.cycle 14 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 3 false (1),
.split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.cycle 14 1 false (0),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 19 1 false (3),
.cycle 0 16 true (-1),
.cycle 15 3 false (1),
.last 15 (5,true),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 14 1 false (0),
.cycle 2 14 true (-1),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 11 4 true (-1),
.last 15 (5,true)
]),
.cycle 16 3 false (-2),
.cycle 14 3 false (-1),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 7 15 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 18 3 false (0),
.cycle 15 3 false (-1),
.last 15 (5,true),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[144, 4194448, 32768, 512, 2048, 256, 128, 128, 16512, 32768, 131072, 16384, 128, 128, 16512, 32768, 131072, 16384, 16, 4194320, 32768, 512, 2048, 256, 16777216],[4194448, 16, 16, 2176, 128, 16777216, 128, 16, 16, 2176, 8192, 16777216, 128, 4194304, 4194304, 128, 8192, 16777216, 4194320, 16, 16, 128, 128, 16777216, 16777216],16777216⟩,
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 16 3 false (-2),
.cycle 15 3 false (-1),
.cycle 8 10 false (2),
.cycle 11 4 false (1),
.last 15 (5,true)
]),
.cycle 11 5 false (1),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.cycle 17 3 false (-1),
.split 14 (5,false) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.cycle 18 3 false (0),
.cycle 15 3 false (-1),
.last 15 (5,true),
.cycle 7 17 false (3),
.cycle 33 3 false (-1),
.cycle 3 17 false (3),
.cycle 0 16 true (-1),
.cycle 8 7 false (2),
.last 15 (5,true),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.last 15 (5,true),
.cycle 27 3 false (-1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (-1),
.last 15 (5,true)
])
])
theorem kid04_part547_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part547) = true := by rfl

def kid04_part549 : Audit := .cycle 0 18 true (-2)
theorem kid04_part549_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part549) = true := by rfl

def kid04_part550 : Audit := .cycle 20 3 false (0)
theorem kid04_part550_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part550) = true := by rfl

def kid04_part551 : Audit := .cycle 15 1 false (-1)
theorem kid04_part551_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part551) = true := by rfl

def kid04_part552 : Audit := .cycle 14 1 false (-2)
theorem kid04_part552_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part552) = true := by rfl

def kid04_part553 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 9 7 false (2),
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 3 false (1),
.cycle 13 2 true (-2),
.last 17 (5,true),
.cycle 15 3 false (-2),
.cycle 9 9 false (2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 0 20 true (-2),
.last 19 (5,true),
.cycle 16 3 false (-2)
])
theorem kid04_part553_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part553) = true := by rfl

def kid04_part554 : Audit := .cycle 13 1 false (-1)
theorem kid04_part554_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part554) = true := by rfl

def kid04_part555 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 23 3 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 18 true (-1),
.cycle 0 17 true (-1),
.cycle 23 3 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 0 18 true (-1),
.cycle 14 3 false (1),
.cycle 17 3 false (0),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 24 3 false (2),
.cycle 14 17 true (0),
.cycle 1 16 true (-1),
.cycle 22 3 false (2),
.cycle 25 3 false (3),
.last 17 (4,false),
.cycle 0 18 true (-1)
])
theorem kid04_part555_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part555) = true := by rfl

def kid04_part556 : Audit := .cycle 14 3 false (1)
theorem kid04_part556_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part556) = true := by rfl

def kid04_part557 : Audit := .cycle 0 16 true (-1)
theorem kid04_part557_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part557) = true := by rfl

def kid04_part558 : Audit := .cycle 14 1 false (0)
theorem kid04_part558_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part558) = true := by rfl

def kid04_part559 : Audit := .split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 2 true (-1),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 18 1 false (2),
.cycle 0 16 true (-1),
.cycle 15 3 false (1),
.last 15 (5,true),
.last 17 (5,true),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 3 false (0),
.cycle 2 14 true (-1),
.last 16 (5,true),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 11 4 true (-1),
.last 15 (5,true)
])
theorem kid04_part559_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part559) = true := by rfl

def kid04_part560 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (-1),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 16 1 true (0),
.cycle 0 16 true (-1),
.cycle 22 3 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 16 1 true (2),
.cycle 15 3 false (1),
.cycle 16 3 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 14 2 true (0),
.cycle 15 17 true (1),
.cycle 1 15 true (-1),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.last 16 (4,false),
.cycle 16 1 true (2)
])
theorem kid04_part560_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part560) = true := by rfl

def kid04_part561 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 23 3 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 9 9 false (2),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.cycle 17 3 false (-2),
.cycle 9 11 false (2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 18 17 true (-2),
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 0 22 true (-2),
.last 17 (4,false),
.cycle 19 3 false (-1)
])
theorem kid04_part561_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part561) = true := by rfl

def kid04_part562 : Audit := .cycle 14 3 false (-1)
theorem kid04_part562_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part562) = true := by rfl

def kid04_part563 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 25 3 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 0 22 true (-2),
.cycle 0 19 true (-2),
.cycle 25 3 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 0 22 true (-2),
.cycle 16 3 false (1),
.cycle 19 3 false (0),
.cycle 0 21 true (-2),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 28 3 false (2),
.cycle 16 17 true (0),
.cycle 1 18 true (-2),
.cycle 24 3 false (2),
.cycle 27 3 false (3),
.last 19 (4,false),
.last 21 (4,false)
])
theorem kid04_part563_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part563) = true := by rfl

def kid04_part564 : Audit := .cycle 14 1 false (-2)
theorem kid04_part564_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part564) = true := by rfl

def kid04_part565 : Audit := .split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.last 20 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 18 true (-2),
.cycle 12 3 false (0),
.cycle 18 1 false (0),
.last 18 (5,true),
.cycle 15 3 false (-1),
.last 15 (5,true),
.last 17 (5,true),
.cycle 15 3 false (-2),
.last 41 (5,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 18 true (-2),
.last 16 (5,true),
.cycle 15 3 false (-1),
.last 18 (5,true),
.cycle 11 4 false (1),
.last 15 (5,true)
])
theorem kid04_part565_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part565) = true := by rfl

def kid04_part566 : Audit := .cycle 13 1 false (-1)
theorem kid04_part566_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part566) = true := by rfl

def kid04_part567 : Audit := .split 16 (5,true) (byMove [
.cycle 23 3 false (1),
.cycle 39 3 false (-1),
.last 18 (4,false),
.cycle 0 18 true (-1),
.cycle 17 3 false (-1),
.cycle 28 7 false (1),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.last 17 (4,false),
.cycle 2 32 true (-1),
.cycle 18 3 false (0),
.cycle 12 5 false (1),
.last 18 (4,false),
.cycle 24 3 false (2),
.cycle 17 3 false (-1),
.cycle 10 10 false (2),
.cycle 14 17 true (0),
.cycle 9 21 false (3),
.cycle 2 15 false (3),
.cycle 7 21 false (3),
.last 17 (4,false),
.cycle 20 14 true (1)
])
theorem kid04_part567_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part567) = true := by rfl

def kid04_part568 : Audit := .cycle 9 5 false (2)
theorem kid04_part568_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part568) = true := by rfl

def kid04_part569 : Audit := .cycle 0 16 true (-1)
theorem kid04_part569_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part569) = true := by rfl

def kid04_part570 : Audit := .cycle 17 3 false (1)
theorem kid04_part570_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part570) = true := by rfl

def kid04_part571 : Audit := .split 14 (4,false) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.cycle 18 1 false (-2),
.last 18 (5,true),
.cycle 15 3 false (-1),
.last 15 (5,true),
.cycle 7 17 false (3),
.last 33 (5,true),
.cycle 23 3 false (1),
.cycle 0 16 true (-1),
.cycle 8 7 false (2),
.last 15 (5,true),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.last 21 (5,true),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.last 15 (5,true),
.last 27 (5,true),
.last 16 (5,true),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 17 (5,true),
.last 15 (5,true)
])
theorem kid04_part571_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part571) = true := by rfl

def kid04_part572 : Audit := .split 15 (5,true) (byMove [
.cycle 2 15 false (3),
.cycle 24 3 false (0),
.cycle 16 3 false (0),
.cycle 0 17 true (-1),
.cycle 11 5 false (1),
.cycle 18 1 true (-2),
.cycle 0 16 true (-1),
.cycle 32 3 false (1),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.last 16 (4,false),
.cycle 16 1 true (2),
.cycle 10 7 false (2),
.cycle 18 3 false (-1),
.cycle 16 3 false (0),
.cycle 7 19 false (3),
.cycle 11 5 false (1),
.cycle 16 3 false (0),
.cycle 15 17 true (1),
.cycle 9 25 false (4),
.cycle 0 30 true (-1),
.cycle 37 3 false (1),
.last 16 (4,false),
.cycle 16 1 true (2)
])
theorem kid04_part572_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part572) = true := by rfl

def kid04_part548 : Audit := .split 13 (5,false) (byMove [(kid04_part549),(kid04_part550),(kid04_part551),(kid04_part552),(kid04_part553),(kid04_part554),(kid04_part555),(kid04_part556),(kid04_part557),(kid04_part558),(kid04_part559),(kid04_part560),(kid04_part561),(kid04_part562),(kid04_part563),(kid04_part564),(kid04_part565),(kid04_part566),(kid04_part567),(kid04_part568),(kid04_part569),(kid04_part570),(kid04_part571),(kid04_part572)])

theorem kid04_part548_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part548) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) 13 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part549),(kid04_part550),(kid04_part551),(kid04_part552),(kid04_part553),(kid04_part554),(kid04_part555),(kid04_part556),(kid04_part557),(kid04_part558),(kid04_part559),(kid04_part560),(kid04_part561),(kid04_part562),(kid04_part563),(kid04_part564),(kid04_part565),(kid04_part566),(kid04_part567),(kid04_part568),(kid04_part569),(kid04_part570),(kid04_part571),(kid04_part572)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part549_checked

  · exact kid04_part555_checked

  · exact kid04_part561_checked

  · exact kid04_part567_checked

  · exact kid04_part550_checked

  · exact kid04_part556_checked

  · exact kid04_part562_checked

  · exact kid04_part568_checked

  · exact kid04_part551_checked

  · exact kid04_part557_checked

  · exact kid04_part563_checked

  · exact kid04_part569_checked

  · exact kid04_part552_checked

  · exact kid04_part558_checked

  · exact kid04_part564_checked

  · exact kid04_part570_checked

  · exact kid04_part553_checked

  · exact kid04_part559_checked

  · exact kid04_part565_checked

  · exact kid04_part571_checked

  · exact kid04_part554_checked

  · exact kid04_part560_checked

  · exact kid04_part566_checked

  · exact kid04_part572_checked

def kid04_part573 : Audit := .cycle 19 3 false (3)
theorem kid04_part573_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part573) = true := by rfl

def kid04_part574 : Audit := .cycle 20 3 false (4)
theorem kid04_part574_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part574) = true := by rfl

def kid04_part575 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.split 15 (5,false) (byMove [
.cycle 0 16 false (3),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 14 2 true (-1),
.cycle 15 1 true (-1),
.cycle 24 3 false (0),
.cycle 16 3 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 31 (5,true),
.cycle 1 15 false (3),
.cycle 21 3 false (1),
.cycle 24 3 false (2),
.last 17 (5,true),
.cycle 15 1 true (-1)
]),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 true (0),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 14 2 true (0),
.cycle 15 1 false (1),
.cycle 0 16 true (0),
.cycle 22 3 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 14 2 true (0),
.cycle 15 1 true (1),
.cycle 24 3 false (2),
.cycle 16 3 false (1),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.last 17 (5,true),
.cycle 15 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 14 2 true (0),
.cycle 15 1 true (1)
]),
.cycle 23 3 false (1),
.cycle 15 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.split 15 (5,false) (byMove [
.cycle 9 8 false (2),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 22 3 false (2),
.cycle 18 1 false (2),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 16 3 false (0),
.last 16 (5,true),
.last 20 (5,true),
.cycle 16 3 false (-1),
.cycle 24 3 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 2 15 false (3),
.cycle 23 3 false (1),
.cycle 16 3 false (0),
.cycle 0 17 true (-1),
.cycle 11 5 false (1),
.last 16 (5,true)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.cycle 14 1 true (0),
.split 15 (5,false) (byMove [
.cycle 22 3 false (2),
.cycle 18 1 false (2),
.cycle 13 3 false (1),
.cycle 0 17 true (0),
.cycle 16 3 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 7 18 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.cycle 14 2 true (0),
.cycle 15 1 true (1),
.cycle 17 3 false (1),
.cycle 12 4 true (0),
.cycle 13 3 false (1),
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 7 20 true (0),
.cycle 14 2 true (0),
.cycle 15 1 true (1)
])
])
theorem kid04_part575_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part575) = true := by rfl

def kid04_part576 : Audit := .cycle 0 14 true (0)
theorem kid04_part576_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part576) = true := by rfl

def kid04_part577 : Audit := .cycle 13 3 false (1)
theorem kid04_part577_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part577) = true := by rfl

def kid04_part579 : Audit := .cycle 0 14 true (0)
theorem kid04_part579_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part579) = true := by rfl

def kid04_part580 : Audit := .cycle 20 3 false (2)
theorem kid04_part580_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part580) = true := by rfl

def kid04_part581 : Audit := .cycle 15 1 false (1)
theorem kid04_part581_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part581) = true := by rfl

def kid04_part582 : Audit := .cycle 14 1 false (0)
theorem kid04_part582_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part582) = true := by rfl

def kid04_part583 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 true (0),
.last 15 (5,false),
.last 17 (5,false),
.cycle 15 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.cycle 14 1 true (0),
.last 15 (5,false)
])
theorem kid04_part583_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part583) = true := by rfl

def kid04_part584 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 14 1 true (0),
.cycle 14 3 true (-1),
.cycle 15 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.last 15 (4,false),
.cycle 14 1 true (0)
])
theorem kid04_part584_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part584) = true := by rfl

def kid04_part585 : Audit := .cycle 0 14 true (0)
theorem kid04_part585_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part585) = true := by rfl

def kid04_part586 : Audit := .cycle 20 3 false (4)
theorem kid04_part586_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part586) = true := by rfl

def kid04_part587 : Audit := .cycle 15 1 false (3)
theorem kid04_part587_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part587) = true := by rfl

def kid04_part588 : Audit := .cycle 14 1 false (2)
theorem kid04_part588_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part588) = true := by rfl

def kid04_part589 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 21 3 false (5),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.last 15 (5,false),
.last 17 (5,false),
.cycle 15 3 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (4),
.cycle 23 3 false (5),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid04_part589_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part589) = true := by rfl

def kid04_part590 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 21 3 false (5),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.last 15 (4,false),
.cycle 14 1 true (2),
.cycle 14 3 true (1),
.cycle 15 3 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 14 1 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (4),
.cycle 23 3 false (5),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid04_part590_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part590) = true := by rfl

def kid04_part591 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 22 3 false (2),
.cycle 25 3 false (3),
.last 17 (4,false),
.cycle 13 5 false (2),
.cycle 0 17 true (0),
.cycle 7 22 true (0),
.cycle 24 3 false (2),
.cycle 22 3 false (2),
.last 17 (4,false),
.cycle 16 1 true (2),
.cycle 14 3 true (0),
.cycle 9 8 true (0),
.cycle 0 19 true (0),
.cycle 20 3 false (2),
.last 17 (4,false),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 32, 64],[35, 35, 16, 35, 2, 1, 64],80⟩,
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 7 18 true (0),
.cycle 7 24 true (0),
.last 17 (4,false),
.cycle 16 1 true (2)
])
theorem kid04_part591_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part591) = true := by rfl

def kid04_part592 : Audit := .cycle 14 3 false (1)
theorem kid04_part592_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part592) = true := by rfl

def kid04_part593 : Audit := .cycle 0 16 true (0)
theorem kid04_part593_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part593) = true := by rfl

def kid04_part594 : Audit := .cycle 14 1 false (0)
theorem kid04_part594_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part594) = true := by rfl

def kid04_part595 : Audit := .split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.cycle 21 3 false (3),
.last 16 (5,false),
.cycle 18 1 false (2),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 13 2 true (0),
.cycle 20 3 false (0),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.cycle 2 14 true (0),
.last 16 (5,false),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 16 3 false (0)
])
theorem kid04_part595_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part595) = true := by rfl

def kid04_part596 : Audit := .split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 21 3 false (3),
.cycle 23 3 false (5),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 13 2 true (0),
.cycle 20 3 false (0),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 2 14 true (0),
.cycle 1 16 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 13 3 false (1)
])
theorem kid04_part596_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part596) = true := by rfl

def kid04_part597 : Audit := .cycle 0 14 true (0)
theorem kid04_part597_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part597) = true := by rfl

def kid04_part598 : Audit := .cycle 1 13 true (0)
theorem kid04_part598_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part598) = true := by rfl

def kid04_part599 : Audit := .cycle 19 3 false (3)
theorem kid04_part599_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part599) = true := by rfl

def kid04_part600 : Audit := .cycle 22 3 false (4)
theorem kid04_part600_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part600) = true := by rfl

def kid04_part601 : Audit := .split 14 (4,false) (byMove [
.cycle 21 3 false (3),
.last 16 (5,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 7 17 true (0),
.cycle 21 3 false (3),
.cycle 19 3 false (3),
.cycle 14 1 true (2),
.last 15 (5,false),
.cycle 16 3 false (2),
.cycle 12 3 true (0),
.last 21 (5,false),
.cycle 22 3 false (4),
.cycle 15 3 false (1),
.cycle 11 5 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid04_part601_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part601) = true := by rfl

def kid04_part602 : Audit := .split 14 (5,false) (byMove [
.cycle 21 3 false (3),
.cycle 23 3 false (3),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 7 17 true (0),
.cycle 21 3 false (3),
.cycle 19 3 false (3),
.last 15 (4,false),
.cycle 14 1 true (2),
.cycle 16 3 false (2),
.cycle 12 3 true (0),
.last 16 (4,false),
.cycle 22 3 false (4),
.cycle 15 3 false (1),
.cycle 13 3 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid04_part602_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part602) = true := by rfl

def kid04_part578 : Audit := .split 13 (5,true) (byMove [(kid04_part579),(kid04_part580),(kid04_part581),(kid04_part582),(kid04_part583),(kid04_part584),(kid04_part585),(kid04_part586),(kid04_part587),(kid04_part588),(kid04_part589),(kid04_part590),(kid04_part591),(kid04_part592),(kid04_part593),(kid04_part594),(kid04_part595),(kid04_part596),(kid04_part597),(kid04_part598),(kid04_part599),(kid04_part600),(kid04_part601),(kid04_part602)])

theorem kid04_part578_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part578) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) 13 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part579),(kid04_part580),(kid04_part581),(kid04_part582),(kid04_part583),(kid04_part584),(kid04_part585),(kid04_part586),(kid04_part587),(kid04_part588),(kid04_part589),(kid04_part590),(kid04_part591),(kid04_part592),(kid04_part593),(kid04_part594),(kid04_part595),(kid04_part596),(kid04_part597),(kid04_part598),(kid04_part599),(kid04_part600),(kid04_part601),(kid04_part602)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part579_checked

  · exact kid04_part585_checked

  · exact kid04_part591_checked

  · exact kid04_part597_checked

  · exact kid04_part580_checked

  · exact kid04_part586_checked

  · exact kid04_part592_checked

  · exact kid04_part598_checked

  · exact kid04_part581_checked

  · exact kid04_part587_checked

  · exact kid04_part593_checked

  · exact kid04_part599_checked

  · exact kid04_part582_checked

  · exact kid04_part588_checked

  · exact kid04_part594_checked

  · exact kid04_part600_checked

  · exact kid04_part583_checked

  · exact kid04_part589_checked

  · exact kid04_part595_checked

  · exact kid04_part601_checked

  · exact kid04_part584_checked

  · exact kid04_part590_checked

  · exact kid04_part596_checked

  · exact kid04_part602_checked

def kid04_part603 : Audit := .cycle 16 3 false (0)
theorem kid04_part603_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part603) = true := by rfl

def kid04_part604 : Audit := .cycle 13 3 false (0)
theorem kid04_part604_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part604) = true := by rfl

def kid04_part605 : Audit := .cycle 21 3 false (3)
theorem kid04_part605_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part605) = true := by rfl

def kid04_part606 : Audit := .cycle 13 1 false (-1)
theorem kid04_part606_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part606) = true := by rfl

def kid04_part607 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.cycle 7 22 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 37 3 false (-3),
.cycle 21 3 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.last 16 (5,true),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 19 3 false (-1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 6 false (1),
.cycle 9 6 false (2),
.cycle 7 22 false (3),
.cycle 18 3 false (0),
.last 16 (5,true),
.last 16 (5,true)
]),
.cycle 15 3 false (1),
.cycle 12 2 true (-1),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.split 14 (5,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.last 17 (5,false),
.cycle 0 16 true (-1),
.cycle 15 3 false (1),
.last 16 (5,false),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.last 15 (5,false),
.cycle 2 14 true (-1),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 11 4 true (-1),
.last 16 (5,false)
]),
.cycle 16 3 false (-2),
.cycle 14 3 false (-1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 7 15 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.last 15 (5,true),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 18 3 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 10 6 false (2),
.cycle 16 3 false (-2),
.cycle 15 3 false (-1),
.cycle 5 10 false (3),
.cycle 11 4 false (1),
.last 15 (5,true)
]),
.cycle 10 5 false (2),
.cycle 15 3 false (-1),
.cycle 14 3 false (0),
.cycle 7 17 false (3),
.cycle 11 3 false (1),
.split 14 (5,true) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.last 17 (5,false),
.cycle 18 3 false (0),
.cycle 15 3 false (-1),
.last 16 (5,false),
.cycle 7 17 false (3),
.cycle 33 3 false (-1),
.last 17 (5,false),
.cycle 0 16 true (-1),
.cycle 8 7 false (2),
.last 16 (5,false),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.last 17 (5,false),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.last 16 (5,false),
.cycle 27 3 false (-1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (-1),
.last 16 (5,false)
])
])
theorem kid04_part607_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part607) = true := by rfl

def kid04_part609 : Audit := .cycle 9 6 false (2)
theorem kid04_part609_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part609) = true := by rfl

def kid04_part610 : Audit := .cycle 7 22 false (3)
theorem kid04_part610_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part610) = true := by rfl

def kid04_part611 : Audit := .cycle 15 1 false (-1)
theorem kid04_part611_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part611) = true := by rfl

def kid04_part612 : Audit := .cycle 14 1 false (-2)
theorem kid04_part612_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part612) = true := by rfl

def kid04_part613 : Audit := .split 14 (4,false) (byMove [
.last 37 (5,true),
.cycle 21 3 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (5,true),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 16 3 false (0),
.cycle 13 2 true (-2),
.last 17 (5,true),
.cycle 15 3 false (-2),
.last 19 (5,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (5,true),
.cycle 9 6 false (2),
.cycle 7 22 false (3),
.cycle 18 3 false (0),
.last 18 (5,true),
.cycle 16 3 false (-2)
])
theorem kid04_part613_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part613) = true := by rfl

def kid04_part614 : Audit := .cycle 13 1 false (-1)
theorem kid04_part614_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part614) = true := by rfl

def kid04_part615 : Audit := .cycle 15 3 false (1)
theorem kid04_part615_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part615) = true := by rfl

def kid04_part616 : Audit := .cycle 12 2 true (-1)
theorem kid04_part616_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part616) = true := by rfl

def kid04_part617 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.last 18 (5,true),
.cycle 16 3 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 17 3 false (1),
.cycle 21 1 false (3),
.last 18 (5,true),
.cycle 16 3 false (-1),
.last 20 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 13 3 false (0),
.last 18 (5,true),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 19 3 false (1),
.last 19 (5,true),
.cycle 3 19 false (3)
])
theorem kid04_part617_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part617) = true := by rfl

def kid04_part618 : Audit := .cycle 21 3 false (3)
theorem kid04_part618_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part618) = true := by rfl

def kid04_part619 : Audit := .cycle 14 3 false (0)
theorem kid04_part619_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part619) = true := by rfl

def kid04_part620 : Audit := .split 14 (5,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 18 1 true (0),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 15 3 false (1),
.cycle 16 1 true (2),
.cycle 14 3 false (0),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 13 2 true (-1),
.cycle 2 14 true (-1),
.cycle 14 2 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 11 4 true (-1),
.cycle 16 1 true (2)
])
theorem kid04_part620_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part620) = true := by rfl

def kid04_part621 : Audit := .split 16 (5,true) (byMove [
.cycle 9 9 false (2),
.cycle 7 17 false (3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 18 3 false (0),
.cycle 12 5 false (0),
.last 18 (4,false),
.cycle 19 3 false (1),
.cycle 17 3 false (-1),
.cycle 18 5 true (0),
.cycle 14 3 false (-1),
.cycle 17 3 false (-2),
.cycle 20 3 false (0),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 10 8 false (2),
.cycle 15 2 true (-2),
.cycle 17 3 false (-1),
.cycle 5 12 false (3),
.cycle 11 6 false (1),
.cycle 17 8 true (-1)
])
theorem kid04_part621_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part621) = true := by rfl

def kid04_part622 : Audit := .cycle 14 3 false (-1)
theorem kid04_part622_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part622) = true := by rfl

def kid04_part623 : Audit := .cycle 17 3 false (1)
theorem kid04_part623_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part623) = true := by rfl

def kid04_part624 : Audit := .cycle 14 1 false (-2)
theorem kid04_part624_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part624) = true := by rfl

def kid04_part625 : Audit := .split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 7 15 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.cycle 25 3 false (3),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.last 15 (5,true),
.last 17 (5,true),
.cycle 15 3 false (-2),
.cycle 18 3 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 10 6 false (2),
.last 16 (5,true),
.cycle 15 3 false (-1),
.cycle 5 10 false (3),
.cycle 11 4 false (1),
.last 15 (5,true)
])
theorem kid04_part625_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part625) = true := by rfl

def kid04_part626 : Audit := .cycle 13 1 false (-1)
theorem kid04_part626_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part626) = true := by rfl

def kid04_part627 : Audit := .cycle 10 5 false (2)
theorem kid04_part627_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part627) = true := by rfl

def kid04_part628 : Audit := .split 15 (5,true) (byMove [
.cycle 9 8 false (2),
.cycle 7 24 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 9 8 false (2),
.cycle 17 3 false (1),
.cycle 12 4 true (-1),
.last 17 (4,false),
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.cycle 1 18 true (-1),
.cycle 14 3 false (0),
.cycle 16 3 false (-1),
.cycle 19 3 false (1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 13 3 false (0),
.cycle 10 7 false (2),
.cycle 14 2 true (-1),
.cycle 16 3 false (0),
.cycle 7 19 false (3),
.cycle 11 5 false (1),
.cycle 14 16 true (-1)
])
theorem kid04_part628_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part628) = true := by rfl

def kid04_part629 : Audit := .cycle 14 3 false (0)
theorem kid04_part629_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part629) = true := by rfl

def kid04_part630 : Audit := .cycle 7 17 false (3)
theorem kid04_part630_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part630) = true := by rfl

def kid04_part631 : Audit := .cycle 11 3 false (1)
theorem kid04_part631_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part631) = true := by rfl

def kid04_part632 : Audit := .split 14 (5,true) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.last 16 (4,false),
.cycle 19 1 false (-1),
.cycle 15 3 false (-1),
.cycle 23 1 true (-3),
.cycle 7 17 false (3),
.cycle 12 22 true (-1),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 8 7 false (2),
.cycle 16 1 true (2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.last 16 (4,false),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.cycle 13 3 false (0),
.cycle 10 19 false (3),
.cycle 14 2 true (0),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 11 7 false (1),
.cycle 16 1 true (2)
])
theorem kid04_part632_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part632) = true := by rfl

def kid04_part608 : Audit := .split 13 (5,false) (byMove [(kid04_part609),(kid04_part610),(kid04_part611),(kid04_part612),(kid04_part613),(kid04_part614),(kid04_part615),(kid04_part616),(kid04_part617),(kid04_part618),(kid04_part619),(kid04_part620),(kid04_part621),(kid04_part622),(kid04_part623),(kid04_part624),(kid04_part625),(kid04_part626),(kid04_part627),(kid04_part628),(kid04_part629),(kid04_part630),(kid04_part631),(kid04_part632)])

theorem kid04_part608_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part608) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) 13 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part609),(kid04_part610),(kid04_part611),(kid04_part612),(kid04_part613),(kid04_part614),(kid04_part615),(kid04_part616),(kid04_part617),(kid04_part618),(kid04_part619),(kid04_part620),(kid04_part621),(kid04_part622),(kid04_part623),(kid04_part624),(kid04_part625),(kid04_part626),(kid04_part627),(kid04_part628),(kid04_part629),(kid04_part630),(kid04_part631),(kid04_part632)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part609_checked

  · exact kid04_part615_checked

  · exact kid04_part621_checked

  · exact kid04_part627_checked

  · exact kid04_part610_checked

  · exact kid04_part616_checked

  · exact kid04_part622_checked

  · exact kid04_part628_checked

  · exact kid04_part611_checked

  · exact kid04_part617_checked

  · exact kid04_part623_checked

  · exact kid04_part629_checked

  · exact kid04_part612_checked

  · exact kid04_part618_checked

  · exact kid04_part624_checked

  · exact kid04_part630_checked

  · exact kid04_part613_checked

  · exact kid04_part619_checked

  · exact kid04_part625_checked

  · exact kid04_part631_checked

  · exact kid04_part614_checked

  · exact kid04_part620_checked

  · exact kid04_part626_checked

  · exact kid04_part632_checked

def kid04_part633 : Audit := .cycle 2 12 true (0)
theorem kid04_part633_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part633) = true := by rfl

def kid04_part634 : Audit := .cycle 1 13 true (0)
theorem kid04_part634_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part634) = true := by rfl

def kid04_part635 : Audit := .cycle 13 3 false (1)
theorem kid04_part635_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part635) = true := by rfl

def kid04_part636 : Audit := .cycle 0 14 true (0)
theorem kid04_part636_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part636) = true := by rfl

def kid04_part637 : Audit := .cycle 11 2 true (0)
theorem kid04_part637_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part637) = true := by rfl

def kid04_part639 : Audit := .cycle 20 3 false (2)
theorem kid04_part639_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part639) = true := by rfl

def kid04_part640 : Audit := .split 15 (5,false) (byMove [
.cycle 22 3 false (2),
.cycle 14 2 true (0),
.last 17 (4,false),
.cycle 0 17 true (0),
.cycle 16 3 false (0),
.cycle 23 3 false (1),
.cycle 0 16 true (0),
.cycle 7 18 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.last 16 (4,false),
.cycle 15 1 true (1),
.cycle 17 3 false (1),
.cycle 12 4 true (0),
.last 17 (4,false),
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.cycle 0 20 true (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 7 20 true (0),
.last 16 (4,false),
.cycle 15 1 true (1)
])
theorem kid04_part640_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part640) = true := by rfl

def kid04_part641 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 false (3),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 true (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 16 3 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.cycle 30 3 false (0),
.cycle 1 15 false (3),
.cycle 21 3 false (1),
.cycle 24 3 false (2),
.cycle 15 1 true (-1),
.last 16 (5,false)
])
theorem kid04_part641_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part641) = true := by rfl

def kid04_part642 : Audit := .cycle 0 15 true (0)
theorem kid04_part642_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part642) = true := by rfl

def kid04_part643 : Audit := .cycle 14 3 false (0)
theorem kid04_part643_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part643) = true := by rfl

def kid04_part644 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (3),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 15 1 true (-1),
.cycle 10 10 false (2),
.cycle 16 3 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 13 17 false (3),
.cycle 1 15 false (3),
.cycle 21 3 false (1),
.cycle 24 3 false (2),
.last 16 (4,false),
.cycle 15 1 true (-1)
])
theorem kid04_part644_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part644) = true := by rfl

def kid04_part645 : Audit := .cycle 0 14 true (0)
theorem kid04_part645_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part645) = true := by rfl

def kid04_part646 : Audit := .cycle 7 16 true (0)
theorem kid04_part646_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part646) = true := by rfl

def kid04_part647 : Audit := .cycle 20 3 false (2)
theorem kid04_part647_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part647) = true := by rfl

def kid04_part648 : Audit := .cycle 18 3 false (2)
theorem kid04_part648_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part648) = true := by rfl

def kid04_part649 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 7 20 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.cycle 14 1 true (2),
.last 15 (5,false),
.last 17 (5,false),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 18 3 false (2),
.cycle 16 3 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 7 16 true (0),
.cycle 7 22 true (0),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid04_part649_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part649) = true := by rfl

def kid04_part650 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.last 15 (4,false),
.cycle 17 1 false (1),
.cycle 0 15 true (0),
.cycle 7 20 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.last 15 (4,false),
.cycle 14 1 true (2),
.cycle 10 9 true (0),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 18 3 false (2),
.last 15 (4,false),
.cycle 19 1 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 7 16 true (0),
.cycle 7 22 true (0),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid04_part650_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part650) = true := by rfl

def kid04_part651 : Audit := .cycle 15 3 false (1)
theorem kid04_part651_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part651) = true := by rfl

def kid04_part652 : Audit := .cycle 12 2 true (0)
theorem kid04_part652_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part652) = true := by rfl

def kid04_part653 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 16 3 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 17 3 false (1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 16 3 false (-1),
.last 20 (5,false),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 19 3 false (1),
.cycle 20 3 false (0),
.last 16 (5,false)
])
theorem kid04_part653_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part653) = true := by rfl

def kid04_part654 : Audit := .cycle 21 3 false (3)
theorem kid04_part654_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part654) = true := by rfl

def kid04_part655 : Audit := .cycle 14 3 false (0)
theorem kid04_part655_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part655) = true := by rfl

def kid04_part656 : Audit := .split 15 (5,false) (byMove [
.cycle 9 8 false (2),
.cycle 7 24 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 17 3 false (1),
.cycle 12 4 true (-1),
.last 17 (4,false),
.cycle 23 3 false (3),
.cycle 16 3 false (0),
.cycle 14 2 true (-1),
.cycle 13 6 false (1),
.cycle 16 3 false (-1),
.cycle 19 3 false (1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 10 7 false (2),
.cycle 13 5 false (1),
.cycle 16 3 false (0),
.cycle 7 19 false (3),
.cycle 11 5 false (1),
.cycle 13 3 false (1)
])
theorem kid04_part656_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part656) = true := by rfl

def kid04_part657 : Audit := .cycle 0 14 true (0)
theorem kid04_part657_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part657) = true := by rfl

def kid04_part658 : Audit := .cycle 1 13 true (0)
theorem kid04_part658_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part658) = true := by rfl

def kid04_part659 : Audit := .cycle 2 12 true (0)
theorem kid04_part659_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part659) = true := by rfl

def kid04_part660 : Audit := .cycle 7 18 true (0)
theorem kid04_part660_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part660) = true := by rfl

def kid04_part661 : Audit := .split 14 (4,false) (byMove [
.cycle 2 14 true (0),
.last 16 (5,false),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 7 17 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 14 1 true (2),
.last 15 (5,false),
.cycle 10 6 true (0),
.cycle 12 3 true (0),
.cycle 15 3 false (1),
.cycle 7 18 true (0),
.cycle 11 7 true (0),
.cycle 11 5 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid04_part661_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part661) = true := by rfl

def kid04_part662 : Audit := .split 14 (5,false) (byMove [
.cycle 2 14 true (0),
.cycle 14 2 true (1),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 7 17 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.cycle 14 1 true (2),
.cycle 10 6 true (0),
.cycle 12 3 true (0),
.cycle 15 3 false (1),
.cycle 7 18 true (0),
.cycle 13 5 true (0),
.cycle 13 3 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid04_part662_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part662) = true := by rfl

def kid04_part638 : Audit := .split 13 (5,true) (byMove [(kid04_part639),(kid04_part640),(kid04_part641),(kid04_part642),(kid04_part643),(kid04_part644),(kid04_part645),(kid04_part646),(kid04_part647),(kid04_part648),(kid04_part649),(kid04_part650),(kid04_part651),(kid04_part652),(kid04_part653),(kid04_part654),(kid04_part655),(kid04_part656),(kid04_part657),(kid04_part658),(kid04_part659),(kid04_part660),(kid04_part661),(kid04_part662)])

theorem kid04_part638_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part638) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) 13 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part639),(kid04_part640),(kid04_part641),(kid04_part642),(kid04_part643),(kid04_part644),(kid04_part645),(kid04_part646),(kid04_part647),(kid04_part648),(kid04_part649),(kid04_part650),(kid04_part651),(kid04_part652),(kid04_part653),(kid04_part654),(kid04_part655),(kid04_part656),(kid04_part657),(kid04_part658),(kid04_part659),(kid04_part660),(kid04_part661),(kid04_part662)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part639_checked

  · exact kid04_part645_checked

  · exact kid04_part651_checked

  · exact kid04_part657_checked

  · exact kid04_part640_checked

  · exact kid04_part646_checked

  · exact kid04_part652_checked

  · exact kid04_part658_checked

  · exact kid04_part641_checked

  · exact kid04_part647_checked

  · exact kid04_part653_checked

  · exact kid04_part659_checked

  · exact kid04_part642_checked

  · exact kid04_part648_checked

  · exact kid04_part654_checked

  · exact kid04_part660_checked

  · exact kid04_part643_checked

  · exact kid04_part649_checked

  · exact kid04_part655_checked

  · exact kid04_part661_checked

  · exact kid04_part644_checked

  · exact kid04_part650_checked

  · exact kid04_part656_checked

  · exact kid04_part662_checked

def kid04_part542 : Audit := .split 12 (1,true) (byMove [(kid04_part543),(kid04_part544),(kid04_part545),(kid04_part546),(kid04_part547),(kid04_part548),(kid04_part573),(kid04_part574),(kid04_part575),(kid04_part576),(kid04_part577),(kid04_part578),(kid04_part603),(kid04_part604),(kid04_part605),(kid04_part606),(kid04_part607),(kid04_part608),(kid04_part633),(kid04_part634),(kid04_part635),(kid04_part636),(kid04_part637),(kid04_part638)])

theorem kid04_part542_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (kid04_part542) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part543),(kid04_part544),(kid04_part545),(kid04_part546),(kid04_part547),(kid04_part548),(kid04_part573),(kid04_part574),(kid04_part575),(kid04_part576),(kid04_part577),(kid04_part578),(kid04_part603),(kid04_part604),(kid04_part605),(kid04_part606),(kid04_part607),(kid04_part608),(kid04_part633),(kid04_part634),(kid04_part635),(kid04_part636),(kid04_part637),(kid04_part638)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part543_checked

  · exact kid04_part573_checked

  · exact kid04_part603_checked

  · exact kid04_part633_checked

  · exact kid04_part544_checked

  · exact kid04_part574_checked

  · exact kid04_part604_checked

  · exact kid04_part634_checked

  · exact kid04_part545_checked

  · exact kid04_part575_checked

  · exact kid04_part605_checked

  · exact kid04_part635_checked

  · exact kid04_part546_checked

  · exact kid04_part576_checked

  · exact kid04_part606_checked

  · exact kid04_part636_checked

  · exact kid04_part547_checked

  · exact kid04_part577_checked

  · exact kid04_part607_checked

  · exact kid04_part637_checked

  · exact kid04_part548_checked

  · exact kid04_part578_checked

  · exact kid04_part608_checked

  · exact kid04_part638_checked

def kid04_part663 : Audit := .cycle 0 11 true (0)
theorem kid04_part663_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,2⟩)) (kid04_part663) = true := by rfl

def kid04_part664 : Audit := .cycle 14 1 false (0)
theorem kid04_part664_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,3⟩)) (kid04_part664) = true := by rfl

def kid04_part666 : Audit := .cycle 0 13 true (0)
theorem kid04_part666_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part666) = true := by rfl

def kid04_part667 : Audit := .split 10 (1,true) (byMove [
.cycle 0 15 true (-1),
.cycle 0 38 true (-2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 15, 15, 1, 15, 64, 64],96⟩,
.split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.last 69 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.last 43 (5,true),
.cycle 11 1 false (-1),
.cycle 0 33 true (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 27 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.last 82 (5,true),
.cycle 0 35 true (-2),
.cycle 12 1 false (-2),
.last 121 (5,true),
.cycle 11 1 false (-1),
.last 49 (5,true),
.cycle 0 15 true (-1),
.last 25 (5,true),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 0 15 true (0),
.split 11 (5,false) (byMove [
.cycle 0 33 true (-2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 44 true (-2),
.cycle 11 1 false (1),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 0 26 true (-1),
.cycle 0 13 true (0),
.cycle 0 17 true (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 0 42 true (-2),
.cycle 0 26 true (0),
.cycle 12 1 false (0),
.cycle 0 28 true (-1),
.cycle 11 1 false (1),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.cycle 0 30 true (-1),
.last 12 (5,true)
]),
.cycle 70 71 true (-4),
.cycle 138 86 false (-4),
.cycle 1 32 false (3),
.cycle 11 1 false (-1),
.cycle 0 34 true (-2),
.split 11 (5,false) (byMove [
.last 35 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.last 27 (5,true),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.cycle 10 2 true (-1),
.last 75 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 21 (5,true),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M100.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M100.never m hm),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.last 13 (5,true),
.last 131 (5,true),
.last 15 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M101.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M101.never m hm),
.last 12 (5,true)
]),
.cycle 0 13 true (0),
.cycle 0 31 true (-2),
.cycle 0 13 true (0),
.cycle 0 20 true (-1),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 10 2 true (0),
.last 1881 (5,true),
.cycle 0 17 true (0),
.cycle 0 38 true (-2),
.last 12 (5,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.last 60 (5,true),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.last 12 (5,true),
.cycle 0 42 true (-2),
.last 13 (5,true),
.last 28 (5,true),
.cycle 0 20 true (-1),
.cycle 0 24 true (-2),
.last 12 (5,true),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.cycle 0 31 true (-2),
.cycle 0 13 true (0),
.cycle 0 26 true (-2),
.last 12 (5,true)
])
])
theorem kid04_part667_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part667) = true := by rfl

def kid04_part668 : Audit := .cycle 13 1 false (-1)
theorem kid04_part668_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part668) = true := by rfl

def kid04_part669 : Audit := .split 12 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 15 1 false (-1),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 15 1 false (1),
.last 14 (5,false),
.cycle 11 3 false (2),
.cycle 18 1 false (-2),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 30 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 13 1 true (3),
.cycle 11 3 true (1),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 9 5 true (0),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 27 true (0),
.cycle 32 1 false (0),
.cycle 0 16 true (0),
.cycle 13 1 true (3)
]),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 23 1 false (1),
.cycle 15 1 false (-1),
.split 13 (5,true) (byMove [
.cycle 20 1 false (-2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 14 (5,false),
.cycle 23 1 false (1),
.last 15 (5,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 16 1 false (0),
.last 15 (5,false),
.cycle 11 3 false (2),
.cycle 18 1 false (-2),
.cycle 25 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 14 (5,false),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 29 true (0),
.cycle 0 15 true (0),
.split 13 (5,false) (byMove [
.cycle 2 13 true (0),
.cycle 12 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.cycle 3 11 true (0),
.cycle 0 31 true (0),
.cycle 13 1 true (3),
.cycle 19 1 false (-1),
.last 15 (5,true),
.cycle 17 1 false (-1),
.cycle 0 29 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 30 true (0),
.cycle 0 16 true (0),
.cycle 13 1 true (3)
])
])
theorem kid04_part669_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part669) = true := by rfl

def kid04_part670 : Audit := .cycle 11 1 false (-1)
theorem kid04_part670_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part670) = true := by rfl

def kid04_part672 : Audit := .cycle 0 15 true (-1)
theorem kid04_part672_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part672) = true := by rfl

def kid04_part673 : Audit := .split 20 (5,false) (byMove [
.last 26 (1,true),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 22 (1,true),
.cycle 17 5 false (1),
.last 24 (1,true),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.cycle 10 12 true (-2),
.last 22 (1,true),
.cycle 17 5 false (1),
.last 24 (1,true),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 22 (1,true),
.cycle 18 6 false (0),
.last 24 (1,true),
.cycle 14 7 false (1),
.cycle 9 12 false (1),
.last 23 (1,true)
])
theorem kid04_part673_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part673) = true := by rfl

def kid04_part674 : Audit := .cycle 12 1 false (0)
theorem kid04_part674_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part674) = true := by rfl

def kid04_part675 : Audit := .cycle 11 1 false (-1)
theorem kid04_part675_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part675) = true := by rfl

def kid04_part676 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 17 true (-2),
.cycle 19 5 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 18 1 true (0),
.last 14 (1,true),
.cycle 11 5 false (-1),
.last 39 (1,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 152 (1,true),
.cycle 18 7 false (1),
.cycle 9 4 false (1),
.cycle 19 6 false (-1)
])
theorem kid04_part676_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part676) = true := by rfl

def kid04_part677 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 20 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 true (-1),
.cycle 15 1 true (1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.last 24 (1,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 21 (1,true),
.cycle 0 15 true (-1),
.last 24 (1,true),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.cycle 18 1 true (-2)
])
theorem kid04_part677_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part677) = true := by rfl

def kid04_part678 : Audit := .split 12 (1,true) (byMove [
.last 22 (5,false),
.last 23 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.last 22 (5,false),
.last 22 (5,false),
.last 20 (5,false),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 24 (5,false),
.cycle 0 15 true (0),
.last 13 (5,false)
])
theorem kid04_part678_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part678) = true := by rfl

def kid04_part679 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 17 (1,true),
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 14 2 true (-1),
.cycle 12 12 true (-1),
.last 17 (1,true),
.cycle 11 5 false (2),
.last 19 (1,true),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 17 (1,true),
.cycle 13 6 false (1),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 9 7 false (2),
.cycle 12 12 true (-1)
])
theorem kid04_part679_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part679) = true := by rfl

def kid04_part680 : Audit := .cycle 0 13 true (0)
theorem kid04_part680_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part680) = true := by rfl

def kid04_part681 : Audit := .cycle 11 1 false (1)
theorem kid04_part681_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part681) = true := by rfl

def kid04_part682 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 14 (1,true),
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 11 2 true (0),
.cycle 16 1 true (2),
.last 14 (1,true),
.cycle 11 5 false (1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 14 (1,true),
.cycle 11 6 false (2),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 9 4 true (0),
.cycle 16 1 true (2)
])
theorem kid04_part682_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part682) = true := by rfl

def kid04_part683 : Audit := .split 11 (5,false) (byMove [
.last 122 (1,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.last 23 (1,true),
.last 12 (1,true),
.cycle 16 1 false (2),
.cycle 0 13 true (0),
.cycle 13 2 true (0),
.cycle 13 1 true (3),
.last 13 (1,true),
.cycle 11 5 false (1),
.last 27 (1,true),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.cycle 9 7 false (2),
.cycle 13 1 true (3)
])
theorem kid04_part683_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part683) = true := by rfl

def kid04_part684 : Audit := .split 12 (1,true) (byMove [
.last 22 (5,false),
.last 23 (5,false),
.last 15 (5,false),
.last 20 (5,false),
.last 15 (5,false),
.cycle 10 3 false (0),
.cycle 0 15 true (-1),
.cycle 7 7 false (3),
.cycle 0 15 true (-1),
.last 20 (5,false),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.cycle 0 17 true (-1),
.last 15 (5,false),
.cycle 10 3 false (0),
.last 33 (5,false),
.last 19 (5,false),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 19 (5,false),
.last 13 (5,false)
])
theorem kid04_part684_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part684) = true := by rfl

def kid04_part685 : Audit := .split 15 (5,false) (byMove [
.cycle 2 26 false (3),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 0 39 true (-3),
.cycle 16 1 false (-2),
.cycle 14 2 true (-3),
.cycle 10 7 false (0),
.last 17 (1,true),
.cycle 11 5 false (0),
.last 19 (1,true),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 17 (1,true),
.cycle 13 6 false (-1),
.last 130 (1,true),
.cycle 12 7 false (0),
.cycle 9 7 false (1),
.last 18 (1,true)
])
theorem kid04_part685_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part685) = true := by rfl

def kid04_part686 : Audit := .split 14 (1,true) (byMove [
.last 24 (5,false),
.last 25 (5,false),
.last 17 (5,false),
.cycle 0 16 true (-1),
.last 17 (5,false),
.cycle 0 18 true (-1),
.cycle 0 15 true (-1),
.last 24 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.last 25 (5,false),
.last 17 (5,false),
.last 27 (5,false),
.last 29 (5,false),
.last 27 (5,false),
.cycle 2 13 true (-1),
.last 26 (5,false),
.last 19 (5,false),
.last 15 (5,false)
])
theorem kid04_part686_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part686) = true := by rfl

def kid04_part687 : Audit := .cycle 11 1 false (-1)
theorem kid04_part687_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part687) = true := by rfl

def kid04_part688 : Audit := .split 12 (5,false) (byMove [
.last 18 (1,true),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 14 (1,true),
.cycle 11 5 false (0),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.last 14 (1,true),
.cycle 11 5 false (-1),
.last 16 (1,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 14 (1,true),
.cycle 11 6 false (0),
.last 16 (1,true),
.cycle 11 7 false (0),
.cycle 9 4 false (1),
.cycle 11 6 false (0)
])
theorem kid04_part688_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part688) = true := by rfl

def kid04_part689 : Audit := .split 11 (5,false) (byMove [
.last 38 (1,true),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.last 12 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 13 2 true (-2),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.last 12 (1,true),
.last 130 (1,true),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 10 3 false (0)
])
theorem kid04_part689_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part689) = true := by rfl

def kid04_part690 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (0),
.last 24 (5,false),
.last 16 (5,false),
.cycle 0 14 true (0),
.last 16 (5,false),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.last 22 (5,false),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 14 (5,false),
.last 13 (5,false),
.last 18 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 23 (5,false),
.last 16 (5,false),
.cycle 2 13 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 24 (5,false),
.cycle 0 15 true (0),
.last 13 (5,false)
])
theorem kid04_part690_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part690) = true := by rfl

def kid04_part691 : Audit := .split 16 (5,false) (byMove [
.last 114 (1,true),
.cycle 14 10 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 2 false (-1),
.cycle 16 1 false (-2),
.last 18 (1,true),
.cycle 14 5 false (0),
.cycle 0 31 true (-2),
.cycle 17 1 false (-1),
.cycle 15 2 true (-2),
.last 19 (1,true),
.last 18 (1,true),
.cycle 14 5 false (0),
.last 20 (1,true),
.cycle 17 1 false (-3),
.cycle 15 2 false (-1),
.cycle 16 1 false (-2),
.last 18 (1,true),
.cycle 11 6 false (2),
.cycle 0 31 true (-2),
.cycle 14 7 false (0),
.cycle 9 8 false (2),
.last 19 (1,true)
])
theorem kid04_part691_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part691) = true := by rfl

def kid04_part692 : Audit := .cycle 0 13 true (0)
theorem kid04_part692_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part692) = true := by rfl

def kid04_part693 : Audit := .split 17 (5,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 19 (1,true),
.cycle 14 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 16 2 true (-1),
.cycle 11 14 true (-1),
.last 19 (1,true),
.cycle 14 5 false (2),
.last 21 (1,true),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 19 (1,true),
.cycle 15 6 false (1),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 9 9 false (2),
.cycle 11 14 true (-1)
])
theorem kid04_part693_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part693) = true := by rfl

def kid04_part694 : Audit := .cycle 9 2 true (0)
theorem kid04_part694_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part694) = true := by rfl

def kid04_part695 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 13 2 false (-1),
.cycle 10 2 true (0),
.last 23 (1,true),
.last 12 (1,true),
.last 29 (1,true),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.cycle 13 1 true (3),
.last 18 (1,true),
.last 12 (1,true),
.last 27 (1,true),
.cycle 18 1 false (-2),
.cycle 13 2 false (-1),
.cycle 13 3 true (1),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 0 31 true (-2),
.cycle 0 13 true (0),
.cycle 9 8 false (2),
.cycle 13 1 true (3)
])
theorem kid04_part695_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part695) = true := by rfl

def kid04_part671 : Audit := .split 10 (5,true) (byMove [(kid04_part672),(kid04_part673),(kid04_part674),(kid04_part675),(kid04_part676),(kid04_part677),(kid04_part678),(kid04_part679),(kid04_part680),(kid04_part681),(kid04_part682),(kid04_part683),(kid04_part684),(kid04_part685),(kid04_part686),(kid04_part687),(kid04_part688),(kid04_part689),(kid04_part690),(kid04_part691),(kid04_part692),(kid04_part693),(kid04_part694),(kid04_part695)])

theorem kid04_part671_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part671) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part672),(kid04_part673),(kid04_part674),(kid04_part675),(kid04_part676),(kid04_part677),(kid04_part678),(kid04_part679),(kid04_part680),(kid04_part681),(kid04_part682),(kid04_part683),(kid04_part684),(kid04_part685),(kid04_part686),(kid04_part687),(kid04_part688),(kid04_part689),(kid04_part690),(kid04_part691),(kid04_part692),(kid04_part693),(kid04_part694),(kid04_part695)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part672_checked

  · exact kid04_part678_checked

  · exact kid04_part684_checked

  · exact kid04_part690_checked

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

def kid04_part696 : Audit := .cycle 2 9 true (1)
theorem kid04_part696_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part696) = true := by rfl

def kid04_part697 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 26 1 false (0),
.cycle 0 13 true (0),
.cycle 12 12 true (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 0 22 true (-2),
.cycle 24 1 false (0),
.cycle 13 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 47 1 false (9),
.cycle 35 1 false (7),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 10 3 true (2),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
]),
.cycle 16 7 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 0 17 true (-1),
.last 15 (5,true),
.cycle 12 7 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 0 25 true (-2),
.cycle 19 1 false (-1),
.cycle 13 3 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 13 (5,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 5 false (1),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 24 true (1),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 13 (5,true),
.cycle 7 8 true (1),
.cycle 2 12 true (1),
.last 15 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
])
])
theorem kid04_part697_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part697) = true := by rfl

def kid04_part698 : Audit := .cycle 24 1 false (2)
theorem kid04_part698_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part698) = true := by rfl

def kid04_part699 : Audit := .cycle 0 11 true (0)
theorem kid04_part699_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part699) = true := by rfl

def kid04_part700 : Audit := .cycle 8 2 true (1)
theorem kid04_part700_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part700) = true := by rfl

def kid04_part702 : Audit := .cycle 0 11 true (0)
theorem kid04_part702_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part702) = true := by rfl

def kid04_part703 : Audit := .cycle 1 10 true (1)
theorem kid04_part703_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part703) = true := by rfl

def kid04_part704 : Audit := .cycle 21 1 false (1)
theorem kid04_part704_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part704) = true := by rfl

def kid04_part705 : Audit := .cycle 23 1 false (1)
theorem kid04_part705_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part705) = true := by rfl

def kid04_part706 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 11 2 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.last 14 (1,true),
.cycle 16 7 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
])
theorem kid04_part706_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part706) = true := by rfl

def kid04_part707 : Audit := .split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 15 2 true (-2),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 30 true (-1),
.cycle 24 1 false (0),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1)
])
theorem kid04_part707_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part707) = true := by rfl

def kid04_part708 : Audit := .cycle 0 11 true (0)
theorem kid04_part708_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part708) = true := by rfl

def kid04_part709 : Audit := .cycle 1 10 true (1)
theorem kid04_part709_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part709) = true := by rfl

def kid04_part710 : Audit := .cycle 35 1 false (7)
theorem kid04_part710_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part710) = true := by rfl

def kid04_part711 : Audit := .cycle 20 1 false (2)
theorem kid04_part711_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part711) = true := by rfl

def kid04_part712 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 32 1 false (6),
.cycle 26 1 false (4),
.cycle 11 2 true (3),
.cycle 18 1 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 40 1 false (10),
.cycle 34 1 false (8),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.last 14 (1,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 29 1 false (5),
.cycle 9 4 true (1),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid04_part712_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part712) = true := by rfl

def kid04_part713 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (2),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 35 1 false (7),
.cycle 35 1 false (7),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid04_part713_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part713) = true := by rfl

def kid04_part714 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 21 (5,false),
.cycle 0 14 true (0),
.cycle 14 5 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 16 7 false (0),
.cycle 13 8 false (1),
.last 21 (5,false),
.cycle 2 13 true (1),
.cycle 14 5 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,false),
.last 13 (5,false)
])
theorem kid04_part714_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part714) = true := by rfl

def kid04_part715 : Audit := .cycle 14 5 false (0)
theorem kid04_part715_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part715) = true := by rfl

def kid04_part716 : Audit := .cycle 0 13 true (0)
theorem kid04_part716_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part716) = true := by rfl

def kid04_part717 : Audit := .cycle 18 1 false (0)
theorem kid04_part717_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part717) = true := by rfl

def kid04_part718 : Audit := .cycle 9 2 true (1)
theorem kid04_part718_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part718) = true := by rfl

def kid04_part719 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 15 2 true (-2),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 47 1 false (7),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 10 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 16 13 true (-1),
.cycle 19 1 false (-1),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 5 false (1),
.cycle 13 3 false (1)
])
theorem kid04_part719_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part719) = true := by rfl

def kid04_part720 : Audit := .cycle 0 11 true (0)
theorem kid04_part720_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part720) = true := by rfl

def kid04_part721 : Audit := .cycle 1 10 true (1)
theorem kid04_part721_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part721) = true := by rfl

def kid04_part722 : Audit := .cycle 2 9 true (1)
theorem kid04_part722_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part722) = true := by rfl

def kid04_part723 : Audit := .cycle 2 12 true (1)
theorem kid04_part723_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part723) = true := by rfl

def kid04_part724 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 24 4 true (4),
.cycle 9 13 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.last 14 (1,true),
.cycle 15 4 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (1),
.cycle 14 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid04_part724_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part724) = true := by rfl

def kid04_part725 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 4, 64],[4, 64, 4, 1, 32, 32, 64],64⟩,
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 12 (1,true),
.cycle 2 16 true (1),
.cycle 2 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid04_part725_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part725) = true := by rfl

def kid04_part701 : Audit := .split 10 (5,true) (byMove [(kid04_part702),(kid04_part703),(kid04_part704),(kid04_part705),(kid04_part706),(kid04_part707),(kid04_part708),(kid04_part709),(kid04_part710),(kid04_part711),(kid04_part712),(kid04_part713),(kid04_part714),(kid04_part715),(kid04_part716),(kid04_part717),(kid04_part718),(kid04_part719),(kid04_part720),(kid04_part721),(kid04_part722),(kid04_part723),(kid04_part724),(kid04_part725)])

theorem kid04_part701_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part701) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part702),(kid04_part703),(kid04_part704),(kid04_part705),(kid04_part706),(kid04_part707),(kid04_part708),(kid04_part709),(kid04_part710),(kid04_part711),(kid04_part712),(kid04_part713),(kid04_part714),(kid04_part715),(kid04_part716),(kid04_part717),(kid04_part718),(kid04_part719),(kid04_part720),(kid04_part721),(kid04_part722),(kid04_part723),(kid04_part724),(kid04_part725)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

def kid04_part726 : Audit := .split 15 (1,true) (byMove [
.cycle 0 35 true (-2),
.cycle 10 12 false (1),
.cycle 13 4 false (-1),
.cycle 0 35 true (-2),
.cycle 12 4 false (0),
.split 16 (5,true) (byMove [
.cycle 2 76 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 0 35 true (-2),
.cycle 11 7 false (1),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.last 17 (5,false),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 45 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 32, 16, 17, 16, 17, 64],96⟩,
.cycle 12 8 false (0),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.last 17 (5,false)
]),
.cycle 0 19 true (-2),
.cycle 18 12 true (-1),
.cycle 9 8 false (1),
.cycle 0 29 true (-2),
.cycle 8 8 false (2),
.split 16 (5,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.last 17 (5,false),
.last 19 (5,false),
.cycle 18 12 true (-1),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.last 24 (5,false),
.last 17 (5,false),
.last 19 (5,false),
.cycle 12 8 false (0),
.last 21 (5,false),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.last 17 (5,false),
.last 19 (5,false),
.cycle 8 12 false (2),
.cycle 0 19 true (-2),
.cycle 17 14 true (-1),
.cycle 6 12 false (3),
.last 17 (5,false)
]),
.cycle 10 6 false (1),
.cycle 11 7 false (1),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.cycle 12 4 false (0),
.split 16 (5,true) (byMove [
.cycle 12 9 false (0),
.last 41 (5,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 10 7 false (1),
.last 18 (5,false),
.cycle 13 5 false (-1),
.cycle 0 21 true (-2),
.cycle 12 5 false (0),
.last 19 (5,false),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 12 8 false (0),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 12 6 false (0),
.last 19 (5,false)
]),
.cycle 0 19 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 2, 15, 1, 15, 64, 64],96⟩,
.cycle 12 6 false (0),
.cycle 45 30 false (5),
.cycle 12 6 false (0),
.split 16 (5,true) (byMove [
.cycle 2 16 false (3),
.last 18 (5,false),
.cycle 11 6 false (1),
.cycle 8 14 false (2),
.cycle 12 6 false (0),
.last 19 (5,false),
.last 19 (5,false),
.last 30 (5,false),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.last 24 (5,false),
.last 17 (5,false),
.cycle 12 8 false (0),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 12 6 false (0),
.last 19 (5,false),
.last 19 (5,false),
.last 30 (5,false),
.cycle 0 19 true (-2),
.last 34 (5,false),
.cycle 20 8 false (0),
.last 17 (5,false)
])
])
theorem kid04_part726_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part726) = true := by rfl

def kid04_part727 : Audit := .split 10 (1,true) (byMove [
.cycle 15 4 false (-1),
.cycle 0 34 true (-2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 4 false (-1),
.split 11 (5,false) (byMove [
.last 30 (5,true),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 14 (5,true),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 13 (5,true),
.last 14 (5,true),
.cycle 12 4 false (-1),
.last 16 (5,true),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 14 (5,true),
.cycle 15 4 false (-1),
.cycle 0 34 true (-2),
.cycle 15 4 false (1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 12 4 false (2),
.cycle 19 4 false (5),
.cycle 12 4 false (0),
.cycle 18 4 false (4),
.cycle 11 4 false (1),
.split 11 (5,true) (byMove [
.cycle 16 4 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,false),
.cycle 18 4 false (4),
.last 13 (5,false),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 12 4 false (2),
.last 13 (5,false),
.last 17 (5,false),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,false),
.cycle 2 11 true (0),
.last 13 (5,false),
.cycle 12 4 false (2),
.cycle 0 13 true (0),
.cycle 13 4 false (1),
.last 13 (5,false)
]),
.cycle 14 4 false (0),
.cycle 11 4 false (0),
.cycle 14 4 false (2),
.cycle 11 1 false (-1),
.cycle 11 4 false (-1),
.split 11 (5,false) (byMove [
.cycle 16 4 false (-2),
.cycle 22 4 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 13 4 false (-1),
.cycle 14 4 false (2),
.cycle 12 4 false (0),
.last 12 (5,true),
.last 14 (5,true),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 15 4 false (-1),
.last 13 (5,true),
.cycle 12 4 false (0),
.cycle 5 7 false (3),
.cycle 13 4 false (-1),
.last 12 (5,true)
]),
.cycle 14 4 false (0),
.cycle 1 12 true (0),
.cycle 11 4 false (1),
.cycle 24 4 false (0),
.cycle 12 4 false (0),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 13 4 false (-1),
.last 15 (5,false),
.cycle 12 4 false (0),
.last 13 (5,false),
.cycle 24 4 false (0),
.last 13 (5,false),
.cycle 22 4 false (2),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.last 13 (5,false),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.cycle 13 4 false (-1),
.cycle 14 4 false (2),
.cycle 12 4 false (0),
.last 13 (5,false),
.cycle 2 11 true (0),
.last 13 (5,false),
.cycle 14 4 false (0),
.cycle 0 13 true (0),
.cycle 14 4 false (0),
.last 13 (5,false)
])
])
theorem kid04_part727_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part727) = true := by rfl

def kid04_part728 : Audit := .split 15 (1,true) (byMove [
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.cycle 27 11 true (-2),
.cycle 0 20 true (-2),
.cycle 0 23 true (-2),
.split 16 (5,true) (byMove [
.cycle 0 21 true (-2),
.cycle 0 31 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 27 11 true (-2),
.last 17 (5,false),
.cycle 0 20 true (-2),
.cycle 18 11 true (-1),
.cycle 0 19 true (-2),
.cycle 17 1 false (1),
.cycle 17 11 true (0),
.last 17 (5,false),
.cycle 14 3 false (1),
.cycle 92 11 true (1),
.cycle 0 24 true (-2),
.cycle 17 1 false (-1),
.cycle 0 23 true (-2),
.last 17 (5,false),
.cycle 54 11 true (2),
.cycle 23 11 true (-2),
.cycle 0 19 true (-2),
.cycle 17 11 true (-1),
.cycle 9 8 true (-2),
.last 17 (5,false)
]),
.cycle 16 11 true (1),
.cycle 18 11 true (2),
.cycle 0 38 true (-2),
.cycle 0 17 true (-2),
.cycle 8 8 true (-2),
.split 16 (5,true) (byMove [
.cycle 33 11 true (1),
.cycle 1 16 true (-2),
.cycle 17 11 true (-1),
.cycle 18 11 true (0),
.last 24 (5,false),
.last 17 (5,false),
.cycle 0 17 true (-2),
.cycle 18 11 true (2),
.cycle 30 11 true (2),
.cycle 0 30 true (-2),
.cycle 0 20 true (-2),
.last 17 (5,false),
.last 19 (5,false),
.cycle 23 11 true (-2),
.cycle 0 19 true (-2),
.cycle 17 11 true (-1),
.cycle 9 8 true (-2),
.last 17 (5,false),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 5, 6, 7, 8, 4, 8, 1, 4, 4, 4, 8, 4, 4],[128, 256, 8, 0, 1, 18014398509481984, 524288, 1048576, 32768, 67109120, 131072, 18014398509481984, 2147483648, 4294967296, 134217728, 29273948526117248, 16777216, 18014398509481984, 8796093022208, 17592186044416, 549755813888, 4294967296, 16777216, 18014398509481984, 33554432, 67108864, 2251799813685248, 29273948526117248, 29555423502827904, 18014398509481984, 128, 256, 2251799813685248, 67108864, 18014398509481984, 18014398509481984, 33554432, 67108864, 134217728, 128, 16777216, 18014398509481984, 562949953421312, 1125899906842624, 134217728, 67108864, 29273948526117248, 18014398509481984, 33554432, 67108864, 134217728, 29273948526117248, 9007199271518208, 18014398509481984, 18014398509481984],[256, 32, 128, 1, 256, 64, 1048576, 131072, 32768, 4096, 32768, 262144, 4294967296, 536870912, 18014398509481984, 16777216, 1073741824, 1073741824, 17592186044416, 2199023255552, 29273948526117248, 68719476736, 16777216, 4398046511104, 67108864, 9007199254740992, 29273948526117248, 281474976710656, 29273948526117248, 16777216, 256, 9007199254740992, 128, 281474976710656, 256, 64, 67108864, 536870912, 33554432, 16777216, 67108864, 16777216, 1125899906842624, 536870912, 33554432, 16777216, 67108864, 281474976710656, 67108864, 536870912, 29273948526117248, 16777216, 29273948526117248, 16777216, 18014398509481984],36028246188359522⟩,
.last 34 (5,false),
.cycle 17 11 true (1),
.cycle 18 11 true (2),
.last 26 (5,false),
.last 17 (5,false)
]),
.cycle 0 25 true (-2),
.cycle 24 11 true (0),
.cycle 10 6 true (-2),
.cycle 16 11 true (-1),
.cycle 0 29 true (-2),
.split 16 (5,true) (byMove [
.far true 1 ⟨0,[0, 0],[29, 29, 29, 8, 4, 64, 64],[29, 32, 16, 29, 16, 1, 64],96⟩,
.cycle 18 11 true (0),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 6 true (-2),
.last 17 (5,false),
.cycle 17 11 true (-1),
.last 18 (5,false),
.cycle 0 28 true (-2),
.cycle 17 11 true (1),
.cycle 20 11 true (-1),
.last 19 (5,false),
.cycle 14 3 false (1),
.cycle 24 11 true (0),
.cycle 18 11 true (-1),
.cycle 17 1 false (-1),
.cycle 0 29 true (-2),
.last 17 (5,false),
.cycle 23 11 true (-2),
.cycle 15 2 true (0),
.cycle 0 25 true (-2),
.cycle 17 11 true (1),
.cycle 0 31 true (-2),
.last 19 (5,false)
]),
.cycle 31 11 true (1),
.cycle 50 11 true (2),
.cycle 21 11 true (-2),
.cycle 12 23 true (-2),
.cycle 0 31 true (-2),
.split 16 (5,true) (byMove [
.cycle 2 16 true (-2),
.last 18 (5,false),
.cycle 17 11 true (-2),
.last 36 (5,false),
.cycle 21 11 true (-2),
.last 19 (5,false),
.cycle 12 23 true (-2),
.cycle 18 11 true (2),
.cycle 0 35 true (-2),
.cycle 3 14 true (-2),
.cycle 0 20 true (-2),
.last 17 (5,false),
.cycle 23 11 true (-2),
.cycle 15 2 true (1),
.cycle 0 25 true (-2),
.cycle 17 11 true (1),
.cycle 0 31 true (-2),
.last 19 (5,false),
.cycle 12 29 true (-2),
.cycle 50 11 true (2),
.cycle 31 11 true (1),
.cycle 18 11 true (2),
.cycle 0 44 true (-2),
.last 17 (5,false)
])
])
theorem kid04_part728_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part728) = true := by rfl

def kid04_part729 : Audit := .cycle 15 1 false (-1)
theorem kid04_part729_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part729) = true := by rfl

def kid04_part730 : Audit := .cycle 11 1 false (-1)
theorem kid04_part730_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part730) = true := by rfl

def kid04_part732 : Audit := .split 17 (5,false) (byMove [
.cycle 11 7 false (1),
.last 26 (1,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 15 5 false (-1),
.last 18 (1,true),
.cycle 16 3 false (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M109.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M109.never m hm),
.cycle 15 3 false (-1),
.cycle 10 8 false (1),
.last 19 (1,true),
.cycle 15 5 false (-1),
.cycle 15 7 false (-1),
.cycle 18 1 false (-4),
.cycle 16 2 false (-2),
.cycle 17 1 false (-3),
.cycle 13 6 false (1),
.last 18 (1,true),
.cycle 15 4 false (-1),
.cycle 5 13 false (3),
.cycle 14 4 false (0),
.proven (BB6.Agent11Raw39B1RCPumps.M110.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M110.never m hm)
])
theorem kid04_part732_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part732) = true := by rfl

def kid04_part733 : Audit := .split 23 (5,false) (byMove [
.cycle 28 7 false (0),
.cycle 11 13 true (-1),
.cycle 34 1 false (-2),
.cycle 12 15 true (-1),
.last 30 (1,true),
.cycle 35 1 false (-3),
.cycle 6 23 false (4),
.last 24 (1,true),
.last 47 (1,true),
.cycle 13 11 true (1),
.cycle 24 11 false (2),
.cycle 0 28 true (-1),
.last 25 (1,true),
.cycle 27 5 false (-1),
.cycle 24 13 false (3),
.cycle 31 1 false (-3),
.cycle 35 2 false (-3),
.cycle 24 9 false (2),
.cycle 41 6 false (-1),
.last 24 (1,true),
.cycle 0 34 true (-2),
.cycle 13 11 true (1),
.cycle 37 4 false (-1),
.last 25 (1,true)
])
theorem kid04_part733_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part733) = true := by rfl

def kid04_part734 : Audit := .cycle 12 1 false (0)
theorem kid04_part734_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part734) = true := by rfl

def kid04_part735 : Audit := .cycle 11 1 false (-1)
theorem kid04_part735_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part735) = true := by rfl

def kid04_part736 : Audit := .split 12 (5,false) (byMove [
.cycle 11 7 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 6 25 false (4),
.last 13 (1,true),
.cycle 11 3 false (-1),
.last 15 (1,true),
.cycle 11 3 false (-1),
.cycle 10 3 false (0),
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 28 13 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 32 6 false (-2),
.last 13 (1,true),
.cycle 11 4 false (-1),
.last 15 (1,true),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid04_part736_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part736) = true := by rfl

def kid04_part737 : Audit := .split 11 (5,false) (byMove [
.cycle 31 7 false (-1),
.cycle 26 13 true (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 13 (1,true),
.last 17 (1,true),
.cycle 22 3 false (2),
.cycle 12 1 false (0),
.cycle 12 3 false (0),
.cycle 17 1 true (1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 34 true (-2),
.cycle 0 23 true (-2),
.cycle 9 3 false (1),
.cycle 25 1 true (-3)
])
theorem kid04_part737_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part737) = true := by rfl

def kid04_part738 : Audit := .split 15 (5,false) (byMove [
.cycle 13 7 false (1),
.cycle 11 13 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (2),
.last 16 (1,true),
.cycle 14 3 false (0),
.cycle 11 11 true (-1),
.cycle 13 3 false (1),
.cycle 11 11 true (-1),
.last 17 (1,true),
.cycle 12 5 false (2),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 13 6 false (1),
.last 16 (1,true),
.cycle 12 4 false (2),
.cycle 11 11 true (-1),
.cycle 13 4 false (1),
.cycle 11 11 true (-1)
])
theorem kid04_part738_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part738) = true := by rfl

def kid04_part739 : Audit := .split 11 (1,true) (byMove [
.last 18 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.last 21 (5,false),
.last 22 (5,false),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 22 (5,false),
.last 18 (5,false),
.last 16 (5,false),
.last 23 (5,false),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.last 15 (5,false),
.last 22 (5,false)
])
theorem kid04_part739_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part739) = true := by rfl

def kid04_part740 : Audit := .split 13 (5,false) (byMove [
.cycle 12 7 false (0),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.last 14 (1,true),
.cycle 11 3 false (1),
.last 16 (1,true),
.cycle 12 3 false (0),
.cycle 0 17 true (-1),
.last 15 (1,true),
.cycle 12 5 false (0),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.last 14 (1,true),
.cycle 12 4 false (0),
.last 16 (1,true),
.cycle 12 4 false (0),
.cycle 0 17 true (-1)
])
theorem kid04_part740_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part740) = true := by rfl

def kid04_part741 : Audit := .split 21 (5,false) (byMove [
.cycle 19 7 false (3),
.cycle 11 13 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 17 5 false (4),
.last 22 (1,true),
.cycle 20 3 false (2),
.cycle 11 11 true (1),
.cycle 19 3 false (3),
.cycle 0 24 true (0),
.last 23 (1,true),
.cycle 18 5 false (4),
.cycle 16 7 false (4),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 19 6 false (3),
.last 22 (1,true),
.cycle 18 4 false (4),
.cycle 11 11 true (1),
.cycle 19 4 false (3),
.cycle 0 24 true (0)
])
theorem kid04_part741_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part741) = true := by rfl

def kid04_part742 : Audit := .split 13 (5,false) (byMove [
.cycle 11 7 false (1),
.last 22 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 14 11 true (-1),
.cycle 11 3 false (1),
.cycle 10 4 true (-1),
.last 15 (1,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 6 false (1),
.last 14 (1,true),
.cycle 11 4 false (1),
.cycle 5 9 false (3),
.cycle 11 4 false (1),
.cycle 8 7 false (2)
])
theorem kid04_part742_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part742) = true := by rfl

def kid04_part743 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 15 13 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 2 false (3),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.last 24 (1,true),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 14 3 false (4),
.cycle 13 1 true (3),
.last 15 (1,true),
.cycle 13 5 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 2 false (3),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 4 false (5),
.cycle 15 11 true (3),
.cycle 11 4 true (1),
.cycle 13 1 true (3)
])
theorem kid04_part743_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part743) = true := by rfl

def kid04_part744 : Audit := .split 12 (1,true) (byMove [
.last 25 (5,false),
.last 23 (5,false),
.last 15 (5,false),
.cycle 0 20 true (-1),
.last 15 (5,false),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.last 24 (5,false),
.cycle 9 5 false (1),
.last 23 (5,false),
.cycle 8 5 false (2),
.last 19 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.cycle 10 3 false (0),
.last 19 (5,false),
.last 31 (5,false),
.last 17 (5,false),
.last 23 (5,false),
.last 17 (5,false),
.last 19 (5,false)
])
theorem kid04_part744_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part744) = true := by rfl

def kid04_part745 : Audit := .split 15 (5,false) (byMove [
.cycle 13 7 false (-1),
.cycle 20 13 true (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 5 false (0),
.last 16 (1,true),
.cycle 14 3 false (-2),
.cycle 19 11 true (1),
.cycle 13 3 false (-1),
.cycle 10 6 false (0),
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 13 6 false (-1),
.last 16 (1,true),
.cycle 12 4 false (0),
.cycle 19 11 true (1),
.cycle 13 4 false (-1),
.last 17 (1,true)
])
theorem kid04_part745_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part745) = true := by rfl

def kid04_part746 : Audit := .split 17 (5,false) (byMove [
.cycle 15 7 false (1),
.cycle 12 13 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (2),
.last 18 (1,true),
.cycle 16 3 false (0),
.cycle 12 11 true (-1),
.cycle 15 3 false (1),
.cycle 12 13 true (-1),
.last 19 (1,true),
.cycle 14 5 false (2),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 15 6 false (1),
.last 18 (1,true),
.cycle 14 4 false (2),
.cycle 12 11 true (-1),
.cycle 15 4 false (1),
.cycle 16 4 false (0)
])
theorem kid04_part746_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part746) = true := by rfl

def kid04_part747 : Audit := .cycle 11 1 false (-1)
theorem kid04_part747_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part747) = true := by rfl

def kid04_part748 : Audit := .split 12 (5,false) (byMove [
.cycle 11 7 false (-1),
.last 21 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 5 false (0),
.last 13 (1,true),
.cycle 11 3 false (-1),
.cycle 0 23 true (-2),
.cycle 11 3 false (-1),
.cycle 10 3 false (0),
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 6 false (0),
.last 13 (1,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid04_part748_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part748) = true := by rfl

def kid04_part749 : Audit := .split 11 (5,false) (byMove [
.cycle 11 7 false (0),
.last 20 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 11 5 false (1),
.last 12 (1,true),
.cycle 11 3 false (0),
.cycle 12 11 true (-1),
.cycle 11 3 false (0),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 11 6 false (1),
.last 12 (1,true),
.cycle 11 4 false (0),
.cycle 5 7 false (3),
.cycle 11 4 false (0),
.cycle 10 3 false (0)
])
theorem kid04_part749_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part749) = true := by rfl

def kid04_part750 : Audit := .split 16 (5,false) (byMove [
.cycle 12 7 false (2),
.last 25 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 2 false (-1),
.cycle 16 1 false (-2),
.cycle 14 5 false (0),
.last 17 (1,true),
.cycle 15 3 false (-1),
.cycle 17 11 true (-2),
.cycle 14 3 false (0),
.cycle 10 7 false (2),
.last 18 (1,true),
.cycle 14 5 false (0),
.cycle 14 7 false (0),
.cycle 17 1 false (-3),
.cycle 15 2 false (-1),
.cycle 16 1 false (-2),
.cycle 11 6 false (2),
.last 17 (1,true),
.cycle 14 4 false (0),
.cycle 5 12 false (3),
.cycle 13 4 false (1),
.cycle 13 8 false (1)
])
theorem kid04_part750_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part750) = true := by rfl

def kid04_part751 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.last 22 (5,false),
.last 14 (5,false),
.cycle 0 16 true (0),
.last 14 (5,false),
.last 18 (5,false),
.last 21 (5,false),
.last 22 (5,false),
.last 25 (5,false),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.last 16 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.last 16 (5,false),
.cycle 0 13 true (0),
.last 16 (5,false),
.cycle 1 12 true (0)
])
theorem kid04_part751_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part751) = true := by rfl

def kid04_part752 : Audit := .split 14 (5,false) (byMove [
.cycle 12 7 false (0),
.last 36 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 5 false (1),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 19 true (-2),
.cycle 12 3 false (0),
.cycle 10 5 false (1),
.last 16 (1,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 6 false (0),
.last 15 (1,true),
.cycle 11 4 false (1),
.cycle 0 19 true (-2),
.cycle 12 4 false (0),
.cycle 12 6 false (0)
])
theorem kid04_part752_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part752) = true := by rfl

def kid04_part753 : Audit := .split 21 (5,false) (byMove [
.cycle 39 7 false (1),
.last 22 (1,true),
.cycle 26 1 false (-2),
.last 24 (1,true),
.cycle 23 2 false (-1),
.cycle 29 1 false (-1),
.cycle 6 16 true (0),
.last 22 (1,true),
.last 27 (1,true),
.cycle 11 11 true (1),
.cycle 5 20 true (0),
.cycle 0 24 true (0),
.last 28 (1,true),
.last 22 (1,true),
.cycle 16 13 false (4),
.cycle 28 1 false (-2),
.cycle 23 2 false (-1),
.cycle 5 18 true (0),
.cycle 25 6 false (1),
.last 22 (1,true),
.cycle 24 4 false (0),
.cycle 11 11 true (1),
.cycle 23 4 false (1),
.cycle 0 24 true (0)
])
theorem kid04_part753_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part753) = true := by rfl

def kid04_part754 : Audit := .split 14 (5,false) (byMove [
.cycle 11 7 false (1),
.last 23 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 25 true (-2),
.cycle 12 3 false (0),
.cycle 10 5 false (1),
.last 16 (1,true),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 6 false (1),
.last 15 (1,true),
.cycle 12 4 false (0),
.cycle 5 10 false (3),
.cycle 11 4 false (1),
.cycle 11 6 false (1)
])
theorem kid04_part754_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part754) = true := by rfl

def kid04_part755 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (0),
.last 14 (1,true),
.cycle 20 1 false (-2),
.cycle 0 15 true (0),
.cycle 17 2 false (-1),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.last 24 (1,true),
.cycle 11 18 true (1),
.cycle 3 11 true (0),
.cycle 8 8 true (0),
.cycle 13 1 true (3),
.last 22 (1,true),
.last 14 (1,true),
.cycle 16 7 false (0),
.cycle 5 29 true (0),
.cycle 17 2 false (-1),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 11 true (3),
.cycle 11 4 true (1),
.cycle 13 1 true (3)
])
theorem kid04_part755_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part755) = true := by rfl

def kid04_part731 : Audit := .split 10 (5,true) (byMove [(kid04_part732),(kid04_part733),(kid04_part734),(kid04_part735),(kid04_part736),(kid04_part737),(kid04_part738),(kid04_part739),(kid04_part740),(kid04_part741),(kid04_part742),(kid04_part743),(kid04_part744),(kid04_part745),(kid04_part746),(kid04_part747),(kid04_part748),(kid04_part749),(kid04_part750),(kid04_part751),(kid04_part752),(kid04_part753),(kid04_part754),(kid04_part755)])

theorem kid04_part731_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part731) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part732),(kid04_part733),(kid04_part734),(kid04_part735),(kid04_part736),(kid04_part737),(kid04_part738),(kid04_part739),(kid04_part740),(kid04_part741),(kid04_part742),(kid04_part743),(kid04_part744),(kid04_part745),(kid04_part746),(kid04_part747),(kid04_part748),(kid04_part749),(kid04_part750),(kid04_part751),(kid04_part752),(kid04_part753),(kid04_part754),(kid04_part755)] mv))) = true

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

def kid04_part756 : Audit := .cycle 2 9 true (1)
theorem kid04_part756_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part756) = true := by rfl

def kid04_part757 : Audit := .split 10 (1,true) (byMove [
.cycle 2 10 true (1),
.cycle 11 11 false (1),
.cycle 1 16 false (3),
.cycle 0 12 true (0),
.cycle 12 3 false (0),
.split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.last 13 (5,false),
.cycle 1 13 false (3),
.cycle 0 13 true (0),
.cycle 1 16 false (3),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 12 (5,false),
.cycle 16 3 false (0),
.last 13 (5,false),
.cycle 0 28 true (-3),
.cycle 24 1 false (0),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 12 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 3 8 true (1),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 32 (5,true),
.cycle 0 23 true (0),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 10 3 true (2),
.last 19 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
]),
.cycle 14 5 false (0),
.cycle 11 6 false (1),
.cycle 12 8 false (0),
.cycle 2 11 true (1),
.cycle 12 3 false (0),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 17 true (-1),
.cycle 16 1 false (0),
.cycle 12 8 false (0),
.last 13 (5,false),
.cycle 2 11 true (1),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 13 (5,false),
.cycle 16 3 false (0),
.last 13 (5,false),
.far true 1 ⟨0,[0, 0],[28, 28, 28, 8, 28, 64, 64],[28, 32, 16, 28, 16, 4, 64],96⟩,
.cycle 19 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 5 false (1),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.last 17 (5,true),
.cycle 0 13 true (0),
.last 17 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 24 true (1),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.last 19 (5,true),
.last 13 (5,true),
.last 17 (5,true),
.cycle 2 12 true (1),
.last 17 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
])
])
theorem kid04_part757_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part757) = true := by rfl

def kid04_part758 : Audit := .cycle 12 3 false (0)
theorem kid04_part758_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part758) = true := by rfl

def kid04_part759 : Audit := .cycle 0 11 true (0)
theorem kid04_part759_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part759) = true := by rfl

def kid04_part760 : Audit := .cycle 11 3 false (1)
theorem kid04_part760_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part760) = true := by rfl

def kid04_part762 : Audit := .cycle 2 10 true (1)
theorem kid04_part762_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part762) = true := by rfl

def kid04_part763 : Audit := .split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.last 14 (5,false),
.cycle 0 13 true (0),
.last 17 (5,false),
.last 24 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 14 (5,false),
.cycle 24 1 false (0),
.cycle 13 3 false (0),
.cycle 0 16 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid04_part763_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part763) = true := by rfl

def kid04_part764 : Audit := .split 17 (5,false) (byMove [
.cycle 11 13 false (1),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.cycle 12 6 false (0),
.cycle 20 1 false (-2),
.cycle 7 22 false (3),
.cycle 11 13 true (-2),
.cycle 11 13 false (1),
.cycle 11 11 false (1),
.cycle 16 2 true (-2),
.cycle 17 1 true (-1),
.cycle 11 8 false (1),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 11 14 true (-2),
.cycle 12 6 false (0),
.cycle 20 1 false (-2),
.last 39 (1,true),
.cycle 29 10 false (-1),
.cycle 2 16 false (3),
.cycle 11 15 true (-2),
.cycle 16 2 true (-2),
.cycle 17 1 true (-1)
])
theorem kid04_part764_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part764) = true := by rfl

def kid04_part765 : Audit := .cycle 0 12 true (0)
theorem kid04_part765_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part765) = true := by rfl

def kid04_part766 : Audit := .cycle 12 3 false (0)
theorem kid04_part766_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part766) = true := by rfl

def kid04_part767 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 7 false (1),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 11 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 2 true (-1),
.cycle 13 1 true (-1),
.last 15 (1,true),
.cycle 11 7 false (1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 11 4 false (1),
.cycle 13 1 false (-1),
.cycle 10 15 false (3),
.cycle 1 13 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-1),
.cycle 13 2 true (-1),
.cycle 13 1 true (-1)
])
theorem kid04_part767_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part767) = true := by rfl

def kid04_part768 : Audit := .cycle 0 11 true (0)
theorem kid04_part768_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part768) = true := by rfl

def kid04_part769 : Audit := .cycle 1 10 true (1)
theorem kid04_part769_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part769) = true := by rfl

def kid04_part770 : Audit := .cycle 0 23 true (0)
theorem kid04_part770_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part770) = true := by rfl

def kid04_part771 : Audit := .cycle 3 8 true (1)
theorem kid04_part771_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part771) = true := by rfl

def kid04_part772 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 8 13 false (4),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (1),
.last 13 (1,true),
.cycle 8 18 true (-1),
.cycle 2 13 true (1),
.cycle 8 8 true (1),
.cycle 8 6 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid04_part772_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part772) = true := by rfl

def kid04_part773 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 0, 64],[4, 64, 0, 1, 32, 32, 64],64⟩,
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 26 14 true (4),
.cycle 0 23 true (0),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 13 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 0, 2048, 0, 128, 256, 8, 256, 2048, 4096, 4096],[256, 4096, 4096, 1, 32, 32, 256, 4096, 0, 1, 32, 32, 4096],7184⟩,
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.cycle 25 1 false (5),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid04_part773_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part773) = true := by rfl

def kid04_part774 : Audit := .cycle 14 5 false (0)
theorem kid04_part774_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part774) = true := by rfl

def kid04_part775 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.last 14 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.last 19 (5,false),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 16 7 false (0),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 14 (5,false),
.cycle 19 1 false (-1),
.cycle 13 3 false (0),
.last 19 (5,false),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 5 false (1),
.cycle 10 2 true (1)
])
theorem kid04_part775_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part775) = true := by rfl

def kid04_part776 : Audit := .split 17 (5,false) (byMove [
.last 22 (1,true),
.last 18 (1,true),
.cycle 15 3 false (-1),
.last 20 (1,true),
.cycle 12 6 false (0),
.last 22 (1,true),
.cycle 0 21 true (-2),
.last 18 (1,true),
.cycle 0 23 true (-2),
.last 20 (1,true),
.cycle 8 10 false (2),
.last 22 (1,true),
.cycle 11 8 false (1),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 11 9 false (1),
.cycle 12 6 false (0),
.cycle 11 11 false (1),
.cycle 0 21 true (-2),
.last 18 (1,true),
.cycle 12 8 false (0),
.last 20 (1,true),
.cycle 12 8 false (0),
.cycle 10 8 false (2)
])
theorem kid04_part776_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part776) = true := by rfl

def kid04_part777 : Audit := .cycle 2 11 true (1)
theorem kid04_part777_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part777) = true := by rfl

def kid04_part778 : Audit := .cycle 12 3 false (0)
theorem kid04_part778_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part778) = true := by rfl

def kid04_part779 : Audit := .split 13 (5,false) (byMove [
.cycle 11 9 false (1),
.last 24 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 7 false (1),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.last 14 (1,true),
.cycle 0 51 true (-2),
.cycle 14 13 true (-1),
.cycle 11 5 false (1),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 11 4 false (1),
.cycle 13 1 false (-1),
.cycle 11 8 false (1),
.last 14 (1,true),
.cycle 11 6 false (1),
.cycle 5 9 false (3),
.cycle 11 6 false (1),
.cycle 11 3 false (1)
])
theorem kid04_part779_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part779) = true := by rfl

def kid04_part780 : Audit := .cycle 0 11 true (0)
theorem kid04_part780_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part780) = true := by rfl

def kid04_part781 : Audit := .cycle 1 10 true (1)
theorem kid04_part781_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part781) = true := by rfl

def kid04_part782 : Audit := .cycle 2 9 true (1)
theorem kid04_part782_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part782) = true := by rfl

def kid04_part783 : Audit := .cycle 2 12 true (1)
theorem kid04_part783_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part783) = true := by rfl

def kid04_part784 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 14 5 false (2),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 16 5 false (2),
.last 13 (1,true),
.cycle 14 5 false (2),
.cycle 2 13 true (1),
.cycle 14 5 false (2),
.cycle 16 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid04_part784_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part784) = true := by rfl

def kid04_part785 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 10 7 false (3),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 0, 64],[4, 64, 0, 1, 32, 32, 64],64⟩,
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 14 true (2),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 0, 2048, 4096, 128, 256, 8, 256, 2048, 0, 4096],[256, 4096, 0, 1, 2048, 2048, 256, 4096, 0, 1, 2048, 2048, 4096],4128⟩,
.last 12 (1,true),
.cycle 10 7 false (3),
.cycle 2 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid04_part785_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part785) = true := by rfl

def kid04_part761 : Audit := .split 10 (5,true) (byMove [(kid04_part762),(kid04_part763),(kid04_part764),(kid04_part765),(kid04_part766),(kid04_part767),(kid04_part768),(kid04_part769),(kid04_part770),(kid04_part771),(kid04_part772),(kid04_part773),(kid04_part774),(kid04_part775),(kid04_part776),(kid04_part777),(kid04_part778),(kid04_part779),(kid04_part780),(kid04_part781),(kid04_part782),(kid04_part783),(kid04_part784),(kid04_part785)])

theorem kid04_part761_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part761) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part762),(kid04_part763),(kid04_part764),(kid04_part765),(kid04_part766),(kid04_part767),(kid04_part768),(kid04_part769),(kid04_part770),(kid04_part771),(kid04_part772),(kid04_part773),(kid04_part774),(kid04_part775),(kid04_part776),(kid04_part777),(kid04_part778),(kid04_part779),(kid04_part780),(kid04_part781),(kid04_part782),(kid04_part783),(kid04_part784),(kid04_part785)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part762_checked

  · exact kid04_part768_checked

  · exact kid04_part774_checked

  · exact kid04_part780_checked

  · exact kid04_part763_checked

  · exact kid04_part769_checked

  · exact kid04_part775_checked

  · exact kid04_part781_checked

  · exact kid04_part764_checked

  · exact kid04_part770_checked

  · exact kid04_part776_checked

  · exact kid04_part782_checked

  · exact kid04_part765_checked

  · exact kid04_part771_checked

  · exact kid04_part777_checked

  · exact kid04_part783_checked

  · exact kid04_part766_checked

  · exact kid04_part772_checked

  · exact kid04_part778_checked

  · exact kid04_part784_checked

  · exact kid04_part767_checked

  · exact kid04_part773_checked

  · exact kid04_part779_checked

  · exact kid04_part785_checked

def kid04_part665 : Audit := .split 9 (4,false) (byMove [(kid04_part666),(kid04_part667),(kid04_part668),(kid04_part669),(kid04_part670),(kid04_part671),(kid04_part696),(kid04_part697),(kid04_part698),(kid04_part699),(kid04_part700),(kid04_part701),(kid04_part726),(kid04_part727),(kid04_part728),(kid04_part729),(kid04_part730),(kid04_part731),(kid04_part756),(kid04_part757),(kid04_part758),(kid04_part759),(kid04_part760),(kid04_part761)])

theorem kid04_part665_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (kid04_part665) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid04_part666),(kid04_part667),(kid04_part668),(kid04_part669),(kid04_part670),(kid04_part671),(kid04_part696),(kid04_part697),(kid04_part698),(kid04_part699),(kid04_part700),(kid04_part701),(kid04_part726),(kid04_part727),(kid04_part728),(kid04_part729),(kid04_part730),(kid04_part731),(kid04_part756),(kid04_part757),(kid04_part758),(kid04_part759),(kid04_part760),(kid04_part761)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part666_checked

  · exact kid04_part696_checked

  · exact kid04_part726_checked

  · exact kid04_part756_checked

  · exact kid04_part667_checked

  · exact kid04_part697_checked

  · exact kid04_part727_checked

  · exact kid04_part757_checked

  · exact kid04_part668_checked

  · exact kid04_part698_checked

  · exact kid04_part728_checked

  · exact kid04_part758_checked

  · exact kid04_part669_checked

  · exact kid04_part699_checked

  · exact kid04_part729_checked

  · exact kid04_part759_checked

  · exact kid04_part670_checked

  · exact kid04_part700_checked

  · exact kid04_part730_checked

  · exact kid04_part760_checked

  · exact kid04_part671_checked

  · exact kid04_part701_checked

  · exact kid04_part731_checked

  · exact kid04_part761_checked

def kid04_part787 : Audit := .cycle 0 13 true (0)
theorem kid04_part787_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part787) = true := by rfl

def kid04_part789 : Audit := .cycle 0 15 true (-1)
theorem kid04_part789_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part789) = true := by rfl

def kid04_part790 : Audit := .cycle 0 38 true (-2)
theorem kid04_part790_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part790) = true := by rfl

def kid04_part791 : Audit := .cycle 12 1 false (0)
theorem kid04_part791_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part791) = true := by rfl

def kid04_part792 : Audit := .cycle 11 1 false (-1)
theorem kid04_part792_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part792) = true := by rfl

def kid04_part793 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.last 28 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 62 28 false (0),
.last 16 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 19 true (-1),
.cycle 0 32 true (-2),
.last 38 (5,true),
.last 38 (5,true),
.last 18 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 20 (5,true),
.last 16 (5,true),
.cycle 0 15 true (-1),
.cycle 0 30 true (-2),
.cycle 0 17 true (-1),
.last 15 (5,true),
.cycle 9 3 false (1)
])
theorem kid04_part793_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part793) = true := by rfl

def kid04_part794 : Audit := .split 28 (5,true) (byMove [
.cycle 1 53 false (3),
.cycle 128 47 true (-2),
.cycle 28 15 false (0),
.cycle 14 15 false (2),
.last 29 (4,false),
.cycle 1 29 false (3),
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 64, 2, 64],[34, 32, 16, 34, 32, 34, 64],80⟩,
.cycle 21 45 true (-3),
.last 30 (4,false),
.cycle 0 30 true (-3),
.last 123 (4,false),
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 64, 2, 64],[34, 32, 16, 34, 32, 34, 64],80⟩,
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 2, 64],[35, 32, 16, 35, 32, 1, 64],80⟩,
.cycle 7 23 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M120.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M120.never m hm),
.cycle 28 13 false (0),
.last 29 (4,false),
.far true 1 ⟨0,[0, 0],[32, 34, 42, 8, 64, 2, 64],[34, 32, 16, 34, 32, 32, 64],80⟩,
.cycle 1 39 false (3),
.cycle 1 41 false (3),
.cycle 13 59 true (-4),
.cycle 1 43 false (5),
.cycle 27 2 true (0),
.cycle 1 35 false (3)
])
theorem kid04_part794_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part794) = true := by rfl

def kid04_part795 : Audit := .cycle 0 13 true (0)
theorem kid04_part795_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part795) = true := by rfl

def kid04_part796 : Audit := .cycle 0 18 true (-1)
theorem kid04_part796_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part796) = true := by rfl

def kid04_part797 : Audit := .cycle 0 13 true (0)
theorem kid04_part797_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part797) = true := by rfl

def kid04_part798 : Audit := .cycle 11 1 false (1)
theorem kid04_part798_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part798) = true := by rfl

def kid04_part799 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 44 true (-2),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 15 1 false (3),
.cycle 0 13 true (0),
.cycle 0 17 true (0),
.last 12 (5,true),
.cycle 8 6 true (0),
.last 25 (5,true),
.cycle 0 26 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 28 true (-1),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid04_part799_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part799) = true := by rfl

def kid04_part800 : Audit := .cycle 0 15 true (0)
theorem kid04_part800_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part800) = true := by rfl

def kid04_part801 : Audit := .split 24 (5,true) (byMove [
.cycle 6 45 false (3),
.cycle 52 37 true (-4),
.cycle 78 1 false (-4),
.cycle 13 15 false (2),
.last 25 (4,false),
.cycle 1 25 false (3),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 2, 64],[35, 1, 16, 35, 32, 35, 64],80⟩,
.cycle 12 40 false (4),
.last 26 (4,false),
.cycle 0 26 true (-3),
.cycle 54 39 true (-4),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 2, 64],[35, 1, 16, 35, 32, 35, 64],80⟩,
.cycle 6 21 false (3),
.cycle 7 19 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M124.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M124.never m hm),
.cycle 75 1 false (-5),
.last 25 (4,false),
.cycle 70 71 true (-4),
.cycle 6 31 false (3),
.cycle 12 38 false (4),
.cycle 12 36 false (4),
.cycle 19 24 true (-1),
.cycle 23 2 true (0),
.cycle 12 40 false (4)
])
theorem kid04_part801_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part801) = true := by rfl

def kid04_part802 : Audit := .split 22 (5,true) (byMove [
.cycle 7 41 false (3),
.cycle 42 57 true (-5),
.cycle 7 32 false (3),
.cycle 12 15 false (2),
.last 23 (4,false),
.cycle 1 23 false (3),
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 64, 2, 64],[34, 2, 16, 34, 32, 34, 64],80⟩,
.cycle 41 54 false (1),
.last 24 (4,false),
.cycle 0 24 true (-3),
.cycle 44 65 true (-5),
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 64, 2, 64],[34, 2, 16, 34, 32, 34, 64],80⟩,
.cycle 7 37 false (3),
.cycle 7 17 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M127.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M127.never m hm),
.cycle 7 30 false (3),
.last 23 (4,false),
.cycle 138 86 false (-4),
.cycle 7 27 false (3),
.cycle 7 19 false (3),
.cycle 39 52 false (1),
.cycle 17 22 true (-1),
.cycle 21 2 true (0),
.cycle 7 21 false (3)
])
theorem kid04_part802_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part802) = true := by rfl

def kid04_part803 : Audit := .split 16 (4,false) (byMove [
.cycle 0 21 true (-1),
.cycle 1 32 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.last 34 (5,true),
.cycle 13 4 true (0),
.cycle 0 24 true (-1),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 0 23 true (-1),
.cycle 0 21 true (-1),
.cycle 13 4 false (2),
.last 28 (5,true),
.cycle 11 6 true (-1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 9 16 false (2),
.cycle 7 24 false (3),
.last 20 (5,true),
.cycle 0 19 true (-1),
.cycle 0 26 true (-1),
.last 19 (5,true),
.cycle 9 8 true (-1)
])
theorem kid04_part803_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part803) = true := by rfl

def kid04_part804 : Audit := .cycle 11 1 false (-1)
theorem kid04_part804_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part804) = true := by rfl

def kid04_part805 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 34 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.proven (BB6.Agent11Raw39B1RCPumps.M128.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M128.never m hm),
.cycle 0 15 true (-1),
.cycle 10 2 true (-1),
.cycle 15 1 false (1),
.cycle 0 32 true (-1),
.cycle 0 36 true (-2),
.last 12 (5,true),
.last 30 (5,true),
.last 44 (5,true),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.far false 9 ⟨0,[0, 6, 3, 7, 1, 8, 3, 3, 7, 6, 4, 4, 5, 2, 8, 3, 7, 7],[137438953472, 274877906944, 8, 0, 16777216, 8589934592, 8796093022208, 17592186044416, 2097152, 137438953472, 18014398526521344, 35184372088832, 562949953421312, 1125899906842624, 512, 67108864, 18014398509481984, 18014407101513728, 524288, 1048576, 2097152, 18041199106981888, 18300271549743104, 20266206915198976, 137438953472, 274877906944, 35184372088832, 18032265574481920, 18014398509744128, 18049582881570816, 33554432, 67108864, 134217728, 18023332041981952, 16777216, 512, 8192, 16384, 8589934592, 274878955520, 18014398509481984, 8589934592, 524288, 1048576, 2251799813685248, 18041199106981888, 18295873486454784, 20266206915198976, 8796093022208, 17592186044416, 35184372088832, 18041199106981888, 18018796573032448, 18014398511579136, 18014398509481984],[274877906944, 274877906944, 137438953472, 1, 16777216, 18014398509481984, 17592186044416, 18014398509481984, 18014398509481984, 262144, 18014398526521344, 18014398509481984, 1125899906842624, 18014398509481984, 18014398509481984, 64, 18014398509481984, 18014398509481984, 1048576, 18032265574481920, 18023332041981952, 262144, 18300271549743104, 18014398509481984, 274877906944, 274877906944, 137438953472, 4398046511104, 18014398509744128, 18014398509481984, 67108864, 18014398509481984, 18014398509481984, 16777216, 16777216, 18014398509481984, 16384, 18014673388437504, 18014535948959744, 1073741824, 18014398509481984, 18014398509481984, 1048576, 18014673388437504, 18014535948959744, 281474976710656, 18295873486454784, 18014398509481984, 17592186044416, 18031990696574976, 18023194603028480, 4398046511104, 18018796573032448, 18014398509481984, 18014398509481984],36028608023608802⟩,
.cycle 0 15 true (-1),
.proven (BB6.Agent11Raw39B1RCPumps.M130.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M130.never m hm),
.last 22 (5,true),
.cycle 8 7 false (2),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid04_part805_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part805) = true := by rfl

def kid04_part806 : Audit := .split 17 (5,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 21 true (-2),
.cycle 11 15 false (2),
.cycle 17 15 false (2),
.last 18 (4,false),
.cycle 1 18 false (3),
.cycle 0 30 true (-2),
.cycle 0 23 true (-2),
.last 19 (4,false),
.cycle 0 19 true (-2),
.cycle 0 23 true (-2),
.cycle 0 32 true (-2),
.cycle 11 16 false (2),
.cycle 7 12 false (3),
.cycle 0 32 true (-2),
.cycle 11 13 false (2),
.last 18 (4,false),
.cycle 0 34 true (-2),
.cycle 2 17 true (-2),
.cycle 16 2 true (1),
.cycle 0 24 true (-2),
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 64, 2, 64],[34, 32, 16, 34, 32, 34, 64],80⟩,
.cycle 17 2 true (1),
.cycle 16 4 true (1)
])
theorem kid04_part806_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part806) = true := by rfl

def kid04_part807 : Audit := .cycle 0 13 true (0)
theorem kid04_part807_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part807) = true := by rfl

def kid04_part808 : Audit := .split 14 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 1 45 false (4),
.cycle 0 27 true (0),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 0 20 true (-1),
.cycle 0 29 true (0),
.cycle 27 11 false (3),
.cycle 23 17 true (0),
.cycle 0 29 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 0 31 true (-2),
.cycle 2 14 true (0),
.cycle 1 15 true (0),
.cycle 0 21 true (-2),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 1 17 true (0)
])
theorem kid04_part808_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part808) = true := by rfl

def kid04_part809 : Audit := .cycle 0 13 true (0)
theorem kid04_part809_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part809) = true := by rfl

def kid04_part810 : Audit := .cycle 0 20 true (-1)
theorem kid04_part810_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part810) = true := by rfl

def kid04_part811 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 10 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.last 21 (5,true),
.last 12 (5,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.last 57 (5,true),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.last 12 (5,true),
.last 25 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 0 20 true (-1),
.cycle 0 24 true (-2),
.last 12 (5,true),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid04_part811_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part811) = true := by rfl

def kid04_part812 : Audit := .cycle 9 2 true (0)
theorem kid04_part812_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part812) = true := by rfl

def kid04_part788 : Audit := .split 10 (1,true) (byMove [(kid04_part789),(kid04_part790),(kid04_part791),(kid04_part792),(kid04_part793),(kid04_part794),(kid04_part795),(kid04_part796),(kid04_part797),(kid04_part798),(kid04_part799),(kid04_part800),(kid04_part801),(kid04_part802),(kid04_part803),(kid04_part804),(kid04_part805),(kid04_part806),(kid04_part807),(kid04_part808),(kid04_part809),(kid04_part810),(kid04_part811),(kid04_part812)])

theorem kid04_part788_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part788) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part789),(kid04_part790),(kid04_part791),(kid04_part792),(kid04_part793),(kid04_part794),(kid04_part795),(kid04_part796),(kid04_part797),(kid04_part798),(kid04_part799),(kid04_part800),(kid04_part801),(kid04_part802),(kid04_part803),(kid04_part804),(kid04_part805),(kid04_part806),(kid04_part807),(kid04_part808),(kid04_part809),(kid04_part810),(kid04_part811),(kid04_part812)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part789_checked

  · exact kid04_part795_checked

  · exact kid04_part801_checked

  · exact kid04_part807_checked

  · exact kid04_part790_checked

  · exact kid04_part796_checked

  · exact kid04_part802_checked

  · exact kid04_part808_checked

  · exact kid04_part791_checked

  · exact kid04_part797_checked

  · exact kid04_part803_checked

  · exact kid04_part809_checked

  · exact kid04_part792_checked

  · exact kid04_part798_checked

  · exact kid04_part804_checked

  · exact kid04_part810_checked

  · exact kid04_part793_checked

  · exact kid04_part799_checked

  · exact kid04_part805_checked

  · exact kid04_part811_checked

  · exact kid04_part794_checked

  · exact kid04_part800_checked

  · exact kid04_part806_checked

  · exact kid04_part812_checked

def kid04_part813 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.split 16 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 19 (1,true),
.cycle 19 1 false (-1),
.cycle 27 1 false (1),
.last 17 (1,true),
.cycle 0 19 true (-1),
.cycle 0 18 true (-1),
.cycle 20 1 false (0),
.cycle 20 1 false (2),
.last 18 (1,true),
.cycle 22 1 false (-2),
.cycle 29 1 false (1),
.cycle 17 1 false (-1),
.cycle 23 1 false (-1),
.cycle 19 1 false (-1),
.cycle 2 16 true (-1),
.last 17 (1,true),
.cycle 21 1 false (-1),
.cycle 0 18 true (-1),
.cycle 15 2 true (0),
.cycle 23 1 false (-1)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 17 1 false (1),
.cycle 14 1 false (0),
.split 13 (1,true) (byMove [
.cycle 24 1 false (-2),
.cycle 25 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 19 true (-2),
.cycle 17 1 false (-3),
.last 14 (5,true),
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 24 1 false (-2),
.cycle 22 1 false (-2),
.last 24 (5,true),
.cycle 24 1 false (-2),
.cycle 19 1 false (-3),
.cycle 20 1 false (-4),
.cycle 10 4 false (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (-3),
.last 14 (5,true),
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 2 12 false (3),
.cycle 0 19 true (-2),
.last 18 (5,true),
.cycle 19 1 false (-3)
]),
.cycle 17 1 false (-3),
.split 18 (5,true) (byMove [
.cycle 14 5 false (2),
.cycle 0 22 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 23 (1,true),
.cycle 21 1 false (-1),
.cycle 29 1 false (1),
.last 19 (1,true),
.cycle 0 23 true (-2),
.cycle 0 20 true (-2),
.cycle 22 1 false (0),
.cycle 22 1 false (2),
.last 20 (1,true),
.cycle 24 1 false (-2),
.cycle 31 1 false (1),
.cycle 19 1 false (-1),
.cycle 27 1 false (-1),
.cycle 21 1 false (-1),
.cycle 2 18 true (-2),
.last 19 (1,true),
.cycle 23 1 false (-1),
.last 37 (1,true),
.cycle 17 2 true (0),
.cycle 25 1 false (-1)
]),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.split 16 (5,true) (byMove [
.cycle 0 20 true (-1),
.last 17 (1,true),
.cycle 10 7 false (2),
.last 19 (1,true),
.cycle 20 1 false (-2),
.cycle 20 1 false (-2),
.cycle 35 1 false (-1),
.last 17 (1,true),
.cycle 0 38 true (-1),
.cycle 0 18 true (-1),
.cycle 8 9 false (2),
.cycle 29 1 false (-1),
.cycle 22 1 false (-2),
.last 17 (1,true),
.last 20 (1,true),
.cycle 23 1 false (-1),
.cycle 20 1 false (-2),
.cycle 20 1 false (-2),
.cycle 30 1 false (-2),
.last 17 (1,true),
.cycle 24 1 false (-2),
.cycle 0 18 true (-1),
.cycle 15 2 true (0),
.cycle 28 1 false (-2)
]),
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 0 17 true (-1),
.split 15 (5,true) (byMove [
.cycle 0 19 true (-1),
.last 16 (1,true),
.cycle 20 1 false (-2),
.last 18 (1,true),
.cycle 25 1 false (-3),
.cycle 20 1 false (-2),
.cycle 0 42 true (-2),
.last 16 (1,true),
.cycle 17 1 true (1),
.cycle 0 17 true (-1),
.cycle 22 1 false (-2),
.cycle 3 17 false (3),
.last 21 (1,true),
.last 16 (1,true),
.cycle 20 1 false (-2),
.cycle 5 11 false (3),
.cycle 16 3 false (0),
.cycle 20 1 false (-2),
.cycle 0 46 true (-2),
.last 16 (1,true),
.cycle 26 1 false (-2),
.cycle 0 17 true (-1),
.cycle 14 2 true (1),
.cycle 32 1 false (-2)
]),
.cycle 9 3 false (1)
])
theorem kid04_part813_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part813) = true := by rfl

def kid04_part814 : Audit := .split 12 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 24 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 0 15 true (0),
.cycle 24 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 true (0),
.cycle 16 1 false (0),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 14 1 true (0),
.cycle 0 17 true (0)
]),
.cycle 0 14 true (0),
.cycle 15 1 false (-1),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.last 14 (4,false),
.cycle 15 1 false (1),
.cycle 11 3 false (2),
.cycle 18 1 false (-2),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 0 16 true (0)
]),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 14 true (0),
.cycle 30 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 13 1 true (3),
.cycle 22 1 false (0),
.cycle 11 3 true (1),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.cycle 9 5 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 27 true (0),
.cycle 32 1 false (0),
.cycle 13 1 true (3),
.cycle 0 16 true (0)
]),
.cycle 25 1 false (1),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.split 14 (4,false) (byMove [
.cycle 0 19 true (-1),
.cycle 24 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 11 4 true (0),
.cycle 19 1 false (-1),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 10 6 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.last 18 (5,true),
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.last 17 (5,true),
.cycle 9 6 true (0)
]),
.cycle 23 1 false (1),
.cycle 15 1 false (-1),
.split 13 (5,true) (byMove [
.cycle 13 5 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 15 1 false (-1),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 16 1 false (0),
.cycle 16 1 false (2),
.cycle 11 3 false (2),
.cycle 18 1 false (-2),
.cycle 25 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 15 1 false (-1),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 13 2 true (1),
.cycle 0 17 true (0)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 29 true (0),
.split 13 (4,false) (byMove [
.cycle 2 13 true (0),
.cycle 12 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 0 28 true (0),
.cycle 13 15 true (1),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.cycle 0 31 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 17 1 false (-1),
.cycle 0 29 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 30 true (0),
.cycle 13 1 true (3),
.cycle 0 16 true (0)
]),
.cycle 0 15 true (0)
])
theorem kid04_part814_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part814) = true := by rfl

def kid04_part816 : Audit := .split 18 (1,true) (byMove [
.last 56 (5,true),
.cycle 2 29 false (3),
.last 32 (5,true),
.cycle 0 20 true (-3),
.cycle 2 21 false (3),
.last 19 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M132.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M132.never m hm),
.cycle 10 26 true (-3),
.cycle 10 16 true (-3),
.last 54 (5,true),
.last 31 (5,true),
.last 58 (5,true),
.cycle 2 23 false (3),
.last 25 (5,true),
.last 48 (5,true),
.last 59 (5,true),
.cycle 2 21 false (3),
.last 19 (5,true),
.last 30 (5,true),
.last 29 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M133.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M133.never m hm),
.cycle 10 28 true (-3),
.proven (BB6.Agent11Raw39B1RCPumps.M134.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M134.never m hm),
.last 21 (5,true)
])
theorem kid04_part816_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part816) = true := by rfl

def kid04_part817 : Audit := .cycle 10 10 false (0)
theorem kid04_part817_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part817) = true := by rfl

def kid04_part818 : Audit := .cycle 14 1 false (-2)
theorem kid04_part818_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part818) = true := by rfl

def kid04_part819 : Audit := .cycle 13 1 false (-3)
theorem kid04_part819_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part819) = true := by rfl

def kid04_part820 : Audit := .cycle 12 1 false (-2)
theorem kid04_part820_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part820) = true := by rfl

def kid04_part821 : Audit := .cycle 11 2 false (-1)
theorem kid04_part821_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part821) = true := by rfl

def kid04_part822 : Audit := .split 14 (1,true) (byMove [
.cycle 10 12 true (-2),
.cycle 10 13 false (0),
.cycle 0 21 true (-2),
.last 20 (5,true),
.cycle 10 5 false (0),
.last 15 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 2, 3, 3, 3],[128, 256, 8, 385, 1, 128, 8192, 16384, 8, 256, 1, 128, 524288, 1048576, 32768, 385, 4096, 17301504, 524288, 1048576, 2097152, 18612224, 262144, 17301504, 16777216],[256, 1, 128, 1, 1, 16777216, 16384, 1, 128, 1, 16777216, 16777216, 1048576, 4096, 17301504, 4096, 17039360, 16777216, 1048576, 262144, 17301504, 262144, 17039360, 16777216, 16777216],33501248⟩,
.cycle 7 9 false (3),
.cycle 0 17 true (-2),
.cycle 10 10 true (-2),
.cycle 0 29 true (-2),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719607808, 1, 128, 524288, 1048576, 32768, 256, 4096, 128, 128, 256, 8, 128, 1, 128, 2147483648, 4294967296, 134217728, 256, 16777216, 68719476736, 2147483648, 4294967296, 8589934592, 128, 1073741824, 2147483648, 2147483648, 4294967296, 8589934592, 109521797120, 1073741824, 70866960384, 68719476736],[256, 32, 128, 1, 131072, 68719476736, 1048576, 131072, 128, 4096, 68719476736, 68719476736, 256, 32, 128, 1, 131072, 68719476736, 4294967296, 536870912, 68719476736, 16777216, 68719476736, 68719476736, 4294967296, 34359738368, 2147483648, 1073741824, 68719476736, 68719476736, 4294967296, 34359738368, 70866960384, 1073741824, 103079215104, 68719476736, 68719476736],137301344332⟩,
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 true (-2),
.cycle 0 19 true (-2),
.cycle 10 5 false (0),
.last 15 (5,true),
.last 28 (5,true),
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 4 11 false (3),
.last 42 (5,true),
.last 17 (5,true)
])
theorem kid04_part822_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part822) = true := by rfl

def kid04_part823 : Audit := .cycle 10 5 false (0)
theorem kid04_part823_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part823) = true := by rfl

def kid04_part824 : Audit := .split 16 (1,true) (byMove [
.cycle 0 29 true (-2),
.cycle 0 30 true (-2),
.cycle 20 1 false (2),
.cycle 0 18 true (-2),
.cycle 0 22 true (-2),
.last 17 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 393, 4, 8, 8192, 16384, 8, 392, 4, 136, 524288, 1048576, 512, 256, 256, 16777216, 524288, 1048576, 2097152, 20725760, 1048576, 19398656, 16777216],[256, 1, 8, 1, 1, 16777216, 16384, 1, 136, 1, 16777216, 16777216, 1048576, 64, 16777216, 64, 16777216, 16777216, 1048576, 262144, 19398656, 262144, 17039360, 16777216, 16777216],33435712⟩,
.cycle 0 29 true (-2),
.cycle 10 14 true (-2),
.cycle 0 27 true (-2),
.cycle 8 25 true (-2),
.cycle 10 16 true (-2),
.cycle 0 24 true (-2),
.cycle 10 10 true (-2),
.cycle 0 21 true (-2),
.cycle 0 30 true (-2),
.cycle 0 34 true (-2),
.last 17 (5,true),
.last 28 (5,true),
.last 27 (5,true),
.cycle 2 15 true (-2),
.cycle 0 31 true (-2),
.cycle 17 19 true (-1),
.last 19 (5,true)
])
theorem kid04_part824_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part824) = true := by rfl

def kid04_part825 : Audit := .cycle 13 1 false (-1)
theorem kid04_part825_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part825) = true := by rfl

def kid04_part826 : Audit := .cycle 10 4 true (-2)
theorem kid04_part826_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part826) = true := by rfl

def kid04_part827 : Audit := .cycle 11 2 true (-2)
theorem kid04_part827_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part827) = true := by rfl

def kid04_part828 : Audit := .split 14 (1,true) (byMove [
.cycle 10 12 false (0),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.last 20 (5,true),
.cycle 10 5 false (0),
.last 15 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 4096, 128, 524288, 1048576, 32768, 67109120, 128, 128, 128, 256, 134217728, 77562155392, 1073741824, 1048576, 33554432, 67108864, 8589934592, 256, 68719476736, 68719476736, 33554432, 67108864, 134217728, 77562155392, 77562155392, 77562155392, 33554432, 67108864, 134217728, 128, 16777216, 68719476736, 68719476736],[256, 1, 128, 1, 4096, 68719476736, 1048576, 4096, 128, 4096, 68719476736, 68719476736, 256, 16777216, 1048576, 16777216, 4096, 68719476736, 67108864, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 16777216, 77562155392, 16777216, 77562155392, 68719476736, 67108864, 16777216, 68719476736, 16777216, 68719476736, 68719476736, 68719476736],128847831874⟩,
.cycle 7 9 false (3),
.cycle 10 16 true (-3),
.cycle 10 10 false (0),
.last 21 (5,true),
.cycle 10 9 false (0),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.last 71 (5,true),
.cycle 10 5 false (0),
.last 15 (5,true),
.last 30 (5,true),
.last 18 (5,true),
.last 33 (5,true),
.cycle 4 11 false (3),
.last 19 (5,true),
.last 17 (5,true)
])
theorem kid04_part828_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part828) = true := by rfl

def kid04_part829 : Audit := .cycle 10 5 false (0)
theorem kid04_part829_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part829) = true := by rfl

def kid04_part830 : Audit := .split 16 (1,true) (byMove [
.cycle 10 14 true (-3),
.cycle 10 15 false (0),
.proven (BB6.Agent11Raw39B1RCPumps.M139.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M139.never m hm),
.last 22 (5,true),
.cycle 10 7 false (0),
.last 17 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 385, 1, 128, 8192, 16384, 8, 384, 1, 128, 524288, 1048576, 512, 256, 1, 16777216, 524288, 1048576, 2097152, 18628608, 17039360, 17301504, 16777216],[256, 1, 128, 1, 1, 16777216, 16384, 1, 128, 1, 16777216, 16777216, 1048576, 64, 16777216, 64, 16777216, 16777216, 1048576, 262144, 17301504, 262144, 17039360, 16777216, 16777216],33435712⟩,
.cycle 7 11 false (3),
.cycle 0 19 true (-3),
.cycle 10 12 true (-3),
.cycle 35 25 true (0),
.cycle 12 8 true (-3),
.cycle 10 9 false (0),
.cycle 10 10 false (0),
.cycle 12 6 true (-3),
.cycle 42 15 true (2),
.cycle 10 7 false (0),
.last 17 (5,true),
.last 30 (5,true),
.last 20 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1075855745, 1, 2097280, 8192, 16384, 8, 256, 16385, 2097280, 33554432, 67108864, 2097152, 256, 16385, 1073741824, 8192, 16384, 8, 2097280, 1, 2097280, 33554432, 67108864, 134217728, 1325416448, 1157627904, 1241513984, 1073741824],[256, 256, 2097280, 1, 16385, 1073741824, 16384, 16384, 2097280, 1, 1073741824, 1073741824, 67108864, 67108864, 1073741824, 262144, 1073741824, 1073741824, 16384, 16384, 2097280, 1, 1073741824, 1073741824, 67108864, 67108864, 1241513984, 16777216, 1157627904, 1073741824, 1073741824],2132194126⟩,
.cycle 4 13 false (3),
.cycle 10 9 false (1),
.last 19 (5,true)
])
theorem kid04_part830_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part830) = true := by rfl

def kid04_part831 : Audit := .cycle 13 1 false (-3)
theorem kid04_part831_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part831) = true := by rfl

def kid04_part832 : Audit := .cycle 12 1 false (-2)
theorem kid04_part832_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part832) = true := by rfl

def kid04_part833 : Audit := .cycle 11 2 false (-1)
theorem kid04_part833_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part833) = true := by rfl

def kid04_part834 : Audit := .split 14 (1,true) (byMove [
.cycle 2 14 false (3),
.cycle 10 14 false (0),
.cycle 10 6 false (0),
.last 20 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 32 (5,true),
.last 20 (5,true),
.cycle 0 17 true (-2),
.cycle 3 12 false (3),
.last 28 (5,true),
.last 32 (5,true),
.last 18 (5,true),
.cycle 10 9 false (0),
.cycle 10 6 false (0),
.cycle 0 19 true (-2),
.last 16 (5,true),
.last 15 (5,true),
.last 28 (5,true),
.last 18 (5,true),
.cycle 0 17 true (-2),
.last 22 (5,true),
.last 26 (5,true),
.last 17 (5,true)
])
theorem kid04_part834_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part834) = true := by rfl

def kid04_part835 : Audit := .split 16 (5,true) (byMove [
.cycle 13 5 false (0),
.last 45 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 1 54 false (5),
.cycle 10 14 true (-2),
.last 17 (1,true),
.cycle 1 18 false (3),
.cycle 0 24 true (-2),
.cycle 10 7 false (0),
.cycle 0 23 true (-2),
.last 18 (1,true),
.cycle 10 9 false (0),
.cycle 10 16 true (-3),
.cycle 17 1 false (-3),
.last 18 (1,true),
.cycle 11 6 false (0),
.cycle 2 16 false (3),
.last 17 (1,true),
.cycle 10 8 false (0),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 1048576, 524288, 1048576, 32768, 67109120, 524288, 1048576, 128, 256, 134217728, 77562118272, 128, 67108864, 33554432, 67108864, 8589934592, 256, 33554432, 128, 33554432, 67108864, 134217728, 77562118272, 33554432, 77562118272, 33554432, 67108864, 134217728, 1048576, 33554432, 67108864, 68719476736],[256, 68719476736, 1048576, 1, 128, 512, 1048576, 68719476736, 1048576, 4096, 4096, 2097152, 256, 68719476736, 67108864, 16777216, 128, 512, 67108864, 68719476736, 128, 1073741824, 1073741824, 134217728, 67108864, 68719476736, 77562118272, 16777216, 77562118272, 134217728, 67108864, 68719476736, 67108864, 16777216, 68719476736, 134217728, 68719476736],128839509826⟩,
.cycle 15 2 true (-2),
.cycle 15 4 true (-2)
])
theorem kid04_part835_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part835) = true := by rfl

def kid04_part836 : Audit := .split 16 (1,true) (byMove [
.cycle 0 29 true (-2),
.cycle 0 30 true (-2),
.cycle 0 30 true (-2),
.cycle 0 18 true (-2),
.cycle 0 22 true (-2),
.last 17 (5,true),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[8388608, 1099511627776, 35184372088832, 32768, 1099511627776, 16, 281475521972224, 281492970277888, 281493104496128, 134217728, 281492970277888, 1024, 8388608, 131072, 0, 35184372088832, 131072, 1099511627776, 8388608, 536872960, 0, 134217728, 536872960, 17179869184, 281475521972224, 281492970277888, 281493104496128, 512, 281492970277888, 268435456, 281474976710656, 0, 512, 2097152, 0, 1024, 281474976710656, 0, 134217728, 2097152, 0, 268435456, 0, 8388608, 0, 134217728, 8388608, 268435456, 281474976710656],[1099511627776, 17179869184, 16, 17179869184, 131072, 281474976710656, 281492970277888, 281492970277888, 1024, 281492970277888, 536870912, 281474976710656, 131072, 0, 1099511627776, 0, 140737488355328, 281474976710656, 536872960, 0, 17179869184, 0, 536870912, 281474976710656, 281492970277888, 281492970277888, 268435456, 281492970277888, 2048, 281474976710656, 0, 17179869184, 1024, 17179869184, 8388608, 281474976710656, 0, 17179869184, 268435456, 17179869184, 8388608, 281474976710656, 8388608, 1099511627776, 268435456, 1099511627776, 536870912, 281474976710656, 281474976710656],424516568747456⟩,
.cycle 0 29 true (-2),
.cycle 10 14 true (-2),
.cycle 0 27 true (-2),
.cycle 0 29 true (-2),
.cycle 2 17 true (-2),
.cycle 0 24 true (-2),
.cycle 7 12 false (3),
.cycle 0 21 true (-2),
.cycle 0 30 true (-2),
.cycle 0 34 true (-2),
.last 17 (5,true),
.last 28 (5,true),
.last 27 (5,true),
.cycle 2 15 true (-2),
.cycle 0 31 true (-2),
.last 27 (5,true),
.last 19 (5,true)
])
theorem kid04_part836_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part836) = true := by rfl

def kid04_part837 : Audit := .cycle 10 7 false (0)
theorem kid04_part837_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part837) = true := by rfl

def kid04_part838 : Audit := .split 15 (5,true) (byMove [
.last 20 (1,true),
.last 16 (1,true),
.cycle 10 13 false (0),
.last 18 (1,true),
.cycle 10 6 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 0, 16, 64],64⟩,
.cycle 0 19 true (-2),
.last 16 (1,true),
.cycle 23 1 true (1),
.last 18 (1,true),
.cycle 8 8 false (2),
.cycle 24 1 true (2),
.cycle 10 8 false (0),
.last 16 (1,true),
.cycle 12 5 false (0),
.cycle 10 9 false (0),
.cycle 10 6 false (0),
.cycle 11 6 false (0),
.cycle 0 19 true (-2),
.last 16 (1,true),
.cycle 10 10 false (0),
.last 18 (1,true),
.cycle 14 2 true (-1),
.cycle 14 4 true (-1)
])
theorem kid04_part838_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part838) = true := by rfl

def kid04_part839 : Audit := .cycle 9 4 false (1)
theorem kid04_part839_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part839) = true := by rfl

def kid04_part815 : Audit := .split 12 (4,false) (byMove [(kid04_part816),(kid04_part817),(kid04_part818),(kid04_part819),(kid04_part820),(kid04_part821),(kid04_part822),(kid04_part823),(kid04_part824),(kid04_part825),(kid04_part826),(kid04_part827),(kid04_part828),(kid04_part829),(kid04_part830),(kid04_part831),(kid04_part832),(kid04_part833),(kid04_part834),(kid04_part835),(kid04_part836),(kid04_part837),(kid04_part838),(kid04_part839)])

theorem kid04_part815_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part815) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 12 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid04_part816),(kid04_part817),(kid04_part818),(kid04_part819),(kid04_part820),(kid04_part821),(kid04_part822),(kid04_part823),(kid04_part824),(kid04_part825),(kid04_part826),(kid04_part827),(kid04_part828),(kid04_part829),(kid04_part830),(kid04_part831),(kid04_part832),(kid04_part833),(kid04_part834),(kid04_part835),(kid04_part836),(kid04_part837),(kid04_part838),(kid04_part839)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part816_checked

  · exact kid04_part822_checked

  · exact kid04_part828_checked

  · exact kid04_part834_checked

  · exact kid04_part817_checked

  · exact kid04_part823_checked

  · exact kid04_part829_checked

  · exact kid04_part835_checked

  · exact kid04_part818_checked

  · exact kid04_part824_checked

  · exact kid04_part830_checked

  · exact kid04_part836_checked

  · exact kid04_part819_checked

  · exact kid04_part825_checked

  · exact kid04_part831_checked

  · exact kid04_part837_checked

  · exact kid04_part820_checked

  · exact kid04_part826_checked

  · exact kid04_part832_checked

  · exact kid04_part838_checked

  · exact kid04_part821_checked

  · exact kid04_part827_checked

  · exact kid04_part833_checked

  · exact kid04_part839_checked

def kid04_part841 : Audit := .cycle 0 15 true (-1)
theorem kid04_part841_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part841) = true := by rfl

def kid04_part842 : Audit := .cycle 19 1 false (-1)
theorem kid04_part842_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part842) = true := by rfl

def kid04_part843 : Audit := .cycle 12 1 false (0)
theorem kid04_part843_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part843) = true := by rfl

def kid04_part844 : Audit := .cycle 11 1 false (-1)
theorem kid04_part844_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part844) = true := by rfl

def kid04_part845 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 19 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 12 1 false (0),
.last 13 (1,true),
.cycle 15 1 false (-3),
.last 23 (1,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 18 1 false (-2),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.cycle 23 1 false (-3),
.cycle 9 3 false (1)
])
theorem kid04_part845_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part845) = true := by rfl

def kid04_part846 : Audit := .cycle 11 1 false (-1)
theorem kid04_part846_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part846) = true := by rfl

def kid04_part847 : Audit := .split 12 (1,true) (byMove [
.cycle 21 1 false (1),
.cycle 22 1 false (0),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 37 1 false (3),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 14 (4,false),
.cycle 22 1 false (2),
.cycle 14 1 false (0),
.cycle 22 1 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 39 1 false (3),
.last 13 (4,false),
.cycle 0 15 true (0)
])
theorem kid04_part847_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part847) = true := by rfl

def kid04_part848 : Audit := .cycle 14 1 false (0)
theorem kid04_part848_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part848) = true := by rfl

def kid04_part849 : Audit := .cycle 0 13 true (0)
theorem kid04_part849_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part849) = true := by rfl

def kid04_part850 : Audit := .cycle 11 1 false (1)
theorem kid04_part850_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part850) = true := by rfl

def kid04_part851 : Audit := .split 11 (4,false) (byMove [
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 20 1 false (2),
.last 12 (1,true),
.cycle 15 1 false (3),
.cycle 0 13 true (0),
.cycle 13 1 false (1),
.cycle 14 1 false (4),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 15 1 false (1),
.cycle 12 3 true (2)
])
theorem kid04_part851_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part851) = true := by rfl

def kid04_part852 : Audit := .cycle 11 1 false (1)
theorem kid04_part852_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part852) = true := by rfl

def kid04_part853 : Audit := .split 12 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 22 1 false (-2),
.last 14 (4,false),
.cycle 0 25 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 15 true (-1),
.cycle 7 7 false (3),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.last 13 (4,false),
.cycle 9 5 false (1),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (4,false),
.cycle 0 17 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 80 1 false (-4),
.cycle 20 1 false (-2),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 13 (4,false),
.cycle 18 1 false (-2)
])
theorem kid04_part853_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part853) = true := by rfl

def kid04_part854 : Audit := .cycle 14 1 false (-2)
theorem kid04_part854_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part854) = true := by rfl

def kid04_part855 : Audit := .split 14 (1,true) (byMove [
.cycle 23 1 false (1),
.cycle 24 1 false (0),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 16 1 false (0),
.cycle 0 18 true (-1),
.cycle 0 15 true (-1),
.cycle 43 1 false (3),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.last 15 (4,false),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 26 1 false (2),
.cycle 28 1 false (0),
.last 26 (4,false),
.cycle 2 13 true (-1),
.cycle 45 1 false (3),
.last 15 (4,false),
.last 18 (4,false)
])
theorem kid04_part855_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part855) = true := by rfl

def kid04_part856 : Audit := .cycle 11 1 false (-1)
theorem kid04_part856_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part856) = true := by rfl

def kid04_part857 : Audit := .split 11 (4,false) (byMove [
.cycle 10 6 false (0),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 15 true (-1),
.last 12 (1,true),
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 13 1 false (-1),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 15 true (-1),
.last 12 (1,true),
.cycle 14 1 false (-2),
.last 14 (1,true),
.cycle 10 3 false (0),
.cycle 14 1 false (-2)
])
theorem kid04_part857_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part857) = true := by rfl

def kid04_part858 : Audit := .cycle 11 1 false (-1)
theorem kid04_part858_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part858) = true := by rfl

def kid04_part859 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 2 14 true (0),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 2 28 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 2 16 true (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 2 29 true (0),
.cycle 2 18 true (0),
.cycle 2 13 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 2 30 true (0),
.last 13 (4,false),
.cycle 0 15 true (0)
])
theorem kid04_part859_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part859) = true := by rfl

def kid04_part860 : Audit := .split 15 (1,true) (byMove [
.cycle 24 1 false (0),
.cycle 25 1 false (-1),
.last 17 (4,false),
.cycle 0 17 true (0),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 0 16 true (0),
.cycle 0 30 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.last 16 (4,false),
.cycle 1 18 true (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.last 17 (4,false),
.cycle 25 1 false (1),
.cycle 17 1 false (-1),
.cycle 14 2 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 0 32 true (0),
.last 16 (4,false),
.cycle 1 17 true (0)
])
theorem kid04_part860_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part860) = true := by rfl

def kid04_part861 : Audit := .cycle 0 13 true (0)
theorem kid04_part861_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part861) = true := by rfl

def kid04_part862 : Audit := .cycle 16 1 false (0)
theorem kid04_part862_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part862) = true := by rfl

def kid04_part863 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.last 25 (1,true),
.last 12 (1,true),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.cycle 12 4 true (2),
.cycle 15 1 false (-1),
.last 12 (1,true),
.last 17 (1,true),
.cycle 16 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 2 true (0),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 12 2 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part863_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part863) = true := by rfl

def kid04_part864 : Audit := .cycle 9 2 true (0)
theorem kid04_part864_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part864) = true := by rfl

def kid04_part840 : Audit := .split 10 (5,true) (byMove [(kid04_part841),(kid04_part842),(kid04_part843),(kid04_part844),(kid04_part845),(kid04_part846),(kid04_part847),(kid04_part848),(kid04_part849),(kid04_part850),(kid04_part851),(kid04_part852),(kid04_part853),(kid04_part854),(kid04_part855),(kid04_part856),(kid04_part857),(kid04_part858),(kid04_part859),(kid04_part860),(kid04_part861),(kid04_part862),(kid04_part863),(kid04_part864)])

theorem kid04_part840_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part840) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part841),(kid04_part842),(kid04_part843),(kid04_part844),(kid04_part845),(kid04_part846),(kid04_part847),(kid04_part848),(kid04_part849),(kid04_part850),(kid04_part851),(kid04_part852),(kid04_part853),(kid04_part854),(kid04_part855),(kid04_part856),(kid04_part857),(kid04_part858),(kid04_part859),(kid04_part860),(kid04_part861),(kid04_part862),(kid04_part863),(kid04_part864)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part841_checked

  · exact kid04_part847_checked

  · exact kid04_part853_checked

  · exact kid04_part859_checked

  · exact kid04_part842_checked

  · exact kid04_part848_checked

  · exact kid04_part854_checked

  · exact kid04_part860_checked

  · exact kid04_part843_checked

  · exact kid04_part849_checked

  · exact kid04_part855_checked

  · exact kid04_part861_checked

  · exact kid04_part844_checked

  · exact kid04_part850_checked

  · exact kid04_part856_checked

  · exact kid04_part862_checked

  · exact kid04_part845_checked

  · exact kid04_part851_checked

  · exact kid04_part857_checked

  · exact kid04_part863_checked

  · exact kid04_part846_checked

  · exact kid04_part852_checked

  · exact kid04_part858_checked

  · exact kid04_part864_checked

def kid04_part865 : Audit := .cycle 2 9 true (1)
theorem kid04_part865_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part865) = true := by rfl

def kid04_part866 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 1 12 true (1),
.cycle 14 6 false (0),
.cycle 12 6 false (0),
.cycle 0 24 true (-2),
.cycle 24 1 false (0),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (1),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 10 3 true (2),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 26 1 false (4),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1),
.split 16 (5,true) (byMove [
.cycle 14 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 19 7 false (1),
.cycle 22 7 false (3),
.cycle 17 7 false (1),
.last 18 (4,false),
.cycle 0 18 true (0),
.cycle 17 7 false (1),
.cycle 24 7 false (5),
.cycle 17 7 false (0),
.cycle 18 7 false (0),
.cycle 24 7 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 7 false (0),
.cycle 2 16 true (0),
.cycle 17 7 false (1),
.cycle 17 7 false (1),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.cycle 6 25 true (0)
]),
.split 14 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 16 5 false (1),
.cycle 21 5 false (3),
.cycle 15 5 false (1),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.cycle 23 5 false (5),
.cycle 17 5 false (-1),
.cycle 15 5 false (0),
.cycle 23 5 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 2 14 true (0),
.cycle 16 5 false (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 7 21 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 40 true (-2),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.cycle 14 6 false (0),
.cycle 12 6 false (0),
.cycle 0 35 true (-2),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (1),
.last 14 (5,true),
.last 33 (5,true),
.cycle 2 12 true (1),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid04_part866_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part866) = true := by rfl

def kid04_part867 : Audit := .split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (0),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (2),
.cycle 15 1 false (3),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 13 11 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 16 11 false (3),
.cycle 11 2 true (0),
.cycle 16 11 false (2)
]),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 26 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 16 1 false (2),
.cycle 15 1 false (3),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 11 2 true (0),
.cycle 27 1 false (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 41 1 false (7),
.split 19 (1,true) (byMove [
.cycle 12 13 false (1),
.cycle 12 14 false (1),
.cycle 16 4 false (0),
.cycle 0 21 false (3),
.cycle 14 6 false (0),
.last 20 (5,true),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 17 3 true (-2),
.cycle 12 31 true (-3),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.cycle 16 4 false (0),
.cycle 12 14 true (-2),
.cycle 14 6 false (0),
.last 20 (5,true),
.last 35 (5,true),
.last 34 (5,true),
.cycle 2 18 false (3),
.cycle 12 15 true (-2),
.last 24 (5,true),
.cycle 3 20 false (3)
]),
.split 12 (1,true) (byMove [
.last 17 (5,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 6 false (-1),
.cycle 0 16 true (-1),
.cycle 19 6 false (3),
.cycle 20 6 false (4),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 21 6 false (3),
.cycle 13 1 false (-1),
.cycle 13 6 false (-1),
.cycle 13 6 false (0),
.cycle 2 12 true (0),
.cycle 1 13 true (0),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
]),
.split 17 (1,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 32 true (-2),
.cycle 0 22 true (-2),
.cycle 0 19 true (-2),
.cycle 0 24 true (-2),
.last 18 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 1, 4, 8192, 16384, 8, 256, 1, 4, 33554432, 67108864, 2097152, 256, 1073741824, 1048576, 8192, 16384, 8, 16384, 1, 4, 33554432, 67108864, 134217728, 1327513993, 1327513993, 67108864, 1073741824],[256, 1, 128, 1, 128, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 1073741824, 1, 1073741824, 1073741824, 67108864, 16777216, 1327513993, 16777216, 1327513993, 1073741824, 1073741824],2140650350⟩,
.cycle 0 31 true (-2),
.last 35 (5,true),
.cycle 0 29 true (-2),
.cycle 0 21 true (-2),
.last 37 (5,true),
.cycle 0 26 true (-2),
.last 31 (5,true),
.cycle 12 6 true (-2),
.cycle 0 32 true (-2),
.cycle 12 8 true (-2),
.last 18 (5,true),
.last 32 (5,true),
.last 40 (5,true),
.cycle 2 16 true (-2),
.cycle 0 33 true (-2),
.last 30 (5,true),
.cycle 0 39 true (-2)
]),
.cycle 24 1 false (0),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 12 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 0 16 true (-1),
.cycle 21 3 false (2),
.last 13 (1,true),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 14 3 false (1),
.cycle 16 1 false (4),
.last 14 (1,true),
.cycle 16 3 false (-1),
.cycle 23 3 false (2),
.cycle 13 1 false (-1),
.cycle 13 3 false (-1),
.cycle 13 3 false (0),
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 15 3 false (0),
.cycle 0 14 true (0),
.cycle 12 2 true (0),
.cycle 0 31 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 0 27 true (0)
])
theorem kid04_part867_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part867) = true := by rfl

def kid04_part868 : Audit := .cycle 0 11 true (0)
theorem kid04_part868_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part868) = true := by rfl

def kid04_part869 : Audit := .cycle 8 2 true (1)
theorem kid04_part869_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part869) = true := by rfl

def kid04_part870 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 12 1 true (2),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 24 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 12 1 true (2)
]),
.cycle 11 1 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (1),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 26 1 false (4),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 14 5 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 13 1 true (3),
.cycle 16 7 false (0),
.cycle 13 8 false (1),
.last 20 (4,false),
.cycle 2 13 true (1),
.cycle 14 5 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 13 1 true (3)
]),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 10 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.cycle 14 5 false (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (1),
.last 12 (1,true),
.last 19 (1,true),
.cycle 2 12 true (1),
.cycle 14 2 true (2),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid04_part870_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part870) = true := by rfl

def kid04_part872 : Audit := .cycle 0 35 true (-2)
theorem kid04_part872_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part872) = true := by rfl

def kid04_part873 : Audit := .cycle 10 12 false (1)
theorem kid04_part873_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part873) = true := by rfl

def kid04_part874 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 22 (5,true),
.last 95 (5,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 12 8 true (-3),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.last 24 (5,true),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 22 (5,true),
.last 41 (5,true),
.cycle 10 12 false (1),
.last 107 (5,true),
.last 21 (5,true),
.cycle 9 9 false (1)
])
theorem kid04_part874_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part874) = true := by rfl

def kid04_part875 : Audit := .split 24 (5,true) (byMove [
.cycle 20 5 false (2),
.cycle 0 28 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 17 9 false (2),
.cycle 0 40 true (-2),
.cycle 26 1 false (0),
.last 26 (4,false),
.cycle 0 26 true (-2),
.cycle 0 33 true (-2),
.cycle 0 30 true (-2),
.cycle 0 31 true (-2),
.cycle 11 15 false (2),
.cycle 0 42 true (-2),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 0 35 true (-2),
.cycle 2 24 true (-2),
.cycle 0 27 true (-2),
.cycle 0 34 true (-2),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 8, 16, 33, 32, 33, 64],80⟩,
.cycle 23 2 true (0),
.cycle 22 6 true (0)
])
theorem kid04_part875_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part875) = true := by rfl

def kid04_part876 : Audit := .cycle 12 4 false (0)
theorem kid04_part876_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part876) = true := by rfl

def kid04_part877 : Audit := .split 16 (5,true) (byMove [
.cycle 39 5 false (-1),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 0 40 true (-2),
.cycle 11 7 false (1),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 50 true (-3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 0 41 true (-2),
.cycle 1 22 false (3),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.last 17 (4,false),
.cycle 9 8 false (1)
])
theorem kid04_part877_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part877) = true := by rfl

def kid04_part878 : Audit := .cycle 0 19 true (-2)
theorem kid04_part878_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part878) = true := by rfl

def kid04_part879 : Audit := .cycle 18 12 true (-1)
theorem kid04_part879_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part879) = true := by rfl

def kid04_part880 : Audit := .split 17 (4,false) (byMove [
.cycle 10 13 false (1),
.cycle 20 1 false (0),
.cycle 21 1 false (-3),
.cycle 0 23 true (-2),
.cycle 12 6 false (0),
.last 18 (5,true),
.last 22 (5,true),
.cycle 0 21 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 25 1 true (1),
.cycle 0 23 true (-2),
.cycle 10 8 false (1),
.cycle 11 11 false (1),
.cycle 10 19 false (1),
.cycle 10 14 true (-2),
.cycle 12 6 false (0),
.last 18 (5,true),
.last 22 (5,true),
.cycle 0 21 true (-2),
.cycle 2 16 false (3),
.cycle 0 23 true (-2),
.last 21 (5,true),
.last 22 (5,true)
])
theorem kid04_part880_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part880) = true := by rfl

def kid04_part881 : Audit := .cycle 0 29 true (-2)
theorem kid04_part881_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part881) = true := by rfl

def kid04_part882 : Audit := .cycle 8 8 false (2)
theorem kid04_part882_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part882) = true := by rfl

def kid04_part883 : Audit := .split 16 (5,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.last 17 (4,false),
.cycle 9 8 false (1),
.cycle 17 3 true (1),
.cycle 18 12 true (-1),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.last 17 (4,false),
.cycle 21 3 true (2),
.cycle 23 3 true (1),
.cycle 11 11 false (1),
.cycle 19 3 true (1),
.cycle 10 9 false (1),
.last 17 (4,false),
.cycle 9 8 false (1),
.cycle 17 3 true (1),
.cycle 21 3 true (1),
.cycle 0 19 true (-2),
.cycle 17 14 true (-1),
.last 17 (4,false),
.cycle 6 12 false (3)
])
theorem kid04_part883_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part883) = true := by rfl

def kid04_part884 : Audit := .cycle 10 6 false (1)
theorem kid04_part884_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part884) = true := by rfl

def kid04_part885 : Audit := .cycle 11 7 false (1)
theorem kid04_part885_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part885) = true := by rfl

def kid04_part886 : Audit := .split 17 (4,false) (byMove [
.last 48 (5,true),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 393, 4, 1, 8192, 16384, 8, 256, 4, 136, 33554432, 67108864, 2097152, 256, 1048576, 1073741824, 33554432, 67108864, 2097152, 393, 1048576, 1090781184, 33554432, 67108864, 134217728, 1325662208, 67108864, 1258553344, 1073741824],[256, 1, 8, 1, 257, 1073741824, 16384, 1, 136, 1, 1073741824, 1073741824, 67108864, 1, 1073741824, 262144, 1073741824, 1073741824, 67108864, 262144, 2097152, 262144, 1140850688, 1073741824, 67108864, 1090781184, 1241513984, 16777216, 1157890048, 1073741824, 1073741824],2140024896⟩,
.cycle 18 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 11 9 false (1),
.last 21 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M148.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M148.never m hm),
.cycle 10 10 false (1),
.last 20 (5,true),
.cycle 9 9 false (1)
])
theorem kid04_part886_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part886) = true := by rfl

def kid04_part887 : Audit := .cycle 10 7 false (1)
theorem kid04_part887_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part887) = true := by rfl

def kid04_part888 : Audit := .cycle 12 4 false (0)
theorem kid04_part888_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part888) = true := by rfl

def kid04_part889 : Audit := .split 16 (5,true) (byMove [
.cycle 16 5 false (-1),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 1, 64],[35, 32, 16, 35, 32, 2, 64],80⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.cycle 13 5 false (-1),
.last 18 (4,false),
.cycle 0 21 true (-2),
.cycle 12 5 false (0),
.cycle 23 5 true (1),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 2 20 false (3),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 16 2 true (-2),
.cycle 17 6 true (-1)
])
theorem kid04_part889_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part889) = true := by rfl

def kid04_part890 : Audit := .cycle 0 19 true (-2)
theorem kid04_part890_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part890) = true := by rfl

def kid04_part891 : Audit := .split 20 (5,true) (byMove [
.cycle 0 24 true (-2),
.cycle 16 39 false (3),
.cycle 58 1 false (-4),
.cycle 119 1 false (-1),
.last 23 (4,false),
.cycle 20 46 false (0),
.cycle 0 49 true (-2),
.cycle 0 48 true (-2),
.last 22 (4,false),
.cycle 0 22 true (-2),
.cycle 12 15 false (2),
.cycle 24 18 true (1),
.cycle 14 11 false (2),
.cycle 15 23 true (-1),
.cycle 11 10 false (2),
.cycle 5 16 false (3),
.last 23 (4,false),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 33, 16, 33, 32, 32, 64],80⟩,
.cycle 0 37 true (-2),
.cycle 16 19 true (0),
.cycle 21 22 false (1),
.cycle 16 26 true (-1),
.cycle 19 2 true (0),
.cycle 18 6 true (0)
])
theorem kid04_part891_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part891) = true := by rfl

def kid04_part892 : Audit := .split 18 (5,true) (byMove [
.cycle 16 5 false (0),
.cycle 20 30 true (-2),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.last 19 (4,false),
.cycle 2 58 false (5),
.cycle 10 14 true (-2),
.cycle 10 14 true (-2),
.last 20 (4,false),
.cycle 0 26 true (-2),
.cycle 12 7 false (0),
.cycle 0 25 true (-2),
.cycle 14 5 false (0),
.cycle 11 9 false (1),
.cycle 10 16 true (-3),
.cycle 19 1 false (-3),
.last 19 (4,false),
.cycle 13 6 false (0),
.cycle 2 18 false (3),
.cycle 2 18 false (3),
.cycle 11 8 false (1),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 33, 16, 33, 32, 33, 64],80⟩,
.cycle 17 2 true (-2),
.cycle 16 6 true (-2)
])
theorem kid04_part892_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part892) = true := by rfl

def kid04_part893 : Audit := .split 50 (5,true) (byMove [
.cycle 4 52 true (-2),
.cycle 0 77 true (-2),
.last 52 (4,false),
.cycle 0 74 true (-2),
.last 57 (4,false),
.cycle 46 48 false (4),
.cycle 16 37 true (0),
.cycle 18 48 true (2),
.last 52 (4,false),
.cycle 4 50 true (-2),
.cycle 51 21 false (3),
.cycle 13 39 true (-2),
.cycle 51 19 false (3),
.cycle 16 39 true (0),
.last 52 (4,false),
.cycle 116 1 false (-6),
.last 57 (4,false),
.cycle 46 30 false (5),
.cycle 16 37 true (0),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 33, 16, 33, 32, 33, 64],80⟩,
.cycle 51 18 false (3),
.cycle 77 36 false (4),
.cycle 49 2 true (2),
.cycle 46 6 true (2)
])
theorem kid04_part893_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part893) = true := by rfl

def kid04_part894 : Audit := .split 17 (5,true) (byMove [
.last 23 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.last 21 (4,false),
.cycle 12 6 false (0),
.last 22 (4,false),
.cycle 0 21 true (-2),
.last 19 (4,false),
.last 19 (4,false),
.last 21 (4,false),
.cycle 8 10 false (2),
.last 28 (4,false),
.cycle 10 8 false (1),
.cycle 11 11 false (1),
.last 19 (4,false),
.cycle 10 9 false (1),
.cycle 12 6 false (0),
.cycle 13 6 false (0),
.cycle 0 21 true (-2),
.last 19 (4,false),
.cycle 11 10 false (1),
.last 21 (4,false),
.cycle 16 2 true (-1),
.cycle 16 6 true (-1)
])
theorem kid04_part894_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part894) = true := by rfl

def kid04_part895 : Audit := .split 16 (5,true) (byMove [
.cycle 2 16 false (3),
.far true 1 ⟨0,[0, 0],[35, 35, 43, 8, 64, 1, 64],[35, 35, 16, 35, 32, 2, 64],80⟩,
.cycle 11 6 false (1),
.cycle 0 28 true (-2),
.last 19 (4,false),
.cycle 18 8 false (-2),
.cycle 17 40 true (1),
.cycle 9 17 false (2),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.last 17 (4,false),
.cycle 20 9 true (2),
.cycle 14 7 false (0),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.last 19 (4,false),
.cycle 13 6 false (0),
.cycle 0 40 true (-2),
.cycle 18 6 true (0),
.cycle 0 19 true (-2),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 33, 16, 33, 32, 33, 64],80⟩,
.last 17 (4,false),
.cycle 16 6 true (-1)
])
theorem kid04_part895_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part895) = true := by rfl

def kid04_part871 : Audit := .split 15 (1,true) (byMove [(kid04_part872),(kid04_part873),(kid04_part874),(kid04_part875),(kid04_part876),(kid04_part877),(kid04_part878),(kid04_part879),(kid04_part880),(kid04_part881),(kid04_part882),(kid04_part883),(kid04_part884),(kid04_part885),(kid04_part886),(kid04_part887),(kid04_part888),(kid04_part889),(kid04_part890),(kid04_part891),(kid04_part892),(kid04_part893),(kid04_part894),(kid04_part895)])

theorem kid04_part871_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part871) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid04_part872),(kid04_part873),(kid04_part874),(kid04_part875),(kid04_part876),(kid04_part877),(kid04_part878),(kid04_part879),(kid04_part880),(kid04_part881),(kid04_part882),(kid04_part883),(kid04_part884),(kid04_part885),(kid04_part886),(kid04_part887),(kid04_part888),(kid04_part889),(kid04_part890),(kid04_part891),(kid04_part892),(kid04_part893),(kid04_part894),(kid04_part895)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part872_checked

  · exact kid04_part878_checked

  · exact kid04_part884_checked

  · exact kid04_part890_checked

  · exact kid04_part873_checked

  · exact kid04_part879_checked

  · exact kid04_part885_checked

  · exact kid04_part891_checked

  · exact kid04_part874_checked

  · exact kid04_part880_checked

  · exact kid04_part886_checked

  · exact kid04_part892_checked

  · exact kid04_part875_checked

  · exact kid04_part881_checked

  · exact kid04_part887_checked

  · exact kid04_part893_checked

  · exact kid04_part876_checked

  · exact kid04_part882_checked

  · exact kid04_part888_checked

  · exact kid04_part894_checked

  · exact kid04_part877_checked

  · exact kid04_part883_checked

  · exact kid04_part889_checked

  · exact kid04_part895_checked

def kid04_part897 : Audit := .split 15 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 7 24 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 4 false (-2),
.cycle 0 19 true (-1),
.cycle 0 21 true (-1),
.last 17 (4,false),
.cycle 25 4 false (3),
.cycle 16 4 false (0),
.cycle 17 4 false (1),
.cycle 7 26 false (3),
.cycle 16 4 false (-1),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 4 false (-2),
.cycle 0 19 true (-1),
.cycle 23 4 false (1),
.cycle 16 4 false (0),
.cycle 12 16 true (-1),
.cycle 14 2 true (-1),
.cycle 0 50 true (-2)
])
theorem kid04_part897_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part897) = true := by rfl

def kid04_part898 : Audit := .cycle 0 34 true (-2)
theorem kid04_part898_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part898) = true := by rfl

def kid04_part899 : Audit := .cycle 12 1 false (0)
theorem kid04_part899_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part899) = true := by rfl

def kid04_part900 : Audit := .cycle 11 1 false (-1)
theorem kid04_part900_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part900) = true := by rfl

def kid04_part901 : Audit := .split 11 (4,false) (byMove [
.cycle 30 4 false (-2),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 14 4 false (0),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.cycle 13 4 false (1),
.cycle 12 4 false (0),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 16 4 false (0),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 15 (5,true),
.last 15 (5,true),
.cycle 0 34 true (-2),
.cycle 15 4 false (1),
.last 14 (5,true),
.cycle 9 3 false (1)
])
theorem kid04_part901_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part901) = true := by rfl

def kid04_part902 : Audit := .cycle 11 4 false (-1)
theorem kid04_part902_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part902) = true := by rfl

def kid04_part903 : Audit := .cycle 12 4 false (2)
theorem kid04_part903_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part903) = true := by rfl

def kid04_part904 : Audit := .cycle 19 4 false (5)
theorem kid04_part904_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part904) = true := by rfl

def kid04_part905 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 4 false (-1),
.cycle 21 4 false (3),
.cycle 13 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 14 4 false (2),
.cycle 13 4 false (1),
.cycle 0 17 true (-1),
.cycle 13 4 false (0),
.cycle 23 4 false (3),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 4 false (-1),
.cycle 0 31 true (0),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.last 15 (5,true),
.cycle 9 4 true (0)
])
theorem kid04_part905_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part905) = true := by rfl

def kid04_part906 : Audit := .cycle 18 4 false (4)
theorem kid04_part906_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part906) = true := by rfl

def kid04_part907 : Audit := .cycle 11 4 false (1)
theorem kid04_part907_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part907) = true := by rfl

def kid04_part908 : Audit := .split 11 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 4 false (0),
.cycle 18 4 false (4),
.cycle 13 4 false (3),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 12 4 false (2),
.cycle 13 4 false (3),
.cycle 23 4 false (1),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 4 false (0),
.cycle 2 11 true (0),
.cycle 11 6 true (1),
.cycle 12 4 false (2),
.cycle 0 13 true (0),
.cycle 11 2 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part908_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part908) = true := by rfl

def kid04_part909 : Audit := .cycle 14 4 false (0)
theorem kid04_part909_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part909) = true := by rfl

def kid04_part910 : Audit := .cycle 11 4 false (0)
theorem kid04_part910_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part910) = true := by rfl

def kid04_part911 : Audit := .cycle 14 4 false (2)
theorem kid04_part911_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part911) = true := by rfl

def kid04_part912 : Audit := .cycle 11 1 false (-1)
theorem kid04_part912_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part912) = true := by rfl

def kid04_part913 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.last 22 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 22 4 false (4),
.cycle 14 4 false (2),
.cycle 12 4 false (0),
.last 12 (5,true),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 15 (5,true),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 5 7 false (3),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid04_part913_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part913) = true := by rfl

def kid04_part914 : Audit := .cycle 11 4 false (-1)
theorem kid04_part914_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part914) = true := by rfl

def kid04_part915 : Audit := .split 14 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 4 false (-1),
.cycle 21 4 false (3),
.cycle 0 16 true (0),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 16 4 false (2),
.cycle 32 4 false (0),
.cycle 15 4 false (0),
.cycle 23 4 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 4 false (-1),
.cycle 2 14 true (0),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 2 17 true (0)
])
theorem kid04_part915_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part915) = true := by rfl

def kid04_part916 : Audit := .cycle 1 12 true (0)
theorem kid04_part916_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part916) = true := by rfl

def kid04_part917 : Audit := .cycle 11 4 false (1)
theorem kid04_part917_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part917) = true := by rfl

def kid04_part918 : Audit := .split 24 (5,true) (byMove [
.cycle 21 5 false (2),
.cycle 11 20 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 25 4 false (-1),
.cycle 0 28 true (0),
.cycle 29 4 false (3),
.last 26 (4,false),
.cycle 11 18 true (0),
.cycle 25 4 false (1),
.cycle 26 4 false (2),
.cycle 11 20 true (-1),
.cycle 25 4 false (0),
.cycle 0 30 true (-1),
.cycle 25 1 false (-1),
.last 25 (4,false),
.cycle 25 4 false (-1),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.cycle 25 4 false (1),
.cycle 11 18 true (0),
.cycle 23 2 true (0),
.cycle 9 17 true (0)
])
theorem kid04_part918_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part918) = true := by rfl

def kid04_part919 : Audit := .split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 38 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 14 4 false (2),
.last 17 (4,false),
.last 14 (4,false),
.cycle 20 4 false (4),
.cycle 13 4 false (1),
.cycle 15 4 false (3),
.cycle 18 4 false (0),
.cycle 13 4 false (0),
.cycle 16 4 false (2),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 2 16 true (0),
.last 17 (4,false),
.cycle 13 4 false (1),
.last 30 (4,false),
.cycle 11 2 true (0),
.cycle 13 5 true (1)
])
theorem kid04_part919_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part919) = true := by rfl

def kid04_part920 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 9 4 true (0),
.last 13 (4,false),
.cycle 0 19 true (0),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 28 true (0),
.cycle 9 21 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.cycle 7 8 true (0),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.last 13 (4,false),
.cycle 14 4 false (2),
.cycle 12 4 false (0),
.cycle 13 4 false (-1),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 15 4 false (1),
.cycle 0 13 true (0),
.cycle 11 2 true (1),
.cycle 12 3 true (2)
])
theorem kid04_part920_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part920) = true := by rfl

def kid04_part896 : Audit := .split 10 (1,true) (byMove [(kid04_part897),(kid04_part898),(kid04_part899),(kid04_part900),(kid04_part901),(kid04_part902),(kid04_part903),(kid04_part904),(kid04_part905),(kid04_part906),(kid04_part907),(kid04_part908),(kid04_part909),(kid04_part910),(kid04_part911),(kid04_part912),(kid04_part913),(kid04_part914),(kid04_part915),(kid04_part916),(kid04_part917),(kid04_part918),(kid04_part919),(kid04_part920)])

theorem kid04_part896_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part896) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid04_part897),(kid04_part898),(kid04_part899),(kid04_part900),(kid04_part901),(kid04_part902),(kid04_part903),(kid04_part904),(kid04_part905),(kid04_part906),(kid04_part907),(kid04_part908),(kid04_part909),(kid04_part910),(kid04_part911),(kid04_part912),(kid04_part913),(kid04_part914),(kid04_part915),(kid04_part916),(kid04_part917),(kid04_part918),(kid04_part919),(kid04_part920)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part897_checked

  · exact kid04_part903_checked

  · exact kid04_part909_checked

  · exact kid04_part915_checked

  · exact kid04_part898_checked

  · exact kid04_part904_checked

  · exact kid04_part910_checked

  · exact kid04_part916_checked

  · exact kid04_part899_checked

  · exact kid04_part905_checked

  · exact kid04_part911_checked

  · exact kid04_part917_checked

  · exact kid04_part900_checked

  · exact kid04_part906_checked

  · exact kid04_part912_checked

  · exact kid04_part918_checked

  · exact kid04_part901_checked

  · exact kid04_part907_checked

  · exact kid04_part913_checked

  · exact kid04_part919_checked

  · exact kid04_part902_checked

  · exact kid04_part908_checked

  · exact kid04_part914_checked

  · exact kid04_part920_checked

def kid04_part922 : Audit := .cycle 14 11 true (0)
theorem kid04_part922_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part922) = true := by rfl

def kid04_part923 : Audit := .cycle 24 11 true (0)
theorem kid04_part923_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part923) = true := by rfl

def kid04_part924 : Audit := .cycle 13 1 false (-1)
theorem kid04_part924_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part924) = true := by rfl

def kid04_part925 : Audit := .cycle 12 1 false (-2)
theorem kid04_part925_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part925) = true := by rfl

def kid04_part926 : Audit := .cycle 11 1 false (-1)
theorem kid04_part926_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part926) = true := by rfl

def kid04_part927 : Audit := .split 19 (5,true) (byMove [
.cycle 15 5 false (1),
.last 24 (1,true),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 11 9 false (1),
.last 24 (1,true),
.cycle 69 11 true (3),
.last 20 (1,true),
.cycle 13 35 true (-3),
.last 22 (1,true),
.cycle 77 11 true (3),
.cycle 21 11 true (0),
.last 21 (1,true),
.last 30 (1,true),
.cycle 73 11 true (3),
.cycle 20 1 false (-2),
.last 25 (1,true),
.cycle 109 11 true (3),
.cycle 13 29 true (-3),
.last 20 (1,true),
.cycle 101 11 true (3),
.last 22 (1,true),
.cycle 18 2 true (-1),
.cycle 28 11 true (0)
])
theorem kid04_part927_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part927) = true := by rfl

def kid04_part928 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 0 29 true (-2),
.last 20 (5,true),
.cycle 0 18 true (-1),
.cycle 0 21 true (-2),
.last 14 (5,true),
.cycle 14 11 true (1),
.cycle 16 11 true (2),
.cycle 0 16 true (-1),
.cycle 0 15 true (-1),
.cycle 8 6 true (-1),
.last 14 (5,true),
.cycle 0 23 true (-2),
.cycle 22 11 true (0),
.cycle 10 4 true (-1),
.cycle 14 11 true (-1),
.cycle 0 27 true (-2),
.last 14 (5,true),
.cycle 29 11 true (1),
.last 26 (5,true),
.last 16 (5,true),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part928_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part928) = true := by rfl

def kid04_part929 : Audit := .cycle 0 21 true (-2)
theorem kid04_part929_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part929) = true := by rfl

def kid04_part930 : Audit := .cycle 12 11 true (0)
theorem kid04_part930_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part930) = true := by rfl

def kid04_part931 : Audit := .cycle 12 1 false (0)
theorem kid04_part931_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part931) = true := by rfl

def kid04_part932 : Audit := .cycle 16 11 true (-1)
theorem kid04_part932_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part932) = true := by rfl

def kid04_part933 : Audit := .cycle 14 11 true (-1)
theorem kid04_part933_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part933) = true := by rfl

def kid04_part934 : Audit := .split 13 (1,true) (byMove [
.cycle 26 11 true (0),
.cycle 38 11 true (0),
.cycle 10 4 false (0),
.last 19 (5,true),
.cycle 30 11 true (0),
.last 14 (5,true),
.cycle 16 11 true (1),
.cycle 7 8 false (3),
.cycle 14 11 true (0),
.cycle 24 11 true (0),
.cycle 26 11 true (-1),
.cycle 16 11 true (-1),
.cycle 32 11 true (0),
.cycle 7 21 false (3),
.cycle 10 4 false (0),
.cycle 16 11 true (0),
.cycle 36 11 true (0),
.last 14 (5,true),
.last 27 (5,true),
.last 17 (5,true),
.cycle 14 11 true (0),
.cycle 4 10 false (3),
.last 18 (5,true),
.cycle 22 11 true (-1)
])
theorem kid04_part934_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part934) = true := by rfl

def kid04_part935 : Audit := .cycle 30 11 true (0)
theorem kid04_part935_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part935) = true := by rfl

def kid04_part936 : Audit := .split 15 (1,true) (byMove [
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.last 24 (5,true),
.cycle 0 20 true (-2),
.cycle 0 23 true (-2),
.last 16 (5,true),
.cycle 16 11 true (1),
.cycle 18 11 true (2),
.cycle 0 38 true (-2),
.cycle 0 17 true (-2),
.cycle 8 8 true (-2),
.last 16 (5,true),
.cycle 0 25 true (-2),
.cycle 24 11 true (0),
.cycle 10 6 true (-2),
.cycle 16 11 true (-1),
.cycle 0 29 true (-2),
.last 16 (5,true),
.cycle 31 11 true (1),
.last 28 (5,true),
.last 18 (5,true),
.cycle 12 23 true (-2),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid04_part936_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part936) = true := by rfl

def kid04_part937 : Audit := .cycle 12 1 false (-2)
theorem kid04_part937_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part937) = true := by rfl

def kid04_part938 : Audit := .cycle 11 1 false (-1)
theorem kid04_part938_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part938) = true := by rfl

def kid04_part939 : Audit := .cycle 16 11 true (0)
theorem kid04_part939_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part939) = true := by rfl

def kid04_part940 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-1),
.last 101 (5,true),
.last 77 (5,true),
.cycle 0 18 true (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 14 11 true (1),
.cycle 16 11 true (2),
.last 28 (5,true),
.cycle 0 15 true (-1),
.cycle 22 11 true (0),
.last 14 (5,true),
.last 17 (5,true),
.cycle 24 11 true (-1),
.cycle 20 11 true (0),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true),
.last 25 (5,true),
.last 26 (5,true),
.last 16 (5,true),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part940_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part940) = true := by rfl

def kid04_part941 : Audit := .split 15 (5,true) (byMove [
.cycle 12 5 false (1),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 5 false (1),
.last 20 (1,true),
.cycle 0 19 true (-1),
.last 16 (1,true),
.cycle 0 21 true (-1),
.last 18 (1,true),
.cycle 0 23 true (-2),
.cycle 17 11 true (0),
.last 17 (1,true),
.last 26 (1,true),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.last 17 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M155.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M155.never m hm),
.cycle 0 19 true (-1),
.last 16 (1,true),
.cycle 84 11 true (1),
.last 18 (1,true),
.cycle 14 2 true (-1),
.cycle 24 11 true (0)
])
theorem kid04_part941_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part941) = true := by rfl

def kid04_part942 : Audit := .cycle 12 11 true (0)
theorem kid04_part942_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part942) = true := by rfl

def kid04_part943 : Audit := .cycle 0 23 true (-2)
theorem kid04_part943_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part943) = true := by rfl

def kid04_part944 : Audit := .split 14 (5,true) (byMove [
.cycle 16 11 true (0),
.last 15 (1,true),
.cycle 38 11 true (0),
.last 17 (1,true),
.cycle 20 11 true (0),
.last 28 (1,true),
.cycle 6 9 false (3),
.last 15 (1,true),
.cycle 21 1 true (1),
.cycle 15 11 true (1),
.cycle 8 7 false (2),
.cycle 0 20 true (-1),
.cycle 22 11 true (0),
.last 15 (1,true),
.cycle 10 5 false (1),
.cycle 0 25 true (-2),
.cycle 26 11 true (0),
.cycle 26 11 true (0),
.cycle 34 11 true (0),
.last 15 (1,true),
.cycle 90 11 true (1),
.cycle 15 11 true (1),
.cycle 13 2 true (0),
.cycle 35 11 true (0)
])
theorem kid04_part944_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part944) = true := by rfl

def kid04_part945 : Audit := .cycle 9 3 false (1)
theorem kid04_part945_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part945) = true := by rfl

def kid04_part921 : Audit := .split 11 (4,false) (byMove [(kid04_part922),(kid04_part923),(kid04_part924),(kid04_part925),(kid04_part926),(kid04_part927),(kid04_part928),(kid04_part929),(kid04_part930),(kid04_part931),(kid04_part932),(kid04_part933),(kid04_part934),(kid04_part935),(kid04_part936),(kid04_part937),(kid04_part938),(kid04_part939),(kid04_part940),(kid04_part941),(kid04_part942),(kid04_part943),(kid04_part944),(kid04_part945)])

theorem kid04_part921_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part921) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some mv)) (byMove [(kid04_part922),(kid04_part923),(kid04_part924),(kid04_part925),(kid04_part926),(kid04_part927),(kid04_part928),(kid04_part929),(kid04_part930),(kid04_part931),(kid04_part932),(kid04_part933),(kid04_part934),(kid04_part935),(kid04_part936),(kid04_part937),(kid04_part938),(kid04_part939),(kid04_part940),(kid04_part941),(kid04_part942),(kid04_part943),(kid04_part944),(kid04_part945)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part922_checked

  · exact kid04_part928_checked

  · exact kid04_part934_checked

  · exact kid04_part940_checked

  · exact kid04_part923_checked

  · exact kid04_part929_checked

  · exact kid04_part935_checked

  · exact kid04_part941_checked

  · exact kid04_part924_checked

  · exact kid04_part930_checked

  · exact kid04_part936_checked

  · exact kid04_part942_checked

  · exact kid04_part925_checked

  · exact kid04_part931_checked

  · exact kid04_part937_checked

  · exact kid04_part943_checked

  · exact kid04_part926_checked

  · exact kid04_part932_checked

  · exact kid04_part938_checked

  · exact kid04_part944_checked

  · exact kid04_part927_checked

  · exact kid04_part933_checked

  · exact kid04_part939_checked

  · exact kid04_part945_checked

def kid04_part946 : Audit := .cycle 15 1 false (-1)
theorem kid04_part946_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part946) = true := by rfl

def kid04_part948 : Audit := .split 17 (5,true) (byMove [
.cycle 13 5 false (-1),
.last 22 (1,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.last 24 (1,true),
.cycle 11 7 false (-1),
.cycle 44 27 true (0),
.last 18 (1,true),
.cycle 0 20 false (3),
.last 20 (1,true),
.cycle 10 8 false (0),
.cycle 11 8 true (-3),
.last 19 (1,true),
.cycle 10 10 false (0),
.cycle 50 27 true (-2),
.cycle 18 1 false (-4),
.cycle 12 6 false (-1),
.cycle 11 7 false (-1),
.cycle 44 27 true (0),
.last 18 (1,true),
.cycle 10 9 false (0),
.last 20 (1,true),
.cycle 16 2 true (-3),
.cycle 24 5 true (0)
])
theorem kid04_part948_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part948) = true := by rfl

def kid04_part949 : Audit := .split 21 (1,true) (byMove [
.cycle 78 45 true (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M156.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M156.never m hm),
.cycle 23 1 false (-3),
.cycle 22 1 false (-4),
.last 122 (5,true),
.last 31 (5,true),
.cycle 88 47 false (6),
.cycle 39 42 true (-1),
.cycle 22 27 true (-2),
.cycle 22 1 false (-2),
.cycle 12 31 true (-3),
.cycle 11 11 false (1),
.last 112 (5,true),
.last 129 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M157.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M157.never m hm),
.cycle 22 1 false (-4),
.cycle 18 10 false (0),
.proven (BB6.Agent11Raw39B1RCPumps.M158.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M158.never m hm),
.last 46 (5,true),
.last 25 (5,true),
.cycle 14 27 true (-3),
.cycle 43 46 true (-1),
.cycle 20 2 true (-3),
.cycle 9 13 false (1)
])
theorem kid04_part949_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part949) = true := by rfl

def kid04_part950 : Audit := .cycle 14 1 false (-2)
theorem kid04_part950_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part950) = true := by rfl

def kid04_part951 : Audit := .cycle 13 1 false (-3)
theorem kid04_part951_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part951) = true := by rfl

def kid04_part952 : Audit := .cycle 12 1 false (-2)
theorem kid04_part952_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part952) = true := by rfl

def kid04_part953 : Audit := .cycle 11 2 false (-1)
theorem kid04_part953_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part953) = true := by rfl

def kid04_part954 : Audit := .cycle 10 5 false (0)
theorem kid04_part954_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part954) = true := by rfl

def kid04_part955 : Audit := .split 13 (1,true) (byMove [
.last 18 (5,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 7 false (0),
.cycle 11 3 false (-1),
.cycle 0 23 true (-2),
.cycle 15 12 true (1),
.cycle 0 27 true (-2),
.cycle 0 22 true (-2),
.cycle 10 4 true (-2),
.last 14 (5,true),
.cycle 10 8 false (0),
.cycle 10 6 false (0),
.cycle 0 27 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 true (-2),
.cycle 11 3 false (-1),
.last 17 (5,true),
.last 27 (5,true),
.cycle 10 5 false (0),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part955_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part955) = true := by rfl

def kid04_part956 : Audit := .cycle 0 26 true (-2)
theorem kid04_part956_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part956) = true := by rfl

def kid04_part957 : Audit := .cycle 0 23 true (-2)
theorem kid04_part957_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part957) = true := by rfl

def kid04_part958 : Audit := .cycle 10 3 false (0)
theorem kid04_part958_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part958) = true := by rfl

def kid04_part959 : Audit := .split 13 (5,true) (byMove [
.cycle 13 5 false (0),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 4 true (-2),
.cycle 11 3 false (-1),
.cycle 0 23 true (-2),
.last 14 (1,true),
.cycle 30 1 false (4),
.cycle 0 22 true (-2),
.cycle 10 4 true (-2),
.cycle 16 3 true (2),
.last 15 (1,true),
.cycle 10 6 false (0),
.cycle 0 27 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 true (-2),
.cycle 11 3 false (-1),
.cycle 0 21 true (-2),
.last 14 (1,true),
.cycle 10 5 false (0),
.cycle 5 9 false (3),
.cycle 13 2 true (-1),
.cycle 14 5 true (0)
])
theorem kid04_part959_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part959) = true := by rfl

def kid04_part960 : Audit := .split 14 (1,true) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M159.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M159.never m hm),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.cycle 0 28 true (-3),
.cycle 10 5 false (0),
.last 15 (5,true),
.cycle 6 9 false (3),
.cycle 16 14 true (0),
.cycle 10 9 false (0),
.proven (BB6.Agent11Raw39B1RCPumps.M160.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M160.never m hm),
.cycle 8 7 false (2),
.last 15 (5,true),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.cycle 10 8 false (0),
.cycle 10 5 false (0),
.last 15 (5,true),
.last 18 (5,true),
.last 29 (5,true),
.last 17 (5,true),
.last 21 (5,true),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid04_part960_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part960) = true := by rfl

def kid04_part961 : Audit := .cycle 10 5 false (0)
theorem kid04_part961_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part961) = true := by rfl

def kid04_part962 : Audit := .cycle 10 7 false (0)
theorem kid04_part962_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part962) = true := by rfl

def kid04_part963 : Audit := .cycle 13 1 false (-3)
theorem kid04_part963_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part963) = true := by rfl

def kid04_part964 : Audit := .cycle 12 1 false (-2)
theorem kid04_part964_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part964) = true := by rfl

def kid04_part965 : Audit := .cycle 11 2 false (-1)
theorem kid04_part965_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part965) = true := by rfl

def kid04_part966 : Audit := .split 16 (5,true) (byMove [
.cycle 14 5 false (0),
.last 21 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 19 (1,true),
.last 23 (1,true),
.cycle 20 14 true (1),
.last 17 (1,true),
.last 48 (1,true),
.last 19 (1,true),
.cycle 10 7 false (0),
.cycle 2 33 true (-2),
.last 18 (1,true),
.cycle 10 9 false (0),
.cycle 20 16 true (0),
.cycle 17 1 false (-3),
.cycle 12 5 false (0),
.cycle 11 6 false (0),
.cycle 0 81 true (-2),
.last 17 (1,true),
.cycle 10 8 false (0),
.last 19 (1,true),
.cycle 15 2 true (-2),
.cycle 22 5 true (0)
])
theorem kid04_part966_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part966) = true := by rfl

def kid04_part967 : Audit := .split 13 (1,true) (byMove [
.cycle 0 26 true (-2),
.cycle 10 12 false (0),
.last 27 (5,true),
.cycle 0 24 true (-2),
.cycle 10 4 false (0),
.last 14 (5,true),
.cycle 6 8 false (3),
.cycle 15 12 true (1),
.last 19 (5,true),
.cycle 0 22 true (-2),
.cycle 8 6 false (2),
.last 14 (5,true),
.cycle 10 6 false (0),
.cycle 10 7 false (0),
.last 19 (5,true),
.cycle 10 7 false (0),
.cycle 10 4 false (0),
.last 14 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid04_part967_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part967) = true := by rfl

def kid04_part968 : Audit := .cycle 10 4 false (0)
theorem kid04_part968_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part968) = true := by rfl

def kid04_part969 : Audit := .cycle 5 8 false (3)
theorem kid04_part969_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part969) = true := by rfl

def kid04_part970 : Audit := .split 14 (5,true) (byMove [
.cycle 13 5 false (-1),
.last 25 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 10 9 false (0),
.cycle 11 4 false (-1),
.cycle 10 7 false (0),
.last 15 (1,true),
.cycle 31 1 true (1),
.cycle 0 27 true (-2),
.cycle 10 5 false (0),
.cycle 17 5 true (1),
.last 16 (1,true),
.cycle 10 7 false (0),
.cycle 10 9 false (0),
.cycle 15 1 false (-3),
.cycle 12 3 false (-1),
.cycle 11 4 false (-1),
.cycle 0 87 true (-2),
.last 15 (1,true),
.cycle 10 6 false (0),
.cycle 5 10 false (3),
.cycle 13 2 true (-2),
.cycle 16 5 true (0)
])
theorem kid04_part970_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part970) = true := by rfl

def kid04_part971 : Audit := .split 13 (5,true) (byMove [
.cycle 0 26 true (-2),
.last 14 (1,true),
.cycle 9 7 false (1),
.last 16 (1,true),
.cycle 10 4 false (0),
.cycle 11 4 false (-1),
.cycle 6 8 false (3),
.last 14 (1,true),
.cycle 9 12 false (1),
.cycle 0 22 true (-2),
.cycle 8 6 false (2),
.cycle 16 3 true (2),
.cycle 10 6 false (0),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 10 7 false (0),
.cycle 10 4 false (0),
.cycle 11 4 false (-1),
.cycle 0 21 true (-2),
.last 14 (1,true),
.cycle 10 8 false (0),
.cycle 5 16 false (3),
.cycle 13 2 true (-1),
.cycle 14 5 true (0)
])
theorem kid04_part971_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part971) = true := by rfl

def kid04_part947 : Audit := .split 12 (4,false) (byMove [(kid04_part948),(kid04_part949),(kid04_part950),(kid04_part951),(kid04_part952),(kid04_part953),(kid04_part954),(kid04_part955),(kid04_part956),(kid04_part957),(kid04_part958),(kid04_part959),(kid04_part960),(kid04_part961),(kid04_part962),(kid04_part963),(kid04_part964),(kid04_part965),(kid04_part966),(kid04_part967),(kid04_part968),(kid04_part969),(kid04_part970),(kid04_part971)])

theorem kid04_part947_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part947) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 12 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid04_part948),(kid04_part949),(kid04_part950),(kid04_part951),(kid04_part952),(kid04_part953),(kid04_part954),(kid04_part955),(kid04_part956),(kid04_part957),(kid04_part958),(kid04_part959),(kid04_part960),(kid04_part961),(kid04_part962),(kid04_part963),(kid04_part964),(kid04_part965),(kid04_part966),(kid04_part967),(kid04_part968),(kid04_part969),(kid04_part970),(kid04_part971)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part948_checked

  · exact kid04_part954_checked

  · exact kid04_part960_checked

  · exact kid04_part966_checked

  · exact kid04_part949_checked

  · exact kid04_part955_checked

  · exact kid04_part961_checked

  · exact kid04_part967_checked

  · exact kid04_part950_checked

  · exact kid04_part956_checked

  · exact kid04_part962_checked

  · exact kid04_part968_checked

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

def kid04_part972 : Audit := .split 10 (5,true) (byMove [
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 29 1 false (-3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 12 1 false (0),
.last 13 (1,true),
.cycle 15 1 false (-3),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 13 (1,true),
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (0),
.split 11 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 13 1 false (1),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 25 3 true (3)
]),
.split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 1 18 true (0),
.cycle 0 15 true (0),
.cycle 18 1 false (0),
.cycle 17 1 true (1),
.cycle 9 4 true (0)
]),
.cycle 20 1 false (2),
.cycle 12 1 false (0),
.cycle 13 1 false (3),
.split 12 (1,true) (byMove [
.cycle 25 11 false (2),
.cycle 22 1 false (-2),
.last 14 (4,false),
.cycle 0 20 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 32, 64],[33, 33, 16, 33, 32, 1, 64],80⟩,
.last 14 (4,false),
.cycle 23 9 false (2),
.cycle 8 5 false (2),
.cycle 37 1 false (-3),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 20 1 false (-2),
.cycle 32 1 false (-2),
.cycle 10 5 false (1),
.cycle 28 1 false (-2),
.cycle 18 1 false (-2),
.cycle 10 7 false (1)
]),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 10 6 false (0),
.cycle 9 10 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.last 12 (1,true),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 10 5 false (1),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 5 7 false (3),
.cycle 10 3 false (0),
.cycle 14 1 false (-2)
]),
.cycle 11 1 false (-1),
.cycle 2 14 true (0),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 21 1 false (-1),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 13 1 false (-1),
.cycle 1 18 true (0),
.cycle 6 18 true (0),
.far true 1 ⟨0,[0, 0],[0, 32, 40, 8, 64, 32, 64],[32, 32, 16, 32, 32, 0, 64],80⟩,
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 13 (4,false),
.cycle 16 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 1 12 true (0)
]),
.cycle 13 1 false (-1),
.cycle 5 18 true (0),
.cycle 10 2 true (0),
.cycle 11 3 true (1)
])
theorem kid04_part972_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part972) = true := by rfl

def kid04_part973 : Audit := .cycle 2 9 true (1)
theorem kid04_part973_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part973) = true := by rfl

def kid04_part975 : Audit := .cycle 2 10 true (1)
theorem kid04_part975_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid04_part975) = true := by rfl

def kid04_part976 : Audit := .cycle 11 11 false (1)
theorem kid04_part976_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid04_part976) = true := by rfl

def kid04_part977 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 1 17 false (3),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 true (-2),
.cycle 1 17 false (3),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 13 4 false (0),
.last 30 (5,true),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 16 1 true (-2),
.last 30 (5,true)
])
theorem kid04_part977_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid04_part977) = true := by rfl

def kid04_part978 : Audit := .cycle 0 12 true (0)
theorem kid04_part978_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid04_part978) = true := by rfl

def kid04_part979 : Audit := .split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 11 5 false (1),
.cycle 20 3 false (2),
.last 14 (4,false),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.cycle 1 14 true (0),
.cycle 14 3 false (0),
.cycle 15 3 false (-1),
.cycle 22 3 false (2),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 2 12 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.cycle 1 14 true (0)
])
theorem kid04_part979_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid04_part979) = true := by rfl

def kid04_part980 : Audit := .split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.cycle 1 13 false (3),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 16 (4,false),
.cycle 1 13 false (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 1 12 true (1),
.cycle 16 3 false (0),
.cycle 17 6 false (-1),
.last 13 (4,false),
.cycle 24 1 false (0),
.last 16 (4,false),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 1 12 true (1)
])
theorem kid04_part980_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid04_part980) = true := by rfl

def kid04_part981 : Audit := .cycle 0 11 true (0)
theorem kid04_part981_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid04_part981) = true := by rfl

def kid04_part982 : Audit := .cycle 1 10 true (1)
theorem kid04_part982_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid04_part982) = true := by rfl

def kid04_part983 : Audit := .cycle 0 23 true (0)
theorem kid04_part983_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid04_part983) = true := by rfl

def kid04_part984 : Audit := .cycle 3 8 true (1)
theorem kid04_part984_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid04_part984) = true := by rfl

def kid04_part985 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 10 3 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
])
theorem kid04_part985_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid04_part985) = true := by rfl

def kid04_part986 : Audit := .cycle 1 11 true (1)
theorem kid04_part986_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid04_part986) = true := by rfl

def kid04_part987 : Audit := .split 14 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 12 5 false (2),
.cycle 20 5 false (3),
.cycle 17 5 false (1),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.cycle 1 16 true (0),
.cycle 16 5 false (0),
.cycle 16 5 false (0),
.cycle 22 5 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 2 14 true (0),
.cycle 15 5 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 1 16 true (0)
])
theorem kid04_part987_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid04_part987) = true := by rfl

def kid04_part988 : Audit := .cycle 11 6 false (1)
theorem kid04_part988_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid04_part988) = true := by rfl

def kid04_part989 : Audit := .split 16 (4,false) (byMove [
.last 58 (5,true),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 46 (5,true),
.cycle 14 4 true (-2),
.cycle 11 7 false (1),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.cycle 12 6 true (-2),
.cycle 13 4 true (-2),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.cycle 14 6 true (-3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 13 4 false (0),
.cycle 10 8 false (2),
.last 20 (5,true),
.cycle 0 25 true (-2),
.cycle 11 9 false (1),
.last 19 (5,true),
.cycle 9 8 false (2)
])
theorem kid04_part989_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid04_part989) = true := by rfl

def kid04_part990 : Audit := .cycle 2 11 true (1)
theorem kid04_part990_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid04_part990) = true := by rfl

def kid04_part991 : Audit := .split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 26 13 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 11 5 false (1),
.cycle 15 3 false (1),
.last 14 (4,false),
.last 14 (4,false),
.cycle 21 3 false (3),
.cycle 13 3 false (1),
.cycle 1 15 true (0),
.cycle 14 3 false (0),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 2 16 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 5 24 true (0),
.cycle 11 2 true (0),
.cycle 1 15 true (0)
])
theorem kid04_part991_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid04_part991) = true := by rfl

def kid04_part992 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.last 13 (4,false),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 0 17 true (-1),
.cycle 2 11 true (1),
.cycle 9 4 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.cycle 13 6 false (0),
.last 13 (4,false),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.cycle 11 2 true (1),
.cycle 1 13 true (1)
])
theorem kid04_part992_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid04_part992) = true := by rfl

def kid04_part993 : Audit := .cycle 0 11 true (0)
theorem kid04_part993_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid04_part993) = true := by rfl

def kid04_part994 : Audit := .cycle 1 10 true (1)
theorem kid04_part994_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid04_part994) = true := by rfl

def kid04_part995 : Audit := .cycle 2 9 true (1)
theorem kid04_part995_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid04_part995) = true := by rfl

def kid04_part996 : Audit := .cycle 2 12 true (1)
theorem kid04_part996_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid04_part996) = true := by rfl

def kid04_part997 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.last 15 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
])
theorem kid04_part997_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid04_part997) = true := by rfl

def kid04_part998 : Audit := .cycle 1 11 true (1)
theorem kid04_part998_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid04_part998) = true := by rfl

def kid04_part974 : Audit := .split 10 (1,true) (byMove [(kid04_part975),(kid04_part976),(kid04_part977),(kid04_part978),(kid04_part979),(kid04_part980),(kid04_part981),(kid04_part982),(kid04_part983),(kid04_part984),(kid04_part985),(kid04_part986),(kid04_part987),(kid04_part988),(kid04_part989),(kid04_part990),(kid04_part991),(kid04_part992),(kid04_part993),(kid04_part994),(kid04_part995),(kid04_part996),(kid04_part997),(kid04_part998)])

theorem kid04_part974_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part974) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid04_part975),(kid04_part976),(kid04_part977),(kid04_part978),(kid04_part979),(kid04_part980),(kid04_part981),(kid04_part982),(kid04_part983),(kid04_part984),(kid04_part985),(kid04_part986),(kid04_part987),(kid04_part988),(kid04_part989),(kid04_part990),(kid04_part991),(kid04_part992),(kid04_part993),(kid04_part994),(kid04_part995),(kid04_part996),(kid04_part997),(kid04_part998)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part975_checked

  · exact kid04_part981_checked

  · exact kid04_part987_checked

  · exact kid04_part993_checked

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

def kid04_part999 : Audit := .split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 20 3 false (0),
.last 15 (1,true),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 3 false (1),
.cycle 14 3 false (1),
.last 15 (1,true),
.cycle 15 3 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.last 15 (1,true),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.cycle 17 3 false (-1),
.cycle 9 5 false (2)
]),
.cycle 0 16 true (-1),
.cycle 19 3 false (3),
.split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 20 3 false (2),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.last 14 (4,false),
.cycle 20 3 false (4),
.cycle 17 3 false (1),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 22 3 false (4),
.last 14 (4,false),
.cycle 2 13 true (0)
]),
.split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 21 3 false (1),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 true (0),
.cycle 21 3 false (3),
.last 16 (1,true),
.cycle 16 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.cycle 14 1 true (0),
.cycle 2 14 true (0)
]),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.cycle 20 3 false (4),
.split 14 (1,true) (byMove [
.cycle 0 18 true (-1),
.cycle 22 3 false (0),
.last 16 (4,false),
.cycle 0 19 true (-1),
.cycle 15 3 false (-1),
.cycle 12 3 false (0),
.cycle 7 17 false (3),
.cycle 7 21 false (4),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 8 7 false (2),
.cycle 34 3 false (0),
.cycle 16 3 false (0),
.cycle 17 3 false (-1),
.last 16 (4,false),
.cycle 17 3 false (1),
.cycle 15 3 false (-1),
.cycle 12 3 false (0),
.cycle 28 3 false (0),
.cycle 25 11 false (3),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 18 3 false (0),
.cycle 10 7 false (2)
]),
.cycle 14 3 false (0),
.cycle 21 3 false (3),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 10 6 false (2),
.cycle 7 22 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 7 22 false (3),
.cycle 15 3 false (1),
.last 14 (1,true),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 10 5 false (2),
.last 14 (1,true),
.cycle 14 3 false (0),
.cycle 7 17 false (3),
.cycle 11 3 false (1),
.cycle 15 3 false (-1)
]),
.cycle 13 3 false (0),
.cycle 2 12 true (0),
.split 13 (1,true) (byMove [
.cycle 20 3 false (2),
.cycle 21 3 false (1),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 14 3 false (0),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.last 14 (4,false),
.cycle 7 16 true (0),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.last 15 (4,false),
.cycle 21 3 false (3),
.cycle 14 3 false (0),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 18 true (0),
.last 14 (4,false),
.cycle 2 13 true (0)
]),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (0),
.cycle 2 13 true (0)
])
theorem kid04_part999_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part999) = true := by rfl

def kid04_part1000 : Audit := .cycle 0 11 true (0)
theorem kid04_part1000_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part1000) = true := by rfl

def kid04_part1002 : Audit := .cycle 0 15 true (0)
theorem kid04_part1002_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1002) = true := by rfl

def kid04_part1003 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 0 44 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 15 true (0),
.cycle 0 22 true (-1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 0 19 true (0),
.cycle 58 43 true (-4),
.cycle 50 63 true (-5),
.last 18 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 0 25 true (-2),
.cycle 0 15 true (0),
.cycle 0 20 true (-1),
.cycle 0 15 true (0),
.cycle 0 24 true (-1),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid04_part1003_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1003) = true := by rfl

def kid04_part1004 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.cycle 20 1 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 21 1 false (1),
.cycle 28 1 false (0),
.last 15 (1,true),
.cycle 21 1 false (-3),
.cycle 22 1 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 18 1 false (-2),
.cycle 10 7 false (2),
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 0 19 true (-1),
.cycle 24 1 false (-2),
.cycle 21 1 false (-1)
])
theorem kid04_part1004_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1004) = true := by rfl

def kid04_part1005 : Audit := .split 14 (1,true) (byMove [
.cycle 26 1 false (0),
.cycle 27 1 false (-1),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 19 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 0 31 true (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.last 15 (4,false),
.last 16 (4,false),
.cycle 21 1 false (-1),
.cycle 22 1 false (-2),
.last 16 (4,false),
.cycle 27 1 false (1),
.cycle 19 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 0 33 true (0),
.last 15 (4,false),
.last 16 (4,false)
])
theorem kid04_part1005_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1005) = true := by rfl

def kid04_part1006 : Audit := .split 16 (4,false) (byMove [
.last 22 (1,true),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 4 false (-1),
.last 18 (1,true),
.cycle 12 7 false (0),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 12 6 true (-2),
.cycle 13 4 true (-2),
.last 18 (1,true),
.cycle 12 7 false (0),
.last 20 (1,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 13 4 false (0),
.last 18 (1,true),
.cycle 14 5 false (0),
.last 20 (1,true),
.cycle 12 9 false (0),
.cycle 10 8 false (2),
.cycle 9 8 false (2)
])
theorem kid04_part1006_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1006) = true := by rfl

def kid04_part1007 : Audit := .split 14 (4,false) (byMove [
.last 32 (1,true),
.last 15 (1,true),
.cycle 18 1 false (-2),
.last 25 (1,true),
.cycle 12 6 false (0),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 7 9 false (3),
.cycle 0 17 true (-1),
.last 28 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 0, 16, 64],64⟩,
.cycle 21 2 true (1),
.cycle 12 8 false (0),
.last 15 (1,true),
.last 20 (1,true),
.cycle 0 19 true (-1),
.cycle 12 6 false (0),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 10 7 false (2),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 0, 16, 64],64⟩,
.cycle 29 2 true (-3)
])
theorem kid04_part1007_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1007) = true := by rfl

def kid04_part1008 : Audit := .cycle 2 11 true (1)
theorem kid04_part1008_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1008) = true := by rfl

def kid04_part1009 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 13 (4,false),
.last 14 (4,false),
.cycle 17 9 false (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.last 14 (4,false)
])
theorem kid04_part1009_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1009) = true := by rfl

def kid04_part1010 : Audit := .split 13 (4,false) (byMove [
.cycle 0 27 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 19 1 false (-1),
.cycle 16 1 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 13 2 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 19 (1,true),
.cycle 28 1 false (0),
.cycle 19 1 false (-1),
.cycle 14 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 1 true (1),
.cycle 13 2 true (1)
])
theorem kid04_part1010_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1010) = true := by rfl

def kid04_part1011 : Audit := .cycle 0 13 true (0)
theorem kid04_part1011_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1011) = true := by rfl

def kid04_part1012 : Audit := .cycle 8 4 true (1)
theorem kid04_part1012_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1012) = true := by rfl

def kid04_part1013 : Audit := .split 14 (4,false) (byMove [
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 8 7 true (1),
.cycle 12 3 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 18 true (1),
.cycle 3 12 true (1),
.cycle 14 1 true (4),
.cycle 13 2 true (3),
.cycle 6 9 true (1),
.last 15 (1,true),
.last 20 (1,true),
.cycle 2 15 true (1),
.cycle 11 8 true (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 14 1 true (4),
.cycle 13 2 true (3)
])
theorem kid04_part1013_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1013) = true := by rfl

def kid04_part1014 : Audit := .split 19 (1,true) (byMove [
.cycle 0 41 true (-2),
.cycle 12 14 false (1),
.last 21 (4,false),
.cycle 0 35 true (-2),
.cycle 14 6 false (0),
.cycle 17 3 false (-1),
.cycle 0 23 true (-2),
.cycle 22 14 true (-1),
.last 21 (4,false),
.cycle 0 35 true (-2),
.cycle 8 12 false (2),
.last 32 (4,false),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.last 21 (4,false),
.cycle 12 9 false (1),
.cycle 14 6 false (0),
.cycle 17 3 false (-1),
.cycle 0 23 true (-2),
.cycle 16 11 false (2),
.cycle 16 5 false (0),
.cycle 59 23 false (3),
.cycle 10 10 false (2),
.cycle 16 7 false (0)
])
theorem kid04_part1014_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1014) = true := by rfl

def kid04_part1015 : Audit := .split 12 (1,true) (byMove [
.cycle 16 6 false (0),
.cycle 0 40 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 14 6 false (2),
.cycle 21 6 false (5),
.last 14 (4,false),
.cycle 20 6 false (4),
.cycle 13 6 false (1),
.cycle 13 6 false (1),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 16 6 false (2),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 6 false (0),
.cycle 15 6 false (1),
.cycle 1 14 true (0),
.cycle 13 6 false (1),
.cycle 27 6 false (1),
.cycle 13 6 false (1),
.cycle 11 2 true (0)
])
theorem kid04_part1015_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1015) = true := by rfl

def kid04_part1016 : Audit := .split 13 (4,false) (byMove [
.cycle 16 13 true (0),
.cycle 28 13 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 87 13 true (3),
.last 15 (1,true),
.cycle 0 25 true (-2),
.cycle 14 13 true (0),
.cycle 14 1 false (0),
.cycle 20 13 true (-1),
.cycle 18 13 true (-1),
.last 15 (1,true),
.cycle 36 13 true (0),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 20 13 true (0),
.last 15 (1,true),
.cycle 0 23 true (-2),
.cycle 14 13 true (0),
.cycle 0 27 true (-2),
.cycle 10 5 false (2),
.cycle 9 5 false (2)
])
theorem kid04_part1016_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1016) = true := by rfl

def kid04_part1017 : Audit := .cycle 19 1 false (-1)
theorem kid04_part1017_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1017) = true := by rfl

def kid04_part1018 : Audit := .split 16 (4,false) (byMove [
.cycle 14 6 false (0),
.last 27 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 4 false (-1),
.cycle 12 7 false (0),
.last 17 (1,true),
.cycle 0 32 true (-2),
.cycle 0 29 true (-2),
.cycle 12 5 false (0),
.cycle 15 2 true (-2),
.last 18 (1,true),
.cycle 12 7 false (0),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 13 4 false (0),
.cycle 14 5 false (0),
.last 17 (1,true),
.cycle 12 6 false (0),
.cycle 5 12 false (3),
.cycle 14 3 false (0),
.cycle 11 6 false (1)
])
theorem kid04_part1018_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1018) = true := by rfl

def kid04_part1019 : Audit := .cycle 12 3 false (0)
theorem kid04_part1019_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1019) = true := by rfl

def kid04_part1020 : Audit := .cycle 2 11 true (1)
theorem kid04_part1020_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1020) = true := by rfl

def kid04_part1021 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 13 5 false (1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 15 7 false (1),
.cycle 13 8 false (1),
.last 20 (4,false),
.cycle 2 13 true (1),
.cycle 13 5 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.last 14 (4,false)
])
theorem kid04_part1021_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1021) = true := by rfl

def kid04_part1022 : Audit := .cycle 13 5 false (1)
theorem kid04_part1022_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1022) = true := by rfl

def kid04_part1023 : Audit := .cycle 0 13 true (0)
theorem kid04_part1023_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1023) = true := by rfl

def kid04_part1024 : Audit := .cycle 10 2 true (1)
theorem kid04_part1024_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1024) = true := by rfl

def kid04_part1025 : Audit := .split 14 (4,false) (byMove [
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 10 6 true (1),
.cycle 0 16 true (0),
.cycle 10 5 true (1),
.cycle 12 3 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 18 true (1),
.cycle 3 12 true (1),
.cycle 14 1 true (4),
.cycle 13 2 true (3),
.cycle 10 7 true (1),
.last 15 (1,true),
.cycle 9 10 true (1),
.cycle 2 15 true (1),
.cycle 11 6 true (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 14 1 true (4),
.cycle 13 2 true (3)
])
theorem kid04_part1025_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1025) = true := by rfl

def kid04_part1001 : Audit := .split 11 (5,true) (byMove [(kid04_part1002),(kid04_part1003),(kid04_part1004),(kid04_part1005),(kid04_part1006),(kid04_part1007),(kid04_part1008),(kid04_part1009),(kid04_part1010),(kid04_part1011),(kid04_part1012),(kid04_part1013),(kid04_part1014),(kid04_part1015),(kid04_part1016),(kid04_part1017),(kid04_part1018),(kid04_part1019),(kid04_part1020),(kid04_part1021),(kid04_part1022),(kid04_part1023),(kid04_part1024),(kid04_part1025)])

theorem kid04_part1001_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part1001) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some mv)) (byMove [(kid04_part1002),(kid04_part1003),(kid04_part1004),(kid04_part1005),(kid04_part1006),(kid04_part1007),(kid04_part1008),(kid04_part1009),(kid04_part1010),(kid04_part1011),(kid04_part1012),(kid04_part1013),(kid04_part1014),(kid04_part1015),(kid04_part1016),(kid04_part1017),(kid04_part1018),(kid04_part1019),(kid04_part1020),(kid04_part1021),(kid04_part1022),(kid04_part1023),(kid04_part1024),(kid04_part1025)] mv))) = true

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

def kid04_part1027 : Audit := .cycle 2 10 true (1)
theorem kid04_part1027_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1027) = true := by rfl

def kid04_part1028 : Audit := .split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 16 (4,false),
.cycle 24 1 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 12 1 true (2),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 13 (4,false),
.cycle 24 1 false (0),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 12 1 true (2)
])
theorem kid04_part1028_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1028) = true := by rfl

def kid04_part1029 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 17 1 true (-3),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 true (-2),
.cycle 17 1 true (-1),
.last 18 (1,true),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 13 4 false (0),
.cycle 32 1 false (-2),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 16 1 true (-2),
.cycle 17 1 true (-1)
])
theorem kid04_part1029_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1029) = true := by rfl

def kid04_part1030 : Audit := .cycle 0 12 true (0)
theorem kid04_part1030_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1030) = true := by rfl

def kid04_part1031 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 21 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 19 3 false (-1),
.last 15 (1,true),
.cycle 16 3 false (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 3 false (1),
.cycle 14 3 false (1),
.last 15 (1,true),
.cycle 16 3 false (-2),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.last 15 (1,true),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 18 3 false (0),
.cycle 16 3 false (0),
.cycle 9 5 false (2)
])
theorem kid04_part1031_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1031) = true := by rfl

def kid04_part1032 : Audit := .cycle 13 1 true (-1)
theorem kid04_part1032_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1032) = true := by rfl

def kid04_part1033 : Audit := .cycle 0 11 true (0)
theorem kid04_part1033_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1033) = true := by rfl

def kid04_part1034 : Audit := .cycle 1 10 true (1)
theorem kid04_part1034_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1034) = true := by rfl

def kid04_part1035 : Audit := .cycle 0 23 true (0)
theorem kid04_part1035_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1035) = true := by rfl

def kid04_part1036 : Audit := .cycle 3 8 true (1)
theorem kid04_part1036_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1036) = true := by rfl

def kid04_part1037 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 15 5 false (2),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 13 (1,true),
.cycle 8 8 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 8 13 true (0),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
])
theorem kid04_part1037_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1037) = true := by rfl

def kid04_part1038 : Audit := .cycle 11 1 true (3)
theorem kid04_part1038_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1038) = true := by rfl

def kid04_part1039 : Audit := .split 16 (1,true) (byMove [
.cycle 0 20 true (-1),
.cycle 23 5 false (0),
.last 18 (4,false),
.cycle 0 21 true (-1),
.cycle 17 5 false (-1),
.cycle 14 3 false (0),
.cycle 6 21 false (3),
.cycle 6 27 false (4),
.last 18 (4,false),
.cycle 0 18 true (-1),
.cycle 8 9 false (2),
.cycle 20 1 true (2),
.cycle 17 5 false (0),
.cycle 19 5 false (-1),
.last 18 (4,false),
.cycle 18 5 false (1),
.cycle 17 5 false (-1),
.cycle 14 3 false (0),
.cycle 30 5 false (0),
.cycle 29 11 false (3),
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 18 5 false (0),
.cycle 10 7 false (2)
])
theorem kid04_part1039_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1039) = true := by rfl

def kid04_part1040 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.last 13 (4,false),
.cycle 0 16 true (0),
.last 16 (4,false),
.cycle 9 11 false (2),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 16 7 false (0),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 13 (4,false),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 16 3 false (-1),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 13 8 false (1),
.cycle 10 2 true (1)
])
theorem kid04_part1040_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1040) = true := by rfl

def kid04_part1041 : Audit := .split 16 (4,false) (byMove [
.last 22 (1,true),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.last 30 (1,true),
.last 18 (1,true),
.cycle 11 7 false (1),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 12 6 true (-2),
.cycle 13 4 true (-2),
.last 18 (1,true),
.cycle 11 7 false (1),
.last 20 (1,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 13 4 false (0),
.last 18 (1,true),
.cycle 11 18 true (-3),
.last 20 (1,true),
.cycle 11 9 false (1),
.cycle 14 5 false (0),
.cycle 9 8 false (2)
])
theorem kid04_part1041_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1041) = true := by rfl

def kid04_part1042 : Audit := .cycle 2 11 true (1)
theorem kid04_part1042_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1042) = true := by rfl

def kid04_part1043 : Audit := .split 13 (4,false) (byMove [
.cycle 11 6 false (1),
.cycle 8 14 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 9 6 false (2),
.cycle 16 3 false (0),
.last 14 (1,true),
.cycle 25 3 false (3),
.cycle 17 3 false (1),
.cycle 14 3 false (0),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 16 3 false (-2),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 11 5 false (1),
.last 14 (1,true),
.cycle 15 3 false (-1),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.cycle 14 3 false (0)
])
theorem kid04_part1043_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1043) = true := by rfl

def kid04_part1044 : Audit := .cycle 11 3 false (1)
theorem kid04_part1044_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1044) = true := by rfl

def kid04_part1045 : Audit := .cycle 0 11 true (0)
theorem kid04_part1045_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1045) = true := by rfl

def kid04_part1046 : Audit := .cycle 1 10 true (1)
theorem kid04_part1046_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1046) = true := by rfl

def kid04_part1047 : Audit := .cycle 2 9 true (1)
theorem kid04_part1047_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1047) = true := by rfl

def kid04_part1048 : Audit := .cycle 2 12 true (1)
theorem kid04_part1048_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1048) = true := by rfl

def kid04_part1049 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 12 2 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.cycle 14 2 true (1),
.last 12 (1,true),
.cycle 13 2 true (0),
.cycle 2 12 true (1),
.cycle 12 2 true (1),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
])
theorem kid04_part1049_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1049) = true := by rfl

def kid04_part1050 : Audit := .cycle 11 1 true (3)
theorem kid04_part1050_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1050) = true := by rfl

def kid04_part1026 : Audit := .split 10 (5,true) (byMove [(kid04_part1027),(kid04_part1028),(kid04_part1029),(kid04_part1030),(kid04_part1031),(kid04_part1032),(kid04_part1033),(kid04_part1034),(kid04_part1035),(kid04_part1036),(kid04_part1037),(kid04_part1038),(kid04_part1039),(kid04_part1040),(kid04_part1041),(kid04_part1042),(kid04_part1043),(kid04_part1044),(kid04_part1045),(kid04_part1046),(kid04_part1047),(kid04_part1048),(kid04_part1049),(kid04_part1050)])

theorem kid04_part1026_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part1026) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid04_part1027),(kid04_part1028),(kid04_part1029),(kid04_part1030),(kid04_part1031),(kid04_part1032),(kid04_part1033),(kid04_part1034),(kid04_part1035),(kid04_part1036),(kid04_part1037),(kid04_part1038),(kid04_part1039),(kid04_part1040),(kid04_part1041),(kid04_part1042),(kid04_part1043),(kid04_part1044),(kid04_part1045),(kid04_part1046),(kid04_part1047),(kid04_part1048),(kid04_part1049),(kid04_part1050)] mv))) = true

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

def kid04_part786 : Audit := .split 9 (5,false) (byMove [(kid04_part787),(kid04_part788),(kid04_part813),(kid04_part814),(kid04_part815),(kid04_part840),(kid04_part865),(kid04_part866),(kid04_part867),(kid04_part868),(kid04_part869),(kid04_part870),(kid04_part871),(kid04_part896),(kid04_part921),(kid04_part946),(kid04_part947),(kid04_part972),(kid04_part973),(kid04_part974),(kid04_part999),(kid04_part1000),(kid04_part1001),(kid04_part1026)])

theorem kid04_part786_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (kid04_part786) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid04_part787),(kid04_part788),(kid04_part813),(kid04_part814),(kid04_part815),(kid04_part840),(kid04_part865),(kid04_part866),(kid04_part867),(kid04_part868),(kid04_part869),(kid04_part870),(kid04_part871),(kid04_part896),(kid04_part921),(kid04_part946),(kid04_part947),(kid04_part972),(kid04_part973),(kid04_part974),(kid04_part999),(kid04_part1000),(kid04_part1001),(kid04_part1026)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part787_checked

  · exact kid04_part865_checked

  · exact kid04_part871_checked

  · exact kid04_part973_checked

  · exact kid04_part788_checked

  · exact kid04_part866_checked

  · exact kid04_part896_checked

  · exact kid04_part974_checked

  · exact kid04_part813_checked

  · exact kid04_part867_checked

  · exact kid04_part921_checked

  · exact kid04_part999_checked

  · exact kid04_part814_checked

  · exact kid04_part868_checked

  · exact kid04_part946_checked

  · exact kid04_part1000_checked

  · exact kid04_part815_checked

  · exact kid04_part869_checked

  · exact kid04_part947_checked

  · exact kid04_part1001_checked

  · exact kid04_part840_checked

  · exact kid04_part870_checked

  · exact kid04_part972_checked

  · exact kid04_part1026_checked

def kid04_part1051 : Audit := .cycle 0 9 true (0)
theorem kid04_part1051_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,0⟩)) (kid04_part1051) = true := by rfl

def kid04_part1052 : Audit := .cycle 1 8 true (1)
theorem kid04_part1052_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,1⟩)) (kid04_part1052) = true := by rfl

def kid04_part1053 : Audit := .cycle 2 7 true (1)
theorem kid04_part1053_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,2⟩)) (kid04_part1053) = true := by rfl

def kid04_part1054 : Audit := .cycle 2 10 true (1)
theorem kid04_part1054_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,3⟩)) (kid04_part1054) = true := by rfl

def kid04_part1056 : Audit := .cycle 2 9 true (1)
theorem kid04_part1056_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part1056) = true := by rfl

def kid04_part1057 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 11 11 false (1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 26 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 12 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1),
.last 20 (5,true),
.cycle 12 6 false (0),
.last 33 (5,true),
.cycle 24 1 false (0),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (5,true),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 65 1 false (7),
.cycle 35 1 false (7),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 10 3 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
]),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 18 4 true (1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 26 1 false (-2),
.last 15 (5,true),
.cycle 12 12 false (1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 13 13 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 28 13 true (0),
.cycle 19 1 false (-1),
.last 17 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 13 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.last 15 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 13 13 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 13 13 false (1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
])
theorem kid04_part1057_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part1057) = true := by rfl

def kid04_part1058 : Audit := .cycle 15 1 false (-1)
theorem kid04_part1058_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part1058) = true := by rfl

def kid04_part1059 : Audit := .cycle 0 11 true (0)
theorem kid04_part1059_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part1059) = true := by rfl

def kid04_part1060 : Audit := .cycle 8 2 true (2)
theorem kid04_part1060_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part1060) = true := by rfl

def kid04_part1062 : Audit := .cycle 0 11 true (0)
theorem kid04_part1062_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1062) = true := by rfl

def kid04_part1063 : Audit := .cycle 1 10 true (1)
theorem kid04_part1063_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1063) = true := by rfl

def kid04_part1064 : Audit := .cycle 21 1 false (1)
theorem kid04_part1064_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1064) = true := by rfl

def kid04_part1065 : Audit := .cycle 23 1 false (1)
theorem kid04_part1065_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1065) = true := by rfl

def kid04_part1066 : Audit := .split 14 (5,false) (byMove [
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
.last 16 (1,true),
.cycle 11 7 false (1),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 18 false (2),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 11 4 false (1),
.cycle 14 1 true (-2)
])
theorem kid04_part1066_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1066) = true := by rfl

def kid04_part1067 : Audit := .split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 15 2 false (-1),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 27 false (3),
.cycle 24 1 false (0),
.cycle 17 2 false (-1),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 14 3 false (0),
.cycle 11 1 true (1)
])
theorem kid04_part1067_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1067) = true := by rfl

def kid04_part1068 : Audit := .cycle 0 11 true (0)
theorem kid04_part1068_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1068) = true := by rfl

def kid04_part1069 : Audit := .cycle 1 10 true (1)
theorem kid04_part1069_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1069) = true := by rfl

def kid04_part1070 : Audit := .cycle 35 1 false (7)
theorem kid04_part1070_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1070) = true := by rfl

def kid04_part1071 : Audit := .cycle 20 1 false (2)
theorem kid04_part1071_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1071) = true := by rfl

def kid04_part1072 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (1),
.cycle 26 1 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
])
theorem kid04_part1072_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1072) = true := by rfl

def kid04_part1073 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 2 false (1),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (3),
.cycle 35 1 false (7),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 21 2 false (1),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid04_part1073_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1073) = true := by rfl

def kid04_part1074 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 21 (5,false),
.cycle 0 14 true (0),
.cycle 18 5 false (1),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 21 (5,false),
.cycle 2 13 true (1),
.cycle 19 11 false (2),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 18 9 false (2),
.last 13 (5,false)
])
theorem kid04_part1074_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1074) = true := by rfl

def kid04_part1075 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 23 5 false (3),
.cycle 24 5 false (4),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.cycle 17 5 false (1),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 25 5 false (3),
.cycle 17 1 false (-1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 13 4 true (0),
.cycle 15 2 true (0)
])
theorem kid04_part1075_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1075) = true := by rfl

def kid04_part1076 : Audit := .cycle 0 13 true (0)
theorem kid04_part1076_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1076) = true := by rfl

def kid04_part1077 : Audit := .cycle 18 1 false (0)
theorem kid04_part1077_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1077) = true := by rfl

def kid04_part1078 : Audit := .split 14 (5,false) (byMove [
.last 20 (1,true),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 12 4 true (-2),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 18 (1,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 16 (1,true),
.cycle 17 4 true (-2),
.last 18 (1,true),
.cycle 11 9 false (1),
.cycle 11 4 false (1),
.cycle 16 4 true (-1)
])
theorem kid04_part1078_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1078) = true := by rfl

def kid04_part1079 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 15 2 false (-1),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 10 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 129 13 true (3),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 0, 16, 64],[4, 64, 0, 1, 16, 16, 64],64⟩,
.cycle 13 3 false (1)
])
theorem kid04_part1079_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1079) = true := by rfl

def kid04_part1080 : Audit := .cycle 0 11 true (0)
theorem kid04_part1080_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1080) = true := by rfl

def kid04_part1081 : Audit := .cycle 1 10 true (1)
theorem kid04_part1081_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1081) = true := by rfl

def kid04_part1082 : Audit := .cycle 2 9 true (1)
theorem kid04_part1082_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1082) = true := by rfl

def kid04_part1083 : Audit := .cycle 2 12 true (1)
theorem kid04_part1083_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1083) = true := by rfl

def kid04_part1084 : Audit := .cycle 9 2 true (2)
theorem kid04_part1084_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1084) = true := by rfl

def kid04_part1085 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 1 false (-2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 13 17 false (1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid04_part1085_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1085) = true := by rfl

def kid04_part1061 : Audit := .split 10 (5,true) (byMove [(kid04_part1062),(kid04_part1063),(kid04_part1064),(kid04_part1065),(kid04_part1066),(kid04_part1067),(kid04_part1068),(kid04_part1069),(kid04_part1070),(kid04_part1071),(kid04_part1072),(kid04_part1073),(kid04_part1074),(kid04_part1075),(kid04_part1076),(kid04_part1077),(kid04_part1078),(kid04_part1079),(kid04_part1080),(kid04_part1081),(kid04_part1082),(kid04_part1083),(kid04_part1084),(kid04_part1085)])

theorem kid04_part1061_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part1061) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part1062),(kid04_part1063),(kid04_part1064),(kid04_part1065),(kid04_part1066),(kid04_part1067),(kid04_part1068),(kid04_part1069),(kid04_part1070),(kid04_part1071),(kid04_part1072),(kid04_part1073),(kid04_part1074),(kid04_part1075),(kid04_part1076),(kid04_part1077),(kid04_part1078),(kid04_part1079),(kid04_part1080),(kid04_part1081),(kid04_part1082),(kid04_part1083),(kid04_part1084),(kid04_part1085)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1062_checked

  · exact kid04_part1068_checked

  · exact kid04_part1074_checked

  · exact kid04_part1080_checked

  · exact kid04_part1063_checked

  · exact kid04_part1069_checked

  · exact kid04_part1075_checked

  · exact kid04_part1081_checked

  · exact kid04_part1064_checked

  · exact kid04_part1070_checked

  · exact kid04_part1076_checked

  · exact kid04_part1082_checked

  · exact kid04_part1065_checked

  · exact kid04_part1071_checked

  · exact kid04_part1077_checked

  · exact kid04_part1083_checked

  · exact kid04_part1066_checked

  · exact kid04_part1072_checked

  · exact kid04_part1078_checked

  · exact kid04_part1084_checked

  · exact kid04_part1067_checked

  · exact kid04_part1073_checked

  · exact kid04_part1079_checked

  · exact kid04_part1085_checked

def kid04_part1086 : Audit := .cycle 0 10 true (0)
theorem kid04_part1086_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part1086) = true := by rfl

def kid04_part1087 : Audit := .cycle 1 9 true (1)
theorem kid04_part1087_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part1087) = true := by rfl

def kid04_part1088 : Audit := .cycle 9 11 true (2)
theorem kid04_part1088_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part1088) = true := by rfl

def kid04_part1089 : Audit := .cycle 3 7 true (1)
theorem kid04_part1089_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part1089) = true := by rfl

def kid04_part1090 : Audit := .cycle 9 1 true (3)
theorem kid04_part1090_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part1090) = true := by rfl

def kid04_part1091 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (3),
.cycle 12 9 true (0),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 21 (5,true) (byMove [
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 0 27 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 4, 64],[4, 64, 36, 1, 16, 36, 64],64⟩,
.cycle 0 25 true (0),
.cycle 2 21 true (1),
.last 22 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 4, 64],[4, 64, 36, 1, 16, 4, 64],64⟩,
.cycle 0 23 true (0),
.cycle 8 14 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 4, 64],[4, 64, 36, 1, 16, 32, 64],64⟩,
.last 23 (1,true),
.cycle 7 21 true (2),
.cycle 2 23 true (1),
.cycle 4 25 true (1),
.cycle 20 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 4, 64],[4, 64, 36, 1, 16, 36, 64],64⟩,
.cycle 2 21 true (1),
.last 22 (1,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 8 14 true (2),
.cycle 22 11 true (6)
]),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 9 11 true (2),
.cycle 3 18 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 21 13 true (3),
.cycle 11 9 true (2),
.cycle 8 26 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 32, 8, 64],[4, 64, 40, 1, 16, 32, 64],64⟩,
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 9 11 true (2),
.cycle 3 18 true (1)
]),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.last 19 (5,true),
.last 16 (5,true),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 6 8 true (2)
]),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 8 7 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 20, 64],[4, 64, 52, 1, 16, 4, 64],64⟩,
.cycle 11 9 true (2),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (3),
.cycle 8 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 8 7 true (2)
]),
.split 12 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 0 56 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 21 1 false (1),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.cycle 26 1 false (6),
.last 14 (1,true),
.last 30 (1,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.cycle 13 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid04_part1091_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part1091) = true := by rfl

def kid04_part1092 : Audit := .cycle 6 4 true (2)
theorem kid04_part1092_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part1092) = true := by rfl

def kid04_part1093 : Audit := .split 10 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.cycle 11 6 false (1),
.split 11 (5,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (0),
.cycle 21 1 false (-3),
.last 19 (5,true),
.cycle 12 7 false (1),
.last 12 (5,true),
.last 14 (5,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 18 (5,true),
.last 13 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.last 24 (5,true),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 12 (5,true),
.last 14 (5,true),
.last 17 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.last 13 (5,true)
]),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 19 7 false (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 47 1 false (9),
.cycle 35 1 false (7),
.cycle 7 7 true (2),
.last 12 (5,false),
.last 14 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 19 7 false (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
]),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 18 1 false (0),
.cycle 11 6 false (1),
.split 11 (5,false) (byMove [
.last 32 (5,true),
.last 19 (5,true),
.cycle 21 1 false (-3),
.last 15 (5,true),
.cycle 12 7 false (1),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 10 2 true (1),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.last 16 (5,true),
.last 12 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 15 8 true (-4),
.cycle 19 1 false (-1),
.last 18 (5,true),
.last 12 (5,true),
.last 17 (5,true),
.last 13 (5,true),
.last 16 (5,true),
.cycle 2 12 true (1),
.last 16 (5,true),
.last 12 (5,true)
]),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 13 (5,false),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 7 7 true (2),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
])
theorem kid04_part1093_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part1093) = true := by rfl

def kid04_part1094 : Audit := .split 17 (1,true) (byMove [
.cycle 0 36 true (-2),
.cycle 11 16 true (-2),
.cycle 0 26 true (-2),
.cycle 0 37 true (-2),
.cycle 11 8 true (-2),
.split 18 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 11 16 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 26 true (-2),
.last 19 (5,false),
.cycle 0 37 true (-2),
.cycle 0 22 true (-2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 0 28 true (-2),
.last 19 (5,false),
.cycle 16 3 false (1),
.cycle 11 11 false (1),
.cycle 0 43 true (-2),
.cycle 19 1 false (-1),
.cycle 0 44 true (-2),
.last 19 (5,false),
.far true 1 ⟨0,[0, 0],[28, 28, 8, 8, 4, 64, 64],[28, 32, 16, 12, 16, 28, 64],96⟩,
.cycle 0 22 true (-2),
.cycle 0 36 true (-2),
.cycle 0 24 true (-2),
.cycle 11 8 true (-2),
.last 19 (5,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 1, 15, 1, 16, 64, 64],96⟩,
.cycle 7 12 true (-2),
.cycle 0 20 true (-2),
.cycle 0 32 true (-2),
.cycle 0 39 true (-2),
.split 18 (5,false) (byMove [
.last 36 (5,true),
.cycle 0 22 true (-2),
.last 33 (5,true),
.cycle 0 24 true (-2),
.cycle 11 8 true (-2),
.last 20 (5,true),
.cycle 0 35 true (-2),
.cycle 19 16 true (3),
.cycle 0 23 true (-2),
.cycle 0 20 true (-2),
.cycle 0 31 true (-2),
.last 19 (5,true),
.last 21 (5,true),
.last 32 (5,true),
.cycle 0 39 true (-2),
.last 31 (5,true),
.last 26 (5,true),
.last 20 (5,true),
.cycle 0 42 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073741856, 1, 128, 8192, 16384, 8, 256, 32, 8192, 33554432, 67108864, 2097152, 256, 1073741824, 33554432, 8192, 16384, 8, 32, 1, 8192, 33554432, 67108864, 134217728, 1864384937, 1864384937, 33554432, 1073741824],[256, 32, 128, 1, 1024, 1073741824, 16384, 32, 32, 1, 65536, 1073741824, 67108864, 8388608, 1073741824, 262144, 268435456, 1073741824, 16384, 32, 1073741824, 1, 65536, 1073741824, 67108864, 536870912, 1864384937, 16777216, 268435456, 1073741824, 1073741824],2140650318⟩,
.cycle 7 12 true (-2),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719612160, 1, 512, 524288, 1048576, 32768, 256, 135168, 2097152, 128, 256, 8, 135168, 1, 512, 2147483648, 4294967296, 134217728, 256, 68719476992, 8589934592, 2147483648, 4294967296, 8589934592, 135168, 1073741824, 8589934592, 2147483648, 4294967296, 8589934592, 119320777601, 119320777601, 8589934592, 68719476736],[256, 32, 128, 1, 1024, 68719476736, 1048576, 131072, 135168, 4096, 4194304, 68719476736, 256, 32, 640, 1, 1024, 68719476736, 4294967296, 536870912, 68719476992, 16777216, 17179869184, 68719476736, 4294967296, 34359738368, 68719509504, 1073741824, 17179869184, 68719476736, 4294967296, 34359738368, 119320777601, 1073741824, 17179869184, 68719476736, 68719476736],137301344332⟩,
.proven (BB6.Agent11Raw39B1RCPumps.M176.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M176.never m hm),
.last 19 (5,true)
]),
.cycle 11 10 true (-2),
.cycle 11 11 false (1),
.cycle 12 6 true (-2),
.cycle 0 22 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 31, 31, 64, 64],[4, 31, 31, 1, 16, 64, 64],96⟩,
.split 18 (5,true) (byMove [
.cycle 11 15 false (1),
.cycle 0 28 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 6 true (-2),
.last 19 (5,false),
.cycle 0 22 true (-2),
.last 20 (5,false),
.cycle 0 49 true (-2),
.cycle 0 24 true (-2),
.cycle 19 13 true (-1),
.last 20 (5,false),
.cycle 16 3 false (1),
.cycle 11 11 false (1),
.cycle 0 24 true (-2),
.cycle 19 1 false (-1),
.cycle 11 14 true (-2),
.last 19 (5,false),
.cycle 0 22 true (-2),
.cycle 17 2 true (0),
.cycle 11 10 true (-2),
.far true 1 ⟨0,[0, 0],[28, 28, 8, 8, 4, 64, 64],[28, 32, 16, 12, 16, 28, 64],96⟩,
.far true 1 ⟨0,[0, 0],[28, 28, 8, 8, 4, 64, 64],[28, 32, 16, 12, 16, 16, 64],96⟩,
.last 20 (5,false)
]),
.cycle 35 16 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 2, 15, 1, 16, 64, 64],96⟩,
.cycle 0 20 true (-2),
.cycle 4 14 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 31, 31, 64, 64],[4, 16, 31, 1, 16, 64, 64],96⟩,
.split 18 (5,false) (byMove [
.cycle 0 22 true (-2),
.cycle 17 2 true (1),
.cycle 11 10 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073872896, 1, 1073741960, 8192, 16384, 8, 256, 131072, 128, 33554432, 67108864, 2097152, 256, 1073741824, 128, 8192, 16384, 8, 131072, 1, 8, 33554432, 67108864, 134217728, 1864524169, 1864524169, 1864524169, 1073741824],[256, 2048, 128, 1, 1024, 1073741824, 16384, 131072, 131072, 1, 65536, 1073741824, 67108864, 536870912, 1073741824, 262144, 268435456, 1073741824, 16384, 131072, 1073741824, 1, 65536, 1073741824, 67108864, 536870912, 1864524169, 16777216, 268435456, 1073741824, 1073741824],2140517230⟩,
.last 30 (5,true),
.last 19 (5,true),
.last 58 (5,true),
.cycle 19 16 true (3),
.last 30 (5,true),
.cycle 0 20 true (-2),
.last 32 (5,true),
.last 19 (5,true),
.last 32 (5,true),
.last 20 (5,true),
.last 28 (5,true),
.cycle 5 14 true (-2),
.last 38 (5,true),
.last 19 (5,true),
.last 42 (5,true),
.last 50 (5,true),
.last 34 (5,true),
.last 46 (5,true),
.last 36 (5,true),
.last 19 (5,true)
])
])
theorem kid04_part1094_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part1094) = true := by rfl

def kid04_part1095 : Audit := .cycle 2 10 true (1)
theorem kid04_part1095_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part1095) = true := by rfl

def kid04_part1096 : Audit := .cycle 8 3 true (2)
theorem kid04_part1096_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part1096) = true := by rfl

def kid04_part1098 : Audit := .cycle 0 20 true (0)
theorem kid04_part1098_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1098) = true := by rfl

def kid04_part1099 : Audit := .cycle 0 14 true (0)
theorem kid04_part1099_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1099) = true := by rfl

def kid04_part1100 : Audit := .cycle 21 1 false (1)
theorem kid04_part1100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1100) = true := by rfl

def kid04_part1101 : Audit := .cycle 0 16 true (0)
theorem kid04_part1101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1101) = true := by rfl

def kid04_part1102 : Audit := .split 14 (5,false) (byMove [
.cycle 11 11 false (1),
.last 19 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 19 (1,true),
.last 15 (1,true),
.cycle 13 3 false (-1),
.last 17 (1,true),
.cycle 11 5 false (1),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 21 (1,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 19 (1,true),
.last 15 (1,true),
.cycle 11 6 false (1),
.last 17 (1,true),
.cycle 11 8 false (1),
.cycle 11 6 false (1)
])
theorem kid04_part1102_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1102) = true := by rfl

def kid04_part1103 : Audit := .split 11 (5,false) (byMove [
.cycle 0 42 true (-1),
.last 12 (1,true),
.cycle 16 1 false (-2),
.cycle 21 1 false (-1),
.cycle 15 2 false (-1),
.cycle 13 1 false (-1),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 14 1 true (2),
.last 19 (1,true),
.last 12 (1,true),
.last 21 (1,true),
.cycle 0 16 true (0),
.cycle 17 2 false (-1),
.cycle 13 1 false (-1),
.last 13 (1,true),
.cycle 1 19 false (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 14 3 false (0),
.cycle 17 1 true (-1)
])
theorem kid04_part1103_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1103) = true := by rfl

def kid04_part1104 : Audit := .cycle 2 10 true (1)
theorem kid04_part1104_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1104) = true := by rfl

def kid04_part1105 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (5,false),
.cycle 35 1 false (7),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid04_part1105_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1105) = true := by rfl

def kid04_part1106 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 18 1 false (-2),
.last 16 (1,true),
.cycle 18 2 false (0),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 17 3 false (1),
.cycle 0 15 true (0),
.cycle 8 6 true (1),
.cycle 47 1 false (7),
.last 23 (1,true),
.last 14 (1,true),
.cycle 20 15 true (0),
.cycle 23 1 false (-1),
.cycle 26 2 false (0),
.cycle 17 1 false (-1),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 19 7 false (1),
.cycle 0 15 true (0),
.cycle 18 9 false (2),
.cycle 0 31 true (0)
])
theorem kid04_part1106_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1106) = true := by rfl

def kid04_part1107 : Audit := .cycle 0 12 true (0)
theorem kid04_part1107_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1107) = true := by rfl

def kid04_part1108 : Audit := .cycle 8 3 true (2)
theorem kid04_part1108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1108) = true := by rfl

def kid04_part1109 : Audit := .split 12 (5,false) (byMove [
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
.cycle 8 7 true (2),
.cycle 12 1 true (4),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 2 false (5),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid04_part1109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1109) = true := by rfl

def kid04_part1110 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.last 21 (5,false),
.cycle 0 17 true (0),
.cycle 18 5 false (1),
.cycle 18 3 false (0),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 19 5 false (1),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.last 16 (5,false),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 21 (5,false),
.cycle 5 8 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 64, 64],[1, 16, 16, 1, 1, 1, 64],112⟩,
.cycle 18 3 false (0),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 64, 64],[1, 1, 16, 1, 1, 1, 64],112⟩,
.cycle 18 13 false (2)
])
theorem kid04_part1110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1110) = true := by rfl

def kid04_part1111 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 18 5 false (2),
.cycle 26 5 false (6),
.last 19 (5,false),
.cycle 19 5 false (3),
.cycle 18 5 true (2),
.cycle 17 5 false (1),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 12 6 true (0),
.cycle 1 19 true (0),
.cycle 17 5 false (1),
.cycle 5 12 true (0),
.cycle 18 5 true (2),
.cycle 15 2 true (0)
])
theorem kid04_part1111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1111) = true := by rfl

def kid04_part1112 : Audit := .cycle 2 12 true (1)
theorem kid04_part1112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1112) = true := by rfl

def kid04_part1113 : Audit := .cycle 18 1 false (0)
theorem kid04_part1113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1113) = true := by rfl

def kid04_part1114 : Audit := .split 14 (5,false) (byMove [
.cycle 25 5 true (1),
.last 25 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 7 false (1),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 11 8 true (-2),
.cycle 17 5 true (1),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 23 5 true (1),
.last 15 (1,true),
.cycle 11 6 false (1),
.cycle 5 10 false (3),
.cycle 17 5 true (1),
.cycle 19 5 true (1)
])
theorem kid04_part1114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1114) = true := by rfl

def kid04_part1115 : Audit := .split 11 (5,false) (byMove [
.cycle 49 8 false (1),
.last 12 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 15 2 false (-1),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.last 12 (1,true),
.cycle 15 3 false (0),
.cycle 2 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 10 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 18 8 true (0),
.cycle 19 1 false (-1),
.cycle 21 2 false (-1),
.cycle 13 1 false (-1),
.cycle 17 7 false (1),
.last 12 (1,true),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 13 3 false (1)
])
theorem kid04_part1115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1115) = true := by rfl

def kid04_part1116 : Audit := .cycle 2 10 true (1)
theorem kid04_part1116_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1116) = true := by rfl

def kid04_part1117 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 18 (5,false),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.last 18 (5,false),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid04_part1117_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1117) = true := by rfl

def kid04_part1118 : Audit := .cycle 7 4 true (2)
theorem kid04_part1118_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1118) = true := by rfl

def kid04_part1119 : Audit := .cycle 0 12 true (0)
theorem kid04_part1119_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1119) = true := by rfl

def kid04_part1120 : Audit := .cycle 8 3 true (2)
theorem kid04_part1120_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1120) = true := by rfl

def kid04_part1121 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 8 7 true (2),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 10 7 true (2),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid04_part1121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1121) = true := by rfl

def kid04_part1097 : Audit := .split 10 (5,true) (byMove [(kid04_part1098),(kid04_part1099),(kid04_part1100),(kid04_part1101),(kid04_part1102),(kid04_part1103),(kid04_part1104),(kid04_part1105),(kid04_part1106),(kid04_part1107),(kid04_part1108),(kid04_part1109),(kid04_part1110),(kid04_part1111),(kid04_part1112),(kid04_part1113),(kid04_part1114),(kid04_part1115),(kid04_part1116),(kid04_part1117),(kid04_part1118),(kid04_part1119),(kid04_part1120),(kid04_part1121)])

theorem kid04_part1097_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part1097) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part1098),(kid04_part1099),(kid04_part1100),(kid04_part1101),(kid04_part1102),(kid04_part1103),(kid04_part1104),(kid04_part1105),(kid04_part1106),(kid04_part1107),(kid04_part1108),(kid04_part1109),(kid04_part1110),(kid04_part1111),(kid04_part1112),(kid04_part1113),(kid04_part1114),(kid04_part1115),(kid04_part1116),(kid04_part1117),(kid04_part1118),(kid04_part1119),(kid04_part1120),(kid04_part1121)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1098_checked

  · exact kid04_part1104_checked

  · exact kid04_part1110_checked

  · exact kid04_part1116_checked

  · exact kid04_part1099_checked

  · exact kid04_part1105_checked

  · exact kid04_part1111_checked

  · exact kid04_part1117_checked

  · exact kid04_part1100_checked

  · exact kid04_part1106_checked

  · exact kid04_part1112_checked

  · exact kid04_part1118_checked

  · exact kid04_part1101_checked

  · exact kid04_part1107_checked

  · exact kid04_part1113_checked

  · exact kid04_part1119_checked

  · exact kid04_part1102_checked

  · exact kid04_part1108_checked

  · exact kid04_part1114_checked

  · exact kid04_part1120_checked

  · exact kid04_part1103_checked

  · exact kid04_part1109_checked

  · exact kid04_part1115_checked

  · exact kid04_part1121_checked

def kid04_part1122 : Audit := .cycle 0 10 true (0)
theorem kid04_part1122_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part1122) = true := by rfl

def kid04_part1123 : Audit := .cycle 1 9 true (1)
theorem kid04_part1123_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part1123) = true := by rfl

def kid04_part1124 : Audit := .cycle 2 8 true (1)
theorem kid04_part1124_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part1124) = true := by rfl

def kid04_part1125 : Audit := .cycle 2 11 true (1)
theorem kid04_part1125_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part1125) = true := by rfl

def kid04_part1126 : Audit := .cycle 9 1 true (3)
theorem kid04_part1126_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part1126) = true := by rfl

def kid04_part1127 : Audit := .split 10 (5,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.last 17 (5,true),
.cycle 15 8 true (-2),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 19 1 false (1),
.cycle 6 6 true (2),
.last 12 (1,true),
.last 23 (1,true),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (5,true) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 8 13 true (2),
.cycle 52 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.cycle 9 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 4, 64],[4, 64, 36, 1, 16, 32, 64],64⟩,
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 17 4 true (4),
.cycle 2 21 true (1),
.cycle 8 14 true (2),
.cycle 9 22 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 9 12 true (3),
.cycle 10 11 true (3)
]),
.cycle 3 8 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.last 22 (5,true),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.last 26 (5,true),
.cycle 5 7 true (1),
.cycle 8 6 true (2),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true)
]),
.split 14 (5,true) (byMove [
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 8 7 true (2),
.cycle 17 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.cycle 8 16 true (2),
.cycle 0 18 true (0),
.cycle 6 9 true (2),
.last 15 (1,true),
.cycle 11 4 true (2),
.cycle 2 15 true (1),
.cycle 8 8 true (2),
.cycle 17 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 9 6 true (2),
.cycle 10 5 true (2)
]),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 21 1 false (-1),
.last 14 (1,true),
.cycle 8 7 true (2),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 33 1 false (7),
.cycle 6 11 true (2),
.last 12 (1,true),
.cycle 23 4 true (0),
.cycle 5 7 true (1),
.cycle 8 6 true (2),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid04_part1127_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part1127) = true := by rfl

def kid04_part1055 : Audit := .split 9 (4,false) (byMove [(kid04_part1056),(kid04_part1057),(kid04_part1058),(kid04_part1059),(kid04_part1060),(kid04_part1061),(kid04_part1086),(kid04_part1087),(kid04_part1088),(kid04_part1089),(kid04_part1090),(kid04_part1091),(kid04_part1092),(kid04_part1093),(kid04_part1094),(kid04_part1095),(kid04_part1096),(kid04_part1097),(kid04_part1122),(kid04_part1123),(kid04_part1124),(kid04_part1125),(kid04_part1126),(kid04_part1127)])

theorem kid04_part1055_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (kid04_part1055) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid04_part1056),(kid04_part1057),(kid04_part1058),(kid04_part1059),(kid04_part1060),(kid04_part1061),(kid04_part1086),(kid04_part1087),(kid04_part1088),(kid04_part1089),(kid04_part1090),(kid04_part1091),(kid04_part1092),(kid04_part1093),(kid04_part1094),(kid04_part1095),(kid04_part1096),(kid04_part1097),(kid04_part1122),(kid04_part1123),(kid04_part1124),(kid04_part1125),(kid04_part1126),(kid04_part1127)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1056_checked

  · exact kid04_part1086_checked

  · exact kid04_part1092_checked

  · exact kid04_part1122_checked

  · exact kid04_part1057_checked

  · exact kid04_part1087_checked

  · exact kid04_part1093_checked

  · exact kid04_part1123_checked

  · exact kid04_part1058_checked

  · exact kid04_part1088_checked

  · exact kid04_part1094_checked

  · exact kid04_part1124_checked

  · exact kid04_part1059_checked

  · exact kid04_part1089_checked

  · exact kid04_part1095_checked

  · exact kid04_part1125_checked

  · exact kid04_part1060_checked

  · exact kid04_part1090_checked

  · exact kid04_part1096_checked

  · exact kid04_part1126_checked

  · exact kid04_part1061_checked

  · exact kid04_part1091_checked

  · exact kid04_part1097_checked

  · exact kid04_part1127_checked

def kid04_part1129 : Audit := .cycle 2 9 true (1)
theorem kid04_part1129_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid04_part1129) = true := by rfl

def kid04_part1130 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 1 12 true (1),
.cycle 14 6 false (1),
.cycle 12 6 false (0),
.cycle 0 24 true (-2),
.cycle 24 1 false (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 15 3 false (1)
]),
.cycle 11 11 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (1),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 10 3 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 15 (5,true),
.cycle 0 16 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 1 11 true (1),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 20 (5,true),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.last 12 (5,true),
.last 21 (5,true),
.cycle 12 6 false (0),
.last 19 (5,true),
.cycle 19 1 false (-1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 14 (5,true),
.last 17 (5,true),
.cycle 0 13 true (0),
.last 16 (5,true),
.last 12 (5,true)
]),
.split 19 (5,true) (byMove [
.cycle 0 37 true (-2),
.cycle 0 23 true (-2),
.cycle 11 17 false (2),
.cycle 18 19 false (2),
.last 20 (4,false),
.cycle 1 20 false (3),
.cycle 0 34 true (-2),
.cycle 0 25 true (-2),
.last 21 (4,false),
.cycle 0 21 true (-2),
.cycle 0 27 true (-2),
.cycle 0 36 true (-2),
.cycle 11 18 false (2),
.cycle 7 14 false (3),
.cycle 0 36 true (-2),
.cycle 11 15 false (2),
.last 20 (4,false),
.cycle 0 38 true (-2),
.cycle 2 19 true (-2),
.cycle 18 2 true (1),
.cycle 0 28 true (-2),
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 64, 2, 64],[34, 32, 16, 34, 34, 34, 64],80⟩,
.cycle 18 4 true (1),
.cycle 18 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.cycle 8 5 true (2),
.last 33 (5,true),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid04_part1130_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid04_part1130) = true := by rfl

def kid04_part1132 : Audit := .cycle 0 23 false (3)
theorem kid04_part1132_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part1132) = true := by rfl

def kid04_part1133 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (2),
.cycle 15 1 false (1),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 16 11 false (3),
.cycle 11 2 true (0),
.cycle 13 11 false (1)
])
theorem kid04_part1133_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part1133) = true := by rfl

def kid04_part1134 : Audit := .cycle 15 1 false (-1)
theorem kid04_part1134_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part1134) = true := by rfl

def kid04_part1135 : Audit := .cycle 0 13 true (0)
theorem kid04_part1135_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part1135) = true := by rfl

def kid04_part1136 : Audit := .cycle 15 1 false (-1)
theorem kid04_part1136_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part1136) = true := by rfl

def kid04_part1137 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 26 1 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 26 1 false (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 25 1 false (-1),
.cycle 28 1 false (0),
.cycle 11 2 true (0),
.cycle 18 1 false (-2)
])
theorem kid04_part1137_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part1137) = true := by rfl

def kid04_part1138 : Audit := .cycle 0 12 true (0)
theorem kid04_part1138_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part1138) = true := by rfl

def kid04_part1139 : Audit := .cycle 1 11 true (1)
theorem kid04_part1139_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part1139) = true := by rfl

def kid04_part1140 : Audit := .cycle 24 1 false (2)
theorem kid04_part1140_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part1140) = true := by rfl

def kid04_part1141 : Audit := .cycle 21 1 false (1)
theorem kid04_part1141_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part1141) = true := by rfl

def kid04_part1142 : Audit := .cycle 11 1 true (1)
theorem kid04_part1142_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part1142) = true := by rfl

def kid04_part1143 : Audit := .cycle 25 1 false (1)
theorem kid04_part1143_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part1143) = true := by rfl

def kid04_part1144 : Audit := .split 19 (1,true) (byMove [
.cycle 12 13 false (1),
.cycle 12 14 false (1),
.cycle 16 4 false (0),
.cycle 0 21 false (3),
.cycle 14 6 false (1),
.last 20 (5,true),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 17 3 true (-2),
.cycle 12 13 false (1),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.cycle 16 4 false (0),
.cycle 12 14 true (-2),
.last 21 (5,true),
.last 20 (5,true),
.cycle 13 26 false (3),
.cycle 13 22 false (2),
.cycle 2 18 false (3),
.cycle 12 15 true (-2),
.cycle 13 12 false (1),
.cycle 13 8 false (1)
])
theorem kid04_part1144_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part1144) = true := by rfl

def kid04_part1145 : Audit := .split 12 (1,true) (byMove [
.cycle 18 6 false (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 6 false (-1),
.cycle 15 1 false (-1),
.cycle 19 6 false (3),
.cycle 20 6 false (4),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 13 6 false (2),
.last 13 (5,true),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 21 6 false (3),
.cycle 13 1 false (-1),
.cycle 13 6 false (-1),
.cycle 15 1 false (-1),
.cycle 2 12 true (0),
.cycle 1 13 true (0),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 15 6 false (1),
.last 13 (5,true)
])
theorem kid04_part1145_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part1145) = true := by rfl

def kid04_part1146 : Audit := .split 17 (1,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 32 true (-2),
.cycle 0 22 true (-2),
.cycle 0 19 true (-2),
.cycle 0 24 true (-2),
.last 18 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 1, 15, 1, 32, 64, 64],64⟩,
.cycle 0 31 true (-2),
.cycle 0 43 true (-2),
.cycle 0 29 true (-2),
.cycle 0 21 true (-2),
.cycle 0 31 true (-2),
.cycle 0 26 true (-2),
.cycle 0 39 false (3),
.cycle 12 6 true (-2),
.cycle 0 32 true (-2),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 44 true (-2),
.cycle 0 48 true (-2),
.cycle 2 16 true (-2),
.cycle 0 33 true (-2),
.cycle 0 38 true (-2),
.cycle 0 26 true (-2)
])
theorem kid04_part1146_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part1146) = true := by rfl

def kid04_part1147 : Audit := .cycle 24 1 false (0)
theorem kid04_part1147_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part1147) = true := by rfl

def kid04_part1148 : Audit := .split 13 (5,true) (byMove [
.cycle 24 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.last 28 (1,true),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 8 10 true (0),
.cycle 24 1 false (0),
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 25 1 false (1),
.cycle 12 2 true (0),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 31 true (0),
.cycle 11 3 true (0),
.cycle 19 1 false (-1)
])
theorem kid04_part1148_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part1148) = true := by rfl

def kid04_part1149 : Audit := .split 12 (5,true) (byMove [
.cycle 25 1 false (-3),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 26 1 false (0),
.last 13 (1,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 19 1 false (-1),
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 21 1 false (-3),
.cycle 28 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 22 1 false (-2),
.cycle 22 1 false (-2)
])
theorem kid04_part1149_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part1149) = true := by rfl

def kid04_part1150 : Audit := .cycle 0 12 true (0)
theorem kid04_part1150_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part1150) = true := by rfl

def kid04_part1151 : Audit := .cycle 1 11 true (1)
theorem kid04_part1151_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part1151) = true := by rfl

def kid04_part1152 : Audit := .cycle 2 10 true (1)
theorem kid04_part1152_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part1152) = true := by rfl

def kid04_part1153 : Audit := .cycle 2 13 true (1)
theorem kid04_part1153_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part1153) = true := by rfl

def kid04_part1154 : Audit := .cycle 11 1 true (1)
theorem kid04_part1154_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part1154) = true := by rfl

def kid04_part1155 : Audit := .cycle 15 3 false (1)
theorem kid04_part1155_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part1155) = true := by rfl

def kid04_part1131 : Audit := .split 11 (4,false) (byMove [(kid04_part1132),(kid04_part1133),(kid04_part1134),(kid04_part1135),(kid04_part1136),(kid04_part1137),(kid04_part1138),(kid04_part1139),(kid04_part1140),(kid04_part1141),(kid04_part1142),(kid04_part1143),(kid04_part1144),(kid04_part1145),(kid04_part1146),(kid04_part1147),(kid04_part1148),(kid04_part1149),(kid04_part1150),(kid04_part1151),(kid04_part1152),(kid04_part1153),(kid04_part1154),(kid04_part1155)])

theorem kid04_part1131_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid04_part1131) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,false) (some mv)) (byMove [(kid04_part1132),(kid04_part1133),(kid04_part1134),(kid04_part1135),(kid04_part1136),(kid04_part1137),(kid04_part1138),(kid04_part1139),(kid04_part1140),(kid04_part1141),(kid04_part1142),(kid04_part1143),(kid04_part1144),(kid04_part1145),(kid04_part1146),(kid04_part1147),(kid04_part1148),(kid04_part1149),(kid04_part1150),(kid04_part1151),(kid04_part1152),(kid04_part1153),(kid04_part1154),(kid04_part1155)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1132_checked

  · exact kid04_part1138_checked

  · exact kid04_part1144_checked

  · exact kid04_part1150_checked

  · exact kid04_part1133_checked

  · exact kid04_part1139_checked

  · exact kid04_part1145_checked

  · exact kid04_part1151_checked

  · exact kid04_part1134_checked

  · exact kid04_part1140_checked

  · exact kid04_part1146_checked

  · exact kid04_part1152_checked

  · exact kid04_part1135_checked

  · exact kid04_part1141_checked

  · exact kid04_part1147_checked

  · exact kid04_part1153_checked

  · exact kid04_part1136_checked

  · exact kid04_part1142_checked

  · exact kid04_part1148_checked

  · exact kid04_part1154_checked

  · exact kid04_part1137_checked

  · exact kid04_part1143_checked

  · exact kid04_part1149_checked

  · exact kid04_part1155_checked

def kid04_part1156 : Audit := .cycle 0 11 true (0)
theorem kid04_part1156_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid04_part1156) = true := by rfl

def kid04_part1157 : Audit := .cycle 8 2 true (2)
theorem kid04_part1157_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid04_part1157) = true := by rfl

def kid04_part1158 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 16 1 false (0),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 15 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 18 1 false (2),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 8 14 true (0),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 15 1 false (1),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 18 5 false (1),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 19 5 false (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 20 (4,false),
.cycle 2 13 true (1),
.cycle 19 9 false (1),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 18 9 false (2)
]),
.split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 1 false (-1),
.cycle 23 5 false (3),
.cycle 24 5 false (4),
.last 18 (4,false),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.cycle 17 5 false (1),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 25 5 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 1 false (-1),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 13 4 true (0),
.cycle 15 2 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.cycle 8 4 true (1),
.cycle 10 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 12 2 true (0),
.cycle 14 1 false (-2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 15 2 true (0),
.cycle 0 13 true (0),
.cycle 14 2 true (1),
.cycle 12 2 true (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (2),
.cycle 6 6 true (2),
.last 12 (1,true),
.last 19 (1,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid04_part1158_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid04_part1158) = true := by rfl

def kid04_part1159 : Audit := .cycle 0 10 true (0)
theorem kid04_part1159_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid04_part1159) = true := by rfl

def kid04_part1160 : Audit := .cycle 1 9 true (1)
theorem kid04_part1160_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid04_part1160) = true := by rfl

def kid04_part1161 : Audit := .split 20 (4,false) (byMove [
.cycle 2 20 true (1),
.split 21 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 1 22 true (1),
.cycle 38 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 1 22 true (1),
.cycle 59 1 false (9),
.cycle 6 18 true (2),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 32 1 false (0),
.cycle 0 26 true (0),
.cycle 1 24 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 2 23 true (1),
.cycle 20 2 true (3),
.cycle 9 13 true (2)
]),
.cycle 45 1 false (1),
.cycle 0 22 true (0),
.cycle 8 13 true (2),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 39 1 false (1),
.cycle 38 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 41 1 false (3),
.cycle 59 1 false (9),
.last 23 (1,true),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 32 1 false (0),
.cycle 0 26 true (0),
.cycle 43 1 false (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 2 23 true (1),
.cycle 20 2 true (3),
.cycle 9 13 true (2)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.cycle 20 1 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 4, 64],[4, 64, 4, 1, 32, 64, 64],64⟩,
.cycle 6 15 true (2),
.split 21 (1,true) (byMove [
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 35 1 false (1),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.cycle 0 25 true (0),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.cycle 7 18 true (2),
.cycle 0 23 true (0),
.cycle 8 14 true (2),
.last 22 (5,true),
.cycle 39 9 false (2),
.cycle 36 7 false (1),
.cycle 2 23 true (1),
.cycle 32 1 false (0),
.last 31 (5,true),
.cycle 0 31 true (0),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 8 14 true (2),
.last 22 (5,true)
]),
.split 26 (1,true) (byMove [
.cycle 2 26 true (1),
.cycle 1 27 true (1),
.cycle 0 31 true (0),
.cycle 0 28 true (0),
.cycle 8 19 true (1),
.last 27 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 10 17 true (1),
.cycle 3 24 true (1),
.cycle 0 30 true (0),
.cycle 0 51 true (0),
.cycle 6 21 true (1),
.cycle 34 13 false (2),
.cycle 21 6 true (1),
.cycle 2 27 true (1),
.last 28 (5,true),
.last 27 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 2 28 true (1),
.cycle 16 12 true (1),
.cycle 16 34 true (1)
]),
.cycle 2 21 true (1),
.split 22 (5,true) (byMove [
.cycle 2 22 true (1),
.last 23 (1,true),
.cycle 29 1 false (-1),
.cycle 0 24 true (0),
.cycle 8 15 true (2),
.cycle 42 1 false (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 10 13 true (2),
.cycle 3 20 true (1),
.cycle 8 19 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 4, 64],[4, 64, 4, 1, 32, 32, 64],64⟩,
.cycle 6 17 true (2),
.last 23 (1,true),
.cycle 29 1 false (-1),
.cycle 2 23 true (1),
.cycle 21 2 true (3),
.cycle 33 1 false (-1),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 2 24 true (1),
.cycle 20 3 true (3),
.cycle 9 14 true (2)
]),
.split 21 (5,true) (byMove [
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 35 1 false (1),
.cycle 0 31 true (0),
.cycle 27 3 false (-1),
.cycle 0 25 true (0),
.cycle 2 21 true (1),
.last 22 (1,true),
.cycle 31 3 false (1),
.cycle 0 23 true (0),
.cycle 8 14 true (2),
.cycle 41 3 false (4),
.last 23 (1,true),
.last 36 (1,true),
.cycle 2 23 true (1),
.cycle 32 1 false (0),
.cycle 27 3 false (-1),
.cycle 29 3 false (0),
.cycle 2 21 true (1),
.last 22 (1,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 8 14 true (2),
.cycle 9 14 true (2)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 20 1 true (4),
.cycle 9 12 true (2)
])
theorem kid04_part1161_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid04_part1161) = true := by rfl

def kid04_part1162 : Audit := .cycle 3 7 true (1)
theorem kid04_part1162_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid04_part1162) = true := by rfl

def kid04_part1163 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 8 4 true (2),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (5,true) (byMove [
.cycle 2 22 true (1),
.last 23 (1,true),
.cycle 8 26 true (2),
.cycle 0 24 true (0),
.cycle 8 15 true (2),
.cycle 9 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 8 24 true (2),
.cycle 3 20 true (1),
.cycle 10 13 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 61, 4, 16, 64],[4, 64, 24, 1, 32, 32, 64],64⟩,
.cycle 6 17 true (2),
.last 23 (1,true),
.cycle 0 27 true (0),
.cycle 2 23 true (1),
.cycle 21 2 true (5),
.cycle 20 4 true (4),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 2 24 true (1),
.cycle 8 25 true (2),
.cycle 9 14 true (2)
]),
.cycle 8 11 true (2),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 14 true (2),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.last 20 (5,true),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 9 4 true (3)
]),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 19 1 false (-1),
.last 16 (1,true),
.cycle 8 8 true (2),
.cycle 22 1 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 8 19 true (2),
.cycle 0 15 true (0),
.cycle 8 6 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 8 10 true (2),
.last 14 (1,true),
.cycle 19 1 false (-1),
.cycle 5 9 true (1),
.cycle 12 2 true (2),
.cycle 12 4 true (1),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 8 6 true (2),
.cycle 9 6 true (2)
]),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid04_part1163_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid04_part1163) = true := by rfl

def kid04_part1164 : Audit := .cycle 9 1 true (3)
theorem kid04_part1164_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid04_part1164) = true := by rfl

def kid04_part1165 : Audit := .cycle 6 4 true (2)
theorem kid04_part1165_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid04_part1165) = true := by rfl

def kid04_part1166 : Audit := .split 10 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.split 11 (4,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (0),
.cycle 15 1 false (-1),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.cycle 14 6 false (1),
.cycle 12 6 false (0),
.cycle 13 8 true (-2),
.cycle 0 16 true (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 16 9 false (2),
.cycle 17 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 28 (5,true),
.cycle 15 3 false (1)
]),
.cycle 11 6 false (1),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 18 1 false (0),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 7 8 true (2),
.cycle 0 31 true (0),
.cycle 20 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (2)
]),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,false),
.cycle 35 1 false (7),
.last 12 (4,false),
.cycle 7 7 true (2),
.cycle 7 9 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 33 (5,true),
.last 20 (5,true),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 10 2 true (1),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.last 21 (5,true),
.cycle 12 6 false (0),
.last 19 (5,true),
.cycle 19 1 false (-1),
.last 13 (5,true),
.last 12 (5,true),
.last 18 (5,true),
.last 14 (5,true),
.last 17 (5,true),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 11 6 false (1),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 9 4 true (2),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 13 8 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 7 7 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.last 13 (4,false),
.cycle 2 12 true (1),
.cycle 11 2 true (2),
.cycle 13 8 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
])
theorem kid04_part1166_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid04_part1166) = true := by rfl

def kid04_part1168 : Audit := .cycle 0 42 true (-1)
theorem kid04_part1168_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,0⟩)) (kid04_part1168) = true := by rfl

def kid04_part1169 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 11 false (0),
.cycle 0 20 true (-2),
.cycle 18 11 false (2),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 11 false (2),
.cycle 0 21 true (0),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 20 11 false (2),
.cycle 13 1 false (-1),
.cycle 1 26 false (3),
.cycle 17 11 false (2),
.cycle 21 11 false (1),
.cycle 0 16 true (0),
.cycle 13 11 false (2),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.cycle 13 11 false (1)
])
theorem kid04_part1169_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,1⟩)) (kid04_part1169) = true := by rfl

def kid04_part1170 : Audit := .cycle 15 1 false (-1)
theorem kid04_part1170_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,2⟩)) (kid04_part1170) = true := by rfl

def kid04_part1171 : Audit := .cycle 23 1 false (-1)
theorem kid04_part1171_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,3⟩)) (kid04_part1171) = true := by rfl

def kid04_part1172 : Audit := .cycle 15 1 false (-1)
theorem kid04_part1172_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,4⟩)) (kid04_part1172) = true := by rfl

def kid04_part1173 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 13 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 false (3),
.cycle 0 20 true (-2),
.cycle 13 13 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 13 false (3),
.last 17 (1,true),
.last 14 (1,true),
.cycle 14 13 false (0),
.cycle 13 13 false (3),
.cycle 13 1 false (-1),
.last 18 (1,true),
.cycle 22 13 false (2),
.cycle 18 13 false (2),
.cycle 0 16 true (0),
.cycle 18 13 false (2),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.cycle 13 13 false (1)
])
theorem kid04_part1173_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,false,5⟩)) (kid04_part1173) = true := by rfl

def kid04_part1174 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 8 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 29 true (0),
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 6 8 true (1),
.cycle 19 9 false (1),
.cycle 10 4 true (1),
.cycle 2 14 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 0 15 true (0),
.last 22 (5,true)
])
theorem kid04_part1174_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,0⟩)) (kid04_part1174) = true := by rfl

def kid04_part1175 : Audit := .cycle 7 6 true (1)
theorem kid04_part1175_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,1⟩)) (kid04_part1175) = true := by rfl

def kid04_part1176 : Audit := .cycle 0 14 true (0)
theorem kid04_part1176_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,2⟩)) (kid04_part1176) = true := by rfl

def kid04_part1177 : Audit := .cycle 21 1 false (1)
theorem kid04_part1177_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,3⟩)) (kid04_part1177) = true := by rfl

def kid04_part1178 : Audit := .cycle 8 5 true (1)
theorem kid04_part1178_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,4⟩)) (kid04_part1178) = true := by rfl

def kid04_part1179 : Audit := .cycle 2 14 true (1)
theorem kid04_part1179_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,5⟩)) (kid04_part1179) = true := by rfl

def kid04_part1180 : Audit := .split 19 (1,true) (byMove [
.cycle 12 13 false (1),
.cycle 12 14 false (1),
.cycle 16 4 false (0),
.cycle 13 13 false (1),
.cycle 14 6 false (1),
.last 20 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 1, 15, 1, 32, 64, 64],64⟩,
.cycle 7 14 false (3),
.cycle 0 54 true (-2),
.cycle 12 11 false (1),
.last 42 (5,true),
.cycle 0 26 true (-2),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.cycle 16 4 false (0),
.cycle 0 44 true (-2),
.last 21 (5,true),
.last 20 (5,true),
.cycle 43 22 false (3),
.cycle 13 14 false (1),
.cycle 2 22 true (-2),
.cycle 4 16 false (3),
.cycle 13 12 false (1),
.cycle 13 8 false (1)
])
theorem kid04_part1180_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,0⟩)) (kid04_part1180) = true := by rfl

def kid04_part1181 : Audit := .split 12 (1,true) (byMove [
.cycle 18 6 false (0),
.cycle 34 6 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 6 false (-1),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 14 6 false (3),
.cycle 13 6 false (1),
.cycle 20 6 false (4),
.cycle 13 6 false (2),
.last 13 (5,true),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.cycle 13 6 false (-1),
.cycle 17 6 false (1),
.cycle 0 16 true (0),
.cycle 21 6 false (1),
.cycle 13 6 false (1),
.cycle 12 29 true (0),
.cycle 15 6 false (1),
.last 13 (5,true)
])
theorem kid04_part1181_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,1⟩)) (kid04_part1181) = true := by rfl

def kid04_part1182 : Audit := .split 17 (1,true) (byMove [
.cycle 0 36 true (-2),
.cycle 12 16 true (-2),
.cycle 0 26 true (-2),
.cycle 0 37 true (-2),
.cycle 12 8 true (-2),
.last 18 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 1, 15, 1, 32, 64, 64],64⟩,
.cycle 7 12 true (-2),
.cycle 0 20 true (-2),
.cycle 0 32 true (-2),
.cycle 0 39 true (-2),
.cycle 0 39 true (-2),
.cycle 12 10 true (-2),
.cycle 12 11 false (1),
.cycle 12 6 true (-2),
.cycle 0 22 true (-2),
.last 19 (5,true),
.last 18 (5,true),
.cycle 35 16 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 2, 15, 1, 32, 64, 64],64⟩,
.cycle 0 20 true (-2),
.cycle 4 14 true (-2),
.last 29 (5,true),
.last 28 (5,true)
])
theorem kid04_part1182_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,2⟩)) (kid04_part1182) = true := by rfl

def kid04_part1183 : Audit := .cycle 0 16 true (0)
theorem kid04_part1183_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,3⟩)) (kid04_part1183) = true := by rfl

def kid04_part1184 : Audit := .split 13 (5,true) (byMove [
.cycle 24 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 22 true (-2),
.last 15 (1,true),
.cycle 7 8 true (0),
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.cycle 8 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 5, 32, 5, 64],[4, 64, 5, 1, 32, 32, 64],64⟩,
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.cycle 12 2 true (0),
.cycle 23 1 false (-1),
.last 15 (1,true),
.cycle 25 1 false (-1),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 29 1 false (-1),
.cycle 19 1 false (-1)
])
theorem kid04_part1184_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,4⟩)) (kid04_part1184) = true := by rfl

def kid04_part1185 : Audit := .split 12 (5,true) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M199.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M199.never m hm),
.last 17 (1,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 21 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 0 52 true (-2),
.last 15 (1,true),
.cycle 0 40 true (-2),
.cycle 0 34 true (0),
.last 14 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M200.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M200.never m hm),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.far false 4 ⟨0,[0, 1, 0, 2, 2, 3, 3, 3],[128, 256, 8, 257, 256, 1, 8192, 16384, 8, 256, 256, 1, 524288, 1048576, 32768, 257, 1048577, 4352, 524288, 1048576, 2097152, 20763017, 20763017, 20763017, 16777216],[256, 16777216, 8, 1, 2048, 1, 16384, 16777216, 1, 1, 131072, 0, 1048576, 16777216, 2101632, 4096, 8388608, 20763017, 1048576, 16777216, 20763017, 262144, 8388608, 20763017, 16777216],33501248⟩,
.last 29 (1,true),
.cycle 0 16 true (0),
.last 13 (1,true),
.last 25 (1,true),
.last 15 (1,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 1, 4, 4, 4, 4],[128, 256, 8, 1327513993, 256, 1, 8192, 16384, 8, 67109120, 131072, 1, 128, 256, 2097152, 256, 2048, 256, 33554432, 67108864, 134217728, 1, 1, 16777216, 33554432, 67108864, 134217728, 1327513993, 1864384905, 1327513993, 1073741824],[256, 1073741824, 264, 1, 2048, 1024, 16384, 1073741824, 1, 1, 131072, 65536, 256, 1073741824, 256, 262144, 2048, 1024, 67108864, 1073741824, 1, 16777216, 536870912, 268435456, 67108864, 1073741824, 1327513993, 16777216, 536870912, 268435456, 1073741824],2141103966⟩,
.far false 5 ⟨0,[0, 1, 0, 2, 3, 1, 4, 4, 4, 4],[128, 256, 8, 1327513993, 256, 1, 8192, 16384, 8, 67109120, 131072, 1, 128, 256, 2097152, 256, 2048, 256, 33554432, 67108864, 134217728, 1, 1, 16777216, 33554432, 67108864, 134217728, 1327513993, 1864384905, 1327513993, 1073741824],[256, 1073741824, 264, 1, 2048, 2048, 16384, 1073741824, 1, 1, 131072, 131072, 256, 1073741824, 256, 262144, 2048, 2048, 67108864, 1073741824, 1, 16777216, 536870912, 536870912, 67108864, 1073741824, 1327513993, 16777216, 536870912, 536870912, 1073741824],2141103966⟩
])
theorem kid04_part1185_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,false,5⟩)) (kid04_part1185) = true := by rfl

def kid04_part1186 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 14 15 false (2),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 17 9 false (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 29 true (0),
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 18 11 false (2),
.cycle 14 10 false (2),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 0 15 true (0),
.last 28 (5,true)
])
theorem kid04_part1186_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,0⟩)) (kid04_part1186) = true := by rfl

def kid04_part1187 : Audit := .cycle 16 9 false (2)
theorem kid04_part1187_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,1⟩)) (kid04_part1187) = true := by rfl

def kid04_part1188 : Audit := .cycle 0 14 true (0)
theorem kid04_part1188_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,2⟩)) (kid04_part1188) = true := by rfl

def kid04_part1189 : Audit := .cycle 4 8 true (1)
theorem kid04_part1189_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,3⟩)) (kid04_part1189) = true := by rfl

def kid04_part1190 : Audit := .split 28 (5,true) (byMove [
.cycle 0 60 true (-1),
.last 29 (1,true),
.cycle 18 11 false (2),
.last 31 (1,true),
.cycle 16 13 false (3),
.cycle 0 57 false (4),
.cycle 59 25 true (1),
.last 29 (1,true),
.cycle 60 1 true (4),
.cycle 0 56 true (-1),
.cycle 31 1 true (5),
.cycle 0 34 true (-1),
.cycle 15 15 false (3),
.last 29 (1,true),
.cycle 18 11 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 16, 53, 64],[4, 64, 53, 1, 32, 53, 64],64⟩,
.cycle 27 2 true (1),
.cycle 21 15 false (2),
.cycle 13 21 false (4),
.last 29 (1,true),
.cycle 13 17 false (4),
.cycle 0 56 true (-1),
.cycle 31 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 16, 53, 64],[4, 64, 53, 1, 32, 32, 64],64⟩
])
theorem kid04_part1190_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,4⟩)) (kid04_part1190) = true := by rfl

def kid04_part1191 : Audit := .cycle 15 3 false (1)
theorem kid04_part1191_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some ⟨true,true,5⟩)) (kid04_part1191) = true := by rfl

def kid04_part1167 : Audit := .split 11 (4,false) (byMove [(kid04_part1168),(kid04_part1169),(kid04_part1170),(kid04_part1171),(kid04_part1172),(kid04_part1173),(kid04_part1174),(kid04_part1175),(kid04_part1176),(kid04_part1177),(kid04_part1178),(kid04_part1179),(kid04_part1180),(kid04_part1181),(kid04_part1182),(kid04_part1183),(kid04_part1184),(kid04_part1185),(kid04_part1186),(kid04_part1187),(kid04_part1188),(kid04_part1189),(kid04_part1190),(kid04_part1191)])

theorem kid04_part1167_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid04_part1167) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,false) (some mv)) (byMove [(kid04_part1168),(kid04_part1169),(kid04_part1170),(kid04_part1171),(kid04_part1172),(kid04_part1173),(kid04_part1174),(kid04_part1175),(kid04_part1176),(kid04_part1177),(kid04_part1178),(kid04_part1179),(kid04_part1180),(kid04_part1181),(kid04_part1182),(kid04_part1183),(kid04_part1184),(kid04_part1185),(kid04_part1186),(kid04_part1187),(kid04_part1188),(kid04_part1189),(kid04_part1190),(kid04_part1191)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1168_checked

  · exact kid04_part1174_checked

  · exact kid04_part1180_checked

  · exact kid04_part1186_checked

  · exact kid04_part1169_checked

  · exact kid04_part1175_checked

  · exact kid04_part1181_checked

  · exact kid04_part1187_checked

  · exact kid04_part1170_checked

  · exact kid04_part1176_checked

  · exact kid04_part1182_checked

  · exact kid04_part1188_checked

  · exact kid04_part1171_checked

  · exact kid04_part1177_checked

  · exact kid04_part1183_checked

  · exact kid04_part1189_checked

  · exact kid04_part1172_checked

  · exact kid04_part1178_checked

  · exact kid04_part1184_checked

  · exact kid04_part1190_checked

  · exact kid04_part1173_checked

  · exact kid04_part1179_checked

  · exact kid04_part1185_checked

  · exact kid04_part1191_checked

def kid04_part1192 : Audit := .cycle 2 10 true (1)
theorem kid04_part1192_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid04_part1192) = true := by rfl

def kid04_part1194 : Audit := .cycle 2 11 true (1)
theorem kid04_part1194_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1194) = true := by rfl

def kid04_part1195 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 13 (4,false),
.last 14 (4,false),
.cycle 21 9 false (1),
.cycle 20 7 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 9 4 true (2)
])
theorem kid04_part1195_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1195) = true := by rfl

def kid04_part1196 : Audit := .split 13 (4,false) (byMove [
.cycle 0 27 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 19 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 33 1 false (1),
.last 23 (1,true),
.last 14 (1,true),
.last 19 (1,true),
.cycle 28 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 1 true (1),
.cycle 19 5 false (1)
])
theorem kid04_part1196_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1196) = true := by rfl

def kid04_part1197 : Audit := .cycle 0 13 true (0)
theorem kid04_part1197_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1197) = true := by rfl

def kid04_part1198 : Audit := .cycle 8 4 true (2)
theorem kid04_part1198_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1198) = true := by rfl

def kid04_part1199 : Audit := .split 18 (4,false) (byMove [
.cycle 15 11 false (1),
.last 41 (1,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 13 14 true (-2),
.last 19 (1,true),
.cycle 22 1 false (0),
.cycle 0 20 true (-2),
.cycle 13 7 false (1),
.cycle 16 3 false (0),
.last 20 (1,true),
.cycle 13 9 false (1),
.cycle 13 16 true (-3),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 2 18 false (3),
.last 19 (1,true),
.cycle 13 8 false (1),
.cycle 9 24 false (3),
.cycle 15 8 false (1),
.cycle 15 4 false (1)
])
theorem kid04_part1199_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1199) = true := by rfl

def kid04_part1200 : Audit := .cycle 0 12 true (0)
theorem kid04_part1200_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1200) = true := by rfl

def kid04_part1201 : Audit := .cycle 1 11 true (1)
theorem kid04_part1201_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1201) = true := by rfl

def kid04_part1202 : Audit := .split 24 (4,false) (byMove [
.cycle 2 24 true (1),
.last 25 (1,true),
.cycle 53 1 false (1),
.cycle 0 26 true (0),
.cycle 8 17 true (2),
.cycle 43 1 false (3),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 12 13 true (2),
.cycle 3 22 true (1),
.cycle 24 1 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 4, 64],[4, 64, 4, 1, 32, 4, 64],64⟩,
.cycle 6 19 true (2),
.last 25 (1,true),
.last 30 (1,true),
.cycle 2 25 true (1),
.cycle 10 15 true (2),
.cycle 32 2 false (0),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 2 26 true (1),
.cycle 24 1 true (4),
.cycle 9 16 true (2)
])
theorem kid04_part1202_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1202) = true := by rfl

def kid04_part1203 : Audit := .cycle 3 9 true (1)
theorem kid04_part1203_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1203) = true := by rfl

def kid04_part1204 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 6 true (2),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 15 true (2),
.cycle 8 15 true (2),
.cycle 12 1 true (4),
.cycle 11 4 true (3),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 8 true (2),
.cycle 8 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid04_part1204_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1204) = true := by rfl

def kid04_part1205 : Audit := .split 13 (4,false) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 19 1 false (-1),
.last 16 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 23 2 false (1),
.cycle 2 13 true (1),
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 4, 40, 64],[4, 64, 40, 1, 32, 32, 64],64⟩,
.cycle 0 15 true (0),
.cycle 8 6 true (2),
.cycle 11 3 true (3),
.last 24 (1,true),
.last 14 (1,true),
.last 21 (1,true),
.cycle 5 9 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.cycle 41 2 false (7),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 8 6 true (2),
.cycle 11 3 true (3)
])
theorem kid04_part1205_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1205) = true := by rfl

def kid04_part1206 : Audit := .cycle 6 6 true (2)
theorem kid04_part1206_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1206) = true := by rfl

def kid04_part1207 : Audit := .split 12 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 18 (4,false),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 7 8 true (2),
.cycle 21 9 false (1),
.cycle 20 7 false (0),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 18 (4,false),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 11 2 true (2)
])
theorem kid04_part1207_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1207) = true := by rfl

def kid04_part1208 : Audit := .split 13 (4,false) (byMove [
.cycle 0 48 true (-1),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 29 1 false (-1),
.cycle 19 1 false (-1),
.cycle 30 2 false (0),
.last 15 (1,true),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 8 7 true (1),
.cycle 2 18 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 19 (1,true),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.last 15 (1,true),
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 22 15 false (3),
.cycle 19 5 false (1)
])
theorem kid04_part1208_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1208) = true := by rfl

def kid04_part1209 : Audit := .cycle 2 12 true (1)
theorem kid04_part1209_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1209) = true := by rfl

def kid04_part1210 : Audit := .cycle 10 2 true (2)
theorem kid04_part1210_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1210) = true := by rfl

def kid04_part1211 : Audit := .split 18 (4,false) (byMove [
.cycle 15 11 false (1),
.last 31 (1,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 13 9 false (1),
.last 19 (1,true),
.cycle 35 18 true (0),
.cycle 13 10 true (-2),
.cycle 14 5 false (1),
.cycle 16 3 false (0),
.last 20 (1,true),
.cycle 13 9 false (1),
.cycle 13 11 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-2),
.cycle 17 2 false (-1),
.cycle 15 10 false (1),
.last 19 (1,true),
.cycle 13 8 false (1),
.cycle 5 14 false (3),
.cycle 15 6 false (1),
.cycle 15 4 false (1)
])
theorem kid04_part1211_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1211) = true := by rfl

def kid04_part1212 : Audit := .cycle 0 12 true (0)
theorem kid04_part1212_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1212) = true := by rfl

def kid04_part1213 : Audit := .cycle 1 11 true (1)
theorem kid04_part1213_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1213) = true := by rfl

def kid04_part1214 : Audit := .cycle 2 10 true (1)
theorem kid04_part1214_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1214) = true := by rfl

def kid04_part1215 : Audit := .cycle 2 13 true (1)
theorem kid04_part1215_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1215) = true := by rfl

def kid04_part1216 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 4 true (3),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 8 10 true (2),
.cycle 2 13 true (1),
.cycle 10 3 true (2),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid04_part1216_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1216) = true := by rfl

def kid04_part1217 : Audit := .cycle 9 3 true (2)
theorem kid04_part1217_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1217) = true := by rfl

def kid04_part1193 : Audit := .split 11 (5,true) (byMove [(kid04_part1194),(kid04_part1195),(kid04_part1196),(kid04_part1197),(kid04_part1198),(kid04_part1199),(kid04_part1200),(kid04_part1201),(kid04_part1202),(kid04_part1203),(kid04_part1204),(kid04_part1205),(kid04_part1206),(kid04_part1207),(kid04_part1208),(kid04_part1209),(kid04_part1210),(kid04_part1211),(kid04_part1212),(kid04_part1213),(kid04_part1214),(kid04_part1215),(kid04_part1216),(kid04_part1217)])

theorem kid04_part1193_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid04_part1193) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid04_part1194),(kid04_part1195),(kid04_part1196),(kid04_part1197),(kid04_part1198),(kid04_part1199),(kid04_part1200),(kid04_part1201),(kid04_part1202),(kid04_part1203),(kid04_part1204),(kid04_part1205),(kid04_part1206),(kid04_part1207),(kid04_part1208),(kid04_part1209),(kid04_part1210),(kid04_part1211),(kid04_part1212),(kid04_part1213),(kid04_part1214),(kid04_part1215),(kid04_part1216),(kid04_part1217)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1194_checked

  · exact kid04_part1200_checked

  · exact kid04_part1206_checked

  · exact kid04_part1212_checked

  · exact kid04_part1195_checked

  · exact kid04_part1201_checked

  · exact kid04_part1207_checked

  · exact kid04_part1213_checked

  · exact kid04_part1196_checked

  · exact kid04_part1202_checked

  · exact kid04_part1208_checked

  · exact kid04_part1214_checked

  · exact kid04_part1197_checked

  · exact kid04_part1203_checked

  · exact kid04_part1209_checked

  · exact kid04_part1215_checked

  · exact kid04_part1198_checked

  · exact kid04_part1204_checked

  · exact kid04_part1210_checked

  · exact kid04_part1216_checked

  · exact kid04_part1199_checked

  · exact kid04_part1205_checked

  · exact kid04_part1211_checked

  · exact kid04_part1217_checked

def kid04_part1219 : Audit := .cycle 0 20 true (0)
theorem kid04_part1219_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid04_part1219) = true := by rfl

def kid04_part1220 : Audit := .cycle 0 14 true (0)
theorem kid04_part1220_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid04_part1220) = true := by rfl

def kid04_part1221 : Audit := .cycle 21 1 false (1)
theorem kid04_part1221_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid04_part1221) = true := by rfl

def kid04_part1222 : Audit := .cycle 0 16 true (0)
theorem kid04_part1222_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid04_part1222) = true := by rfl

def kid04_part1223 : Audit := .split 11 (4,false) (byMove [
.cycle 0 42 true (-1),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 8 5 true (1),
.cycle 16 1 false (0),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.cycle 14 1 false (-2),
.last 13 (1,true),
.cycle 17 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 13 false (3),
.cycle 15 3 false (1)
])
theorem kid04_part1223_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid04_part1223) = true := by rfl

def kid04_part1224 : Audit := .cycle 13 1 false (-1)
theorem kid04_part1224_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid04_part1224) = true := by rfl

def kid04_part1225 : Audit := .cycle 2 10 true (1)
theorem kid04_part1225_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid04_part1225) = true := by rfl

def kid04_part1226 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,false),
.cycle 35 1 false (7),
.last 12 (4,false),
.cycle 32 1 false (8),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid04_part1226_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid04_part1226) = true := by rfl

def kid04_part1227 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 19 1 false (1),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 31 1 false (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (2)
])
theorem kid04_part1227_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid04_part1227) = true := by rfl

def kid04_part1228 : Audit := .cycle 0 12 true (0)
theorem kid04_part1228_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid04_part1228) = true := by rfl

def kid04_part1229 : Audit := .cycle 8 3 true (2)
theorem kid04_part1229_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid04_part1229) = true := by rfl

def kid04_part1230 : Audit := .cycle 21 1 false (5)
theorem kid04_part1230_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid04_part1230) = true := by rfl

def kid04_part1231 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.last 20 (4,false),
.cycle 0 17 true (0),
.cycle 18 5 false (1),
.cycle 18 3 false (0),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 8 5 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 64, 32, 64],[1, 33, 16, 1, 1, 1, 64],80⟩,
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 20 (4,false),
.cycle 5 8 true (1),
.cycle 19 9 false (1),
.cycle 18 3 false (0),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.cycle 15 19 false (3),
.cycle 18 13 false (2)
])
theorem kid04_part1231_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid04_part1231) = true := by rfl

def kid04_part1232 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 1 false (-1),
.cycle 18 5 false (2),
.cycle 26 5 false (6),
.last 18 (4,false),
.cycle 19 5 false (3),
.cycle 23 5 false (4),
.cycle 17 5 false (1),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 1 false (-1),
.cycle 12 6 true (0),
.cycle 1 19 true (0),
.cycle 17 5 false (1),
.cycle 5 12 true (0),
.cycle 18 7 true (1),
.cycle 15 2 true (0)
])
theorem kid04_part1232_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid04_part1232) = true := by rfl

def kid04_part1233 : Audit := .cycle 2 12 true (1)
theorem kid04_part1233_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid04_part1233) = true := by rfl

def kid04_part1234 : Audit := .cycle 18 1 false (0)
theorem kid04_part1234_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid04_part1234) = true := by rfl

def kid04_part1235 : Audit := .split 11 (4,false) (byMove [
.cycle 31 2 true (2),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 6 true (1),
.last 12 (1,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 12 2 true (2),
.cycle 10 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 12 2 true (0),
.cycle 14 1 false (-2),
.cycle 16 2 true (1),
.last 12 (1,true),
.cycle 15 2 true (0),
.cycle 2 12 true (1),
.cycle 12 2 true (2),
.cycle 12 2 true (1)
])
theorem kid04_part1235_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid04_part1235) = true := by rfl

def kid04_part1236 : Audit := .cycle 13 1 false (-1)
theorem kid04_part1236_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid04_part1236) = true := by rfl

def kid04_part1237 : Audit := .cycle 2 10 true (1)
theorem kid04_part1237_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid04_part1237) = true := by rfl

def kid04_part1238 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 1 16 true (1),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.last 13 (4,false),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid04_part1238_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid04_part1238) = true := by rfl

def kid04_part1239 : Audit := .cycle 7 4 true (2)
theorem kid04_part1239_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid04_part1239) = true := by rfl

def kid04_part1240 : Audit := .cycle 0 12 true (0)
theorem kid04_part1240_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid04_part1240) = true := by rfl

def kid04_part1241 : Audit := .cycle 8 3 true (2)
theorem kid04_part1241_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid04_part1241) = true := by rfl

def kid04_part1242 : Audit := .cycle 9 3 true (2)
theorem kid04_part1242_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid04_part1242) = true := by rfl

def kid04_part1218 : Audit := .split 10 (5,true) (byMove [(kid04_part1219),(kid04_part1220),(kid04_part1221),(kid04_part1222),(kid04_part1223),(kid04_part1224),(kid04_part1225),(kid04_part1226),(kid04_part1227),(kid04_part1228),(kid04_part1229),(kid04_part1230),(kid04_part1231),(kid04_part1232),(kid04_part1233),(kid04_part1234),(kid04_part1235),(kid04_part1236),(kid04_part1237),(kid04_part1238),(kid04_part1239),(kid04_part1240),(kid04_part1241),(kid04_part1242)])

theorem kid04_part1218_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid04_part1218) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid04_part1219),(kid04_part1220),(kid04_part1221),(kid04_part1222),(kid04_part1223),(kid04_part1224),(kid04_part1225),(kid04_part1226),(kid04_part1227),(kid04_part1228),(kid04_part1229),(kid04_part1230),(kid04_part1231),(kid04_part1232),(kid04_part1233),(kid04_part1234),(kid04_part1235),(kid04_part1236),(kid04_part1237),(kid04_part1238),(kid04_part1239),(kid04_part1240),(kid04_part1241),(kid04_part1242)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1219_checked

  · exact kid04_part1225_checked

  · exact kid04_part1231_checked

  · exact kid04_part1237_checked

  · exact kid04_part1220_checked

  · exact kid04_part1226_checked

  · exact kid04_part1232_checked

  · exact kid04_part1238_checked

  · exact kid04_part1221_checked

  · exact kid04_part1227_checked

  · exact kid04_part1233_checked

  · exact kid04_part1239_checked

  · exact kid04_part1222_checked

  · exact kid04_part1228_checked

  · exact kid04_part1234_checked

  · exact kid04_part1240_checked

  · exact kid04_part1223_checked

  · exact kid04_part1229_checked

  · exact kid04_part1235_checked

  · exact kid04_part1241_checked

  · exact kid04_part1224_checked

  · exact kid04_part1230_checked

  · exact kid04_part1236_checked

  · exact kid04_part1242_checked

def kid04_part1243 : Audit := .cycle 0 10 true (0)
theorem kid04_part1243_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid04_part1243) = true := by rfl

def kid04_part1244 : Audit := .cycle 1 9 true (1)
theorem kid04_part1244_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid04_part1244) = true := by rfl

def kid04_part1245 : Audit := .cycle 2 8 true (1)
theorem kid04_part1245_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid04_part1245) = true := by rfl

def kid04_part1246 : Audit := .cycle 2 11 true (1)
theorem kid04_part1246_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid04_part1246) = true := by rfl

def kid04_part1247 : Audit := .split 10 (4,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 13 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.last 30 (5,true),
.cycle 20 7 true (1),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.cycle 8 3 true (2),
.split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 13 true (2),
.cycle 3 9 true (1),
.cycle 9 4 true (3),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 20 7 true (1),
.cycle 2 12 true (1),
.cycle 11 2 true (2),
.cycle 16 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 8 12 true (2),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.far false 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 1, 0, 1],[128, 256, 8, 1073743872, 4194304, 1024, 524288, 1048576, 32768, 256, 1073741825, 4194304, 128, 256, 8, 4194304, 1024, 1024, 128, 256, 134217728, 256, 2048, 1024, 128, 256, 8, 4194304, 4194304, 1024, 1073741824],[256, 32768, 1073743873, 1, 2048, 1073741824, 1048576, 4194304, 4194304, 4096, 8388608, 1073741824, 256, 134217728, 1073741952, 1, 2048, 1073741824, 256, 2048, 1024, 16777216, 2048, 1073741824, 256, 32768, 4194304, 1, 2048, 1073741824, 1073741824],1686324268⟩,
.cycle 16 1 false (0),
.cycle 0 16 true (0),
.cycle 8 6 true (2),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 24 11 false (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true),
.cycle 8 8 true (2),
.last 18 (5,true),
.last 59 (5,true),
.cycle 5 7 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.last 12 (5,true)
]),
.cycle 8 6 true (2),
.cycle 2 11 true (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 8 5 true (2),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 14 true (2),
.cycle 3 10 true (1),
.cycle 8 9 true (2),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 18 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3)
]),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 8 6 true (2),
.cycle 16 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 23 13 false (3),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 9 4 true (3),
.cycle 8 8 true (2),
.last 12 (1,true),
.cycle 34 12 true (4),
.cycle 5 7 true (1),
.cycle 11 2 true (2),
.cycle 16 5 false (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 8 4 true (2),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid04_part1247_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid04_part1247) = true := by rfl

def kid04_part1248 : Audit := .cycle 9 1 true (3)
theorem kid04_part1248_checked : zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid04_part1248) = true := by rfl

def kid04_part1128 : Audit := .split 9 (5,false) (byMove [(kid04_part1129),(kid04_part1130),(kid04_part1131),(kid04_part1156),(kid04_part1157),(kid04_part1158),(kid04_part1159),(kid04_part1160),(kid04_part1161),(kid04_part1162),(kid04_part1163),(kid04_part1164),(kid04_part1165),(kid04_part1166),(kid04_part1167),(kid04_part1192),(kid04_part1193),(kid04_part1218),(kid04_part1243),(kid04_part1244),(kid04_part1245),(kid04_part1246),(kid04_part1247),(kid04_part1248)])

theorem kid04_part1128_checked : zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (kid04_part1128) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,4⟩) (4,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid04_part1129),(kid04_part1130),(kid04_part1131),(kid04_part1156),(kid04_part1157),(kid04_part1158),(kid04_part1159),(kid04_part1160),(kid04_part1161),(kid04_part1162),(kid04_part1163),(kid04_part1164),(kid04_part1165),(kid04_part1166),(kid04_part1167),(kid04_part1192),(kid04_part1193),(kid04_part1218),(kid04_part1243),(kid04_part1244),(kid04_part1245),(kid04_part1246),(kid04_part1247),(kid04_part1248)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1129_checked

  · exact kid04_part1159_checked

  · exact kid04_part1165_checked

  · exact kid04_part1243_checked

  · exact kid04_part1130_checked

  · exact kid04_part1160_checked

  · exact kid04_part1166_checked

  · exact kid04_part1244_checked

  · exact kid04_part1131_checked

  · exact kid04_part1161_checked

  · exact kid04_part1167_checked

  · exact kid04_part1245_checked

  · exact kid04_part1156_checked

  · exact kid04_part1162_checked

  · exact kid04_part1192_checked

  · exact kid04_part1246_checked

  · exact kid04_part1157_checked

  · exact kid04_part1163_checked

  · exact kid04_part1193_checked

  · exact kid04_part1247_checked

  · exact kid04_part1158_checked

  · exact kid04_part1164_checked

  · exact kid04_part1218_checked

  · exact kid04_part1248_checked

def kid04 : Audit := .split 8 (4,true) (byMove [(kid04_part1),(kid04_part2),(kid04_part3),(kid04_part4),(kid04_part5),(kid04_part78),(kid04_part247),(kid04_part248),(kid04_part249),(kid04_part250),(kid04_part251),(kid04_part348),(kid04_part445),(kid04_part542),(kid04_part663),(kid04_part664),(kid04_part665),(kid04_part786),(kid04_part1051),(kid04_part1052),(kid04_part1053),(kid04_part1054),(kid04_part1055),(kid04_part1128)])

theorem check04 : zipCheck 1882 (child ⟨false,false,4⟩) (kid04) = true := by

  change (zipQueryOK 1882 (child ⟨false,false,4⟩) 8 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (child ⟨false,false,4⟩) (4,true) (some mv)) (byMove [(kid04_part1),(kid04_part2),(kid04_part3),(kid04_part4),(kid04_part5),(kid04_part78),(kid04_part247),(kid04_part248),(kid04_part249),(kid04_part250),(kid04_part251),(kid04_part348),(kid04_part445),(kid04_part542),(kid04_part663),(kid04_part664),(kid04_part665),(kid04_part786),(kid04_part1051),(kid04_part1052),(kid04_part1053),(kid04_part1054),(kid04_part1055),(kid04_part1128)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid04_part1_checked

  · exact kid04_part247_checked

  · exact kid04_part445_checked

  · exact kid04_part1051_checked

  · exact kid04_part2_checked

  · exact kid04_part248_checked

  · exact kid04_part542_checked

  · exact kid04_part1052_checked

  · exact kid04_part3_checked

  · exact kid04_part249_checked

  · exact kid04_part663_checked

  · exact kid04_part1053_checked

  · exact kid04_part4_checked

  · exact kid04_part250_checked

  · exact kid04_part664_checked

  · exact kid04_part1054_checked

  · exact kid04_part5_checked

  · exact kid04_part251_checked

  · exact kid04_part665_checked

  · exact kid04_part1055_checked

  · exact kid04_part78_checked

  · exact kid04_part348_checked

  · exact kid04_part786_checked

  · exact kid04_part1128_checked

end BB6.Agent11Raw39B1RC
